#!/usr/bin/env python3
"""Alternating, repeated wrk runs, with disjoint server/client CPU affinity."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import time
from verify import connect, verify
from verify_http import verify_http

ROOT = Path(__file__).resolve().parents[1]
HZ = os.sysconf("SC_CLK_TCK")
CONFIGS = {
    "lean-fast-original-1": (18105, "0", [str(ROOT / "bin/lean-fast-http-original"), "18105"], "1"),
    "lean-fast-before-1": (18094, "0", [str(ROOT / "bin/lean-fast-http-before"), "18094"], "1"),
    "lean-fast-v1-1": (18103, "0", [str(ROOT / "bin/lean-fast-http-v1"), "18103"], "1"),
    "lean-fast-1": (18095, "0", [str(ROOT / "bin/lean-fast-http"), "18095"], "1"),
    "lean-h1-1": (18097, "0", [str(ROOT / "bin/lean-h1-http"), "18097"], "1"),
}


def thread_times(pid):
    result = {}
    for p in Path(f"/proc/{pid}/task").glob("*/stat"):
        try:
            fields = p.read_text().rsplit(")", 1)[1].split()
            result[p.parent.name] = (int(fields[11]) + int(fields[12])) / HZ
        except FileNotFoundError:
            pass
    return result


def run_wrk(port, duration, connections):
    cmd = ["taskset", "-c", "4-11", os.environ.get("WRK", "wrk"), "-t8",
           f"-c{connections}", f"-d{duration}s", "--latency", "--timeout", "2s",
           f"http://127.0.0.1:{port}/"]
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return cmd, result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=int, default=15)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--connections", type=int, default=64)
    parser.add_argument("--output", default="measured")
    parser.add_argument("--server-cpu", type=int,
                        help="override the server CPU for single-CPU configurations")
    parser.add_argument("--configs", nargs="+", choices=CONFIGS,
                        default=[name for name in CONFIGS if name != "lean-fast-original-1"])
    args = parser.parse_args()
    configs = {name: CONFIGS[name] for name in args.configs}
    if args.server_cpu is not None:
        if args.server_cpu not in os.sched_getaffinity(0) or args.server_cpu in range(4, 12):
            parser.error("server CPU must be available and disjoint from wrk CPUs 4–11")
        if any(config[1] != "0" for config in configs.values()):
            parser.error("--server-cpu only applies to single-CPU configurations")
        configs = {name: (port, str(args.server_cpu), command, threads)
                   for name, (port, _, command, threads) in configs.items()}
    out = ROOT / "results" / args.output
    out.mkdir(parents=True, exist_ok=True)
    if (out / "metadata.json").exists():
        parser.error("output already contains a run; choose a new --output name")
    metadata = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "seconds": args.seconds, "repeats": args.repeats,
        "connections": args.connections, "client_threads": 8,
        "client_cpus": "4-11", "warmup_seconds": 3,
        "response_body_bytes": 1024, "protocol": "HTTP/1.1 keep-alive, no pipelining in wrk",
        "transport": "Linux loopback, HTTP without TLS",
        "lscpu": subprocess.check_output(["lscpu"], text=True),
        "uname": subprocess.check_output(["uname", "-a"], text=True),
        "configs": configs,
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "source_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)),
        "original_source_commit": "ad80f25fd47cfde93db96c76affe983ac565b1f0" if "lean-fast-original-1" in configs else None,
        "binary_sha256": {name: hashlib.sha256(Path(config[2][0]).read_bytes()).hexdigest()
                          for name, config in configs.items()},
    }
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    records = []
    for repeat in range(1, args.repeats + 1):
        # Reverse order every second round to reduce systematic thermal/order bias.
        order = list(configs) if repeat % 2 else list(reversed(configs))
        for name in order:
            port, cpus, command, threads = configs[name]
            prefix = f"{name}-run{repeat}"
            # Refuse to benchmark an unrelated server already using this port.
            try:
                with connect(port):
                    pass
            except ConnectionRefusedError:
                pass
            else:
                raise RuntimeError(f"port {port} is already occupied before {prefix}")
            with open(out / f"{prefix}-server.log", "w") as log:
                env = {**os.environ, "LEAN_NUM_THREADS": threads}
                server = subprocess.Popen(["taskset", "-c", cpus, *command],
                                          stdout=log, stderr=log, env=env)
                try:
                    for _ in range(100):
                        if server.poll() is not None:
                            raise RuntimeError(f"server exited: {prefix}")
                        try:
                            with connect(port):
                                break
                        except OSError:
                            time.sleep(0.05)
                    check = verify_http(port) if name in ("lean-fast-1", "lean-fast-v1-1", "lean-fast-original-1") or name.startswith(("lean-std-", "lean-h1-", "lean-compat-", "lean-leanio-", "rust-hyper-")) else verify(port)
                    if server.poll() is not None:
                        raise RuntimeError(f"server exited during verification: {prefix}")
                    _, warmup = run_wrk(port, 3, args.connections)
                    (out / f"{prefix}-warmup.txt").write_text(warmup)
                    before = thread_times(server.pid)
                    started_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
                    boot_started = time.clock_gettime(time.CLOCK_BOOTTIME)
                    started = time.monotonic()
                    cmd, text = run_wrk(port, args.seconds, args.connections)
                    elapsed = time.monotonic() - started
                    boot_elapsed = time.clock_gettime(time.CLOCK_BOOTTIME) - boot_started
                    suspended = max(0., boot_elapsed - elapsed)
                    timing = {"started_utc": started_utc, "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                              "monotonic_seconds": elapsed, "boottime_seconds": boot_elapsed,
                              "suspend_seconds": suspended}
                    (out / f"{prefix}-timing.json").write_text(json.dumps(timing, indent=2) + "\n")
                    after = thread_times(server.pid)
                    status = Path(f"/proc/{server.pid}/status").read_text()
                    (out / f"{prefix}.txt").write_text(text)
                    errors = re.search(r"Socket errors:.*|Non-2xx or 3xx responses:.*", text)
                    if suspended > .05:
                        raise RuntimeError(f"invalid measurement {prefix}: host suspended for {suspended:.3f}s")
                    if elapsed > args.seconds + 2:
                        raise RuntimeError(f"invalid measurement {prefix}: {elapsed:.3f}s for a {args.seconds}s run")
                    if errors:
                        raise RuntimeError(f"invalid measurement {prefix}: {errors.group()}")
                    rate = float(re.search(r"Requests/sec:\s+([\d.]+)", text)[1])
                    p99 = re.search(r"99%\s+(\S+)", text)[1]
                    cpu = {tid: round(value - before.get(tid, value), 3)
                           for tid, value in after.items()}
                    record = {"name": name, "repeat": repeat, "requests_per_second": rate,
                              "p99_latency": p99, "command": cmd, "verification": check,
                              "wall_seconds": elapsed, "timing": timing, "thread_cpu_seconds": cpu,
                              "average_busy_cores": round(sum(cpu.values()) / elapsed, 3),
                              "peak_rss_kib": int(re.search(r"VmHWM:\s+(\d+)", status)[1])}
                    records.append(record)
                    (out / "runs.json").write_text(json.dumps(records, indent=2) + "\n")
                    print(f"{prefix}: {rate:,.2f} req/s, p99 {p99}, "
                          f"busy cores {record['average_busy_cores']}", flush=True)
                finally:
                    server.terminate()
                    try:
                        server.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        server.kill()
                        server.wait()
    summary = {}
    for name in configs:
        rates = [r["requests_per_second"] for r in records if r["name"] == name]
        summary[name] = {"median_req_s": statistics.median(rates),
                         "min_req_s": min(rates), "max_req_s": max(rates)}
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
