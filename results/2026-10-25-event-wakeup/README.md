# Event-driven completion validation

Final core source and executable hashes are in artifacts.json; proofs.json audits
394 theorems and four certificate factories. New transition proofs use only
standard Lean axioms. They do not prove the C implementation or scheduler.

Fresh HTTP wire/protocol/RFC runs and completion selector regressions passed.
Native stress sends notifications before arming, concurrently, after reset, and
after all worker loops have stopped. Half-closed clients still receive bytes.
The generic reactor test interrupts a million-effect chain at a cooperative
yield, checking every acquired resource is adopted and released.

ASan/UBSan instrument native/uv.c, not the shipped Lean runtime. Leak detection
remains enabled with the existing narrowly scoped runtime-startup suppressions.
The raw unsuppressed runtime baseline is retained; it is a diagnostic control,
not a clean sanitizer pass. The three sanitizer JSON reports are the passing
instrumented transport, reactor, and late-notification evaluations.
