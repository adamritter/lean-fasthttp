import FastHTTP.QuotedProofs
import FastHTTP.HexProofs

namespace FastHTTP.Protocol

def SpaceOctet (b : UInt8) : Prop := b.toNat = 32 ∨ b.toNat = 9

theorem space_iff (b : UInt8) : space b = true ↔ SpaceOctet b := by
  simp [space, SpaceOctet, ← UInt8.toNat_inj]

/-- RFC BWS/OWS consists of zero or more SP/HTAB octets. -/
def Whitespace (bytes : ByteArray) (start stop : Nat) : Prop :=
  start ≤ stop ∧ stop ≤ bytes.size ∧ Octets bytes SpaceOctet start stop

/-- RFC token is a nonempty sequence of independently specified tchar octets. -/
def TokenGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  start < stop ∧ stop ≤ bytes.size ∧ Octets bytes TokenOctet start stop

def ChunkValueGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  TokenGrammar bytes start stop ∨ QuotedGrammar bytes start bytes.size stop

/-- RFC 9112 section 7.1.1: BWS ; BWS token [ BWS = BWS (token / quoted-string) ].
All split points are existential grammar witnesses, independent of the parser. -/
def ChunkExtensionGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  ∃ semi key nameEnd,
    Whitespace bytes start semi ∧ semi < bytes.size ∧ bytes[semi]! = 59 ∧
    Whitespace bytes (semi + 1) key ∧ TokenGrammar bytes key nameEnd ∧
    (stop = nameEnd ∨ ∃ eq value,
      Whitespace bytes nameEnd eq ∧ eq < bytes.size ∧ bytes[eq]! = 61 ∧
      Whitespace bytes (eq + 1) value ∧ ChunkValueGrammar bytes value stop)

/-- Zero or more complete extensions; no trailing unassigned whitespace. -/
inductive ChunkExtensionsGrammar (bytes : ByteArray) : Nat → Prop where
  | nil : ChunkExtensionsGrammar bytes bytes.size
  | cons {start next : Nat} : ChunkExtensionGrammar bytes start next →
      ChunkExtensionsGrammar bytes next → ChunkExtensionsGrammar bytes start

theorem spanEnd_whitespace (bytes : ByteArray) (start : Nat) (hs : start ≤ bytes.size) :
    Whitespace bytes start (spanEnd bytes bytes.size space start) := by
  have h := spanEnd_spec bytes bytes.size space start hs
  exact ⟨h.1, h.2.1, fun i hi hj => (space_iff _).mp (h.2.2.1 i hi hj)⟩

theorem spanEnd_token (bytes : ByteArray) (start : Nat) (hs : start ≤ bytes.size)
    (hn : spanEnd bytes bytes.size token start ≠ start) :
    TokenGrammar bytes start (spanEnd bytes bytes.size token start) := by
  have h := spanEnd_spec bytes bytes.size token start hs
  exact ⟨by omega, h.2.1, fun i hi hj => (token_iff _).mp (h.2.2.1 i hi hj)⟩

theorem chunkExtension_sound (bytes : ByteArray) (start stop : Nat)
    (hs : start ≤ bytes.size) (h : chunkExtension bytes start = some stop) :
    ChunkExtensionGrammar bytes start stop := by
  have semi := spanEnd_whitespace bytes start hs
  unfold chunkExtension at h
  try dsimp only at h
  split at h
  · contradiction
  · rename_i hc
    have hc' : spanEnd bytes bytes.size space start < bytes.size ∧
        bytes[spanEnd bytes bytes.size space start]! = 59 := by simpa using hc
    have key := spanEnd_whitespace bytes (spanEnd bytes bytes.size space start + 1) (by omega)
    try dsimp only at h
    split at h
    · contradiction
    · rename_i hn
      have name := spanEnd_token bytes _ key.2.1 (by simpa using hn)
      have eq := spanEnd_whitespace bytes _ name.2.1
      try dsimp only at h
      split at h
      · rename_i heq
        have heq' : spanEnd bytes bytes.size space (spanEnd bytes bytes.size token
            (spanEnd bytes bytes.size space (spanEnd bytes bytes.size space start + 1))) < bytes.size ∧
            bytes[spanEnd bytes bytes.size space (spanEnd bytes bytes.size token
            (spanEnd bytes bytes.size space (spanEnd bytes bytes.size space start + 1)))]! = 61 := by
          simpa using heq
        have value := spanEnd_whitespace bytes _ (Nat.succ_le_of_lt heq'.1)
        refine ⟨_, _, _, semi, hc'.1, hc'.2, key, name, Or.inr ⟨_, _, eq, heq'.1, heq'.2, value, ?_⟩⟩
        try dsimp only at h
        split at h
        · exact Or.inr ((quotedEnd_iff _ _ _ _).mp h)
        · split at h
          · contradiction
          · rename_i hv
            cases h
            exact Or.inl (spanEnd_token bytes _ value.2.1 (by simpa using hv))
      · cases h
        exact ⟨_, _, _, semi, hc'.1, hc'.2, key, name, Or.inl rfl⟩

/-- Every accepted production extension suffix has the complete RFC grammar. -/
theorem chunkExtensions_sound (bytes : ByteArray) (start : Nat)
    (h : chunkExtensions bytes start = .ok ()) : ChunkExtensionsGrammar bytes start := by
  rw [chunkExtensions] at h
  split at h
  · rename_i he; subst start; exact .nil
  · split at h
    · contradiction
    · rename_i hb
      cases he : chunkExtension bytes start with
      | none => simp [he] at h
      | some last =>
        simp only [he] at h
        split at h
        · contradiction
        · rename_i hp
          exact .cons (chunkExtension_sound bytes start last (by omega) he)
            (chunkExtensions_sound bytes last h)
termination_by bytes.size - start

theorem token_not_space (b : UInt8) (h : TokenOctet b) : space b = false := by
  simp [TokenOctet, space, ← UInt8.toNat_inj] at * <;> omega

theorem space_not_token (b : UInt8) (h : SpaceOctet b) : token b = false := by
  simp [SpaceOctet, token, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj] at * <;> omega

/-- Every nonempty extension suffix begins with BWS followed by a semicolon. -/
theorem chunkExtensions_lead (bytes : ByteArray) (start : Nat)
    (h : ChunkExtensionsGrammar bytes start) :
    start ≤ bytes.size ∧
    (spanEnd bytes bytes.size space start = bytes.size ∨
      bytes[spanEnd bytes bytes.size space start]! = 59) ∧
    (start = bytes.size ∨ token bytes[start]! = false) := by
  cases h with
  | nil => simp [spanEnd]
  | @cons start next ext tail =>
    obtain ⟨semi, key, nameEnd, ws, hs, hb, _, _, _⟩ := ext
    dsimp only [Whitespace] at ws
    have he := spanEnd_complete bytes bytes.size space start semi ws.1 (by omega)
      (fun i hi hj => (space_iff _).mpr (ws.2.2 i hi hj))
      (Or.inr (by simp [hb, space]))
    refine ⟨by omega, Or.inr (by simpa [he] using hb), Or.inr ?_⟩
    by_cases hi : start = semi
    · simp [hi, hb, token]
    · exact space_not_token _ (ws.2.2 start (by omega) (by omega))

/-- In a complete suffix the delimiters force maximal token and BWS spans;
no parser-dependent maximality assumptions are added to the RFC grammar. -/
theorem chunkExtension_complete (bytes : ByteArray) (start stop : Nat)
    (h : ChunkExtensionGrammar bytes start stop) (tail : ChunkExtensionsGrammar bytes stop) :
    chunkExtension bytes start = some stop := by
  obtain ⟨semi, key, nameEnd, ws, hs, hb, keyws, name, value⟩ := h
  dsimp only [Whitespace, TokenGrammar] at ws keyws name
  have tailLead := chunkExtensions_lead bytes stop tail
  have semiEq := spanEnd_complete bytes bytes.size space start semi ws.1 (by omega)
    (fun i hi hj => (space_iff _).mpr (ws.2.2 i hi hj)) (Or.inr (by simp [hb, space]))
  have keyEq := spanEnd_complete bytes bytes.size space (semi + 1) key keyws.1 keyws.2.1
    (fun i hi hj => (space_iff _).mpr (keyws.2.2 i hi hj))
    (Or.inr (token_not_space _ (name.2.2 key (by omega) name.1)))
  rcases value with he | ⟨eq, val, eqws, heq, beq, valws, value⟩
  · subst stop
    have nameEq := spanEnd_complete bytes bytes.size token key nameEnd (by omega) name.2.1
      (fun i hi hj => (token_iff _).mpr (name.2.2 i hi hj)) tailLead.2.2
    have noeq : ¬ (spanEnd bytes bytes.size space nameEnd < bytes.size ∧
        bytes[spanEnd bytes bytes.size space nameEnd]! = 61) := by
      rcases tailLead.2.1 with h | h
      · omega
      · simp [h]
    unfold chunkExtension
    simp only [semiEq, keyEq, nameEq]
    have hn : nameEnd ≠ key := by omega
    simp [hs, hb, hn, noeq, -getElem!_pos]
  · dsimp only [Whitespace] at eqws valws
    have nameStop : nameEnd = bytes.size ∨ token bytes[nameEnd]! = false := by
      right
      by_cases hi : nameEnd = eq
      · simp [hi, beq, token]
      · exact space_not_token _ (eqws.2.2 nameEnd (by omega) (by omega))
    have nameEq := spanEnd_complete bytes bytes.size token key nameEnd (by omega) name.2.1
      (fun i hi hj => (token_iff _).mpr (name.2.2 i hi hj)) nameStop
    have eqEq := spanEnd_complete bytes bytes.size space nameEnd eq eqws.1 (by omega)
      (fun i hi hj => (space_iff _).mpr (eqws.2.2 i hi hj)) (Or.inr (by simp [beq, space]))
    have valNotSpace : space bytes[val]! = false := by
      rcases value with v | v
      · exact token_not_space _ (v.2.2 val (by omega) v.1)
      · simp [v.2.2.1, space]
    have valEq := spanEnd_complete bytes bytes.size space (eq + 1) val valws.1 valws.2.1
      (fun i hi hj => (space_iff _).mpr (valws.2.2 i hi hj)) (Or.inr valNotSpace)
    unfold chunkExtension
    simp only [semiEq, keyEq, nameEq]
    have hn : nameEnd ≠ key := by omega
    simp only [show ¬ semi ≥ bytes.size by omega, hb, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, show (nameEnd == key) = false by simp [hn], eqEq,
      show (eq < bytes.size) = True by simp [heq], decide_true, beq, beq_self_eq_true,
      Bool.and_self, valEq]
    rcases value with v | v
    · dsimp only [TokenGrammar] at v
      have valEnd := spanEnd_complete bytes bytes.size token val stop (by omega) v.2.1
        (fun i hi hj => (token_iff _).mpr (v.2.2 i hi hj)) tailLead.2.2
      have vb := (token_iff _).mpr (v.2.2 val (by omega) v.1)
      have vquote : bytes[val]! ≠ 34 := by intro he; simp [he, token] at vb
      have vne : stop ≠ val := by omega
      simp [vquote, valEnd, vne]
    · have q := (quotedEnd_iff bytes val bytes.size stop).mpr v
      simp [v.1, v.2.2.1, q, -getElem!_pos]

/-- Every complete RFC extension suffix is accepted, including all BWS positions
and arbitrary token/quoted values. Together with soundness this is exact. -/
theorem chunkExtensions_complete (bytes : ByteArray) (start : Nat)
    (h : ChunkExtensionsGrammar bytes start) : chunkExtensions bytes start = .ok () := by
  induction h with
  | nil => rw [chunkExtensions]; simp
  | @cons start next ext tail ih =>
    have nextEq := chunkExtension_complete bytes start next ext tail
    obtain ⟨semi, key, nameEnd, ws, hs, hb, keyws, name, val⟩ := ext
    dsimp only [Whitespace, TokenGrammar] at ws keyws name
    have progress : start < next := by
      rcases val with hn | ⟨eq, value, eqws, heq, _, valws, v⟩
      · omega
      · dsimp only [Whitespace] at eqws valws
        rcases v with v | v
        · dsimp only [TokenGrammar] at v
          omega
        · have q := quotedTail_bounds _ _ _ _ v.2.2.2
          omega
    rw [chunkExtensions]
    simp [show start ≠ bytes.size by omega, show ¬ start > bytes.size by omega,
      nextEq, show ¬ next ≤ start by omega, ih]

theorem chunkExtensions_iff (bytes : ByteArray) (start : Nat) :
    chunkExtensions bytes start = .ok () ↔ ChunkExtensionsGrammar bytes start :=
  ⟨chunkExtensions_sound bytes start, chunkExtensions_complete bytes start⟩

/-- The actual chunk-size parser proves numeral, body budget and the complete
extension grammar together; following chunk bytes are not part of this line. -/
theorem chunkSize_grammar (bytes : ByteArray) (limit n : Nat)
    (h : chunkSize bytes limit = .ok n) :
    ∃ stop, 0 < stop ∧ stop ≤ bytes.size ∧
      HexadecimalEncoding (bytes.extract 0 stop).data.toList n ∧ n ≤ limit ∧
      ChunkExtensionsGrammar bytes stop := by
  obtain ⟨stop, hs, hb, numeral, bound, ext⟩ := chunkSize_numeral bytes limit n h
  exact ⟨stop, hs, hb, numeral, bound, chunkExtensions_sound bytes stop ext⟩

end FastHTTP.Protocol
