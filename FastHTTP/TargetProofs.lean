import FastHTTP.AuthorityProofs

namespace FastHTTP.Protocol

/-- Byte-for-byte text comparison, with optional ASCII case folding. -/
def TextGrammar (bytes : ByteArray) (start stop : Nat) (text : String) (fold : Bool := false) : Prop :=
  stop - start = text.utf8ByteSize ∧ ∀ i (hi : i < text.utf8ByteSize),
    if fold then lower bytes[start + i]! = lower (text.getUTF8Byte ⟨i⟩ hi)
    else bytes[start + i]! = text.getUTF8Byte ⟨i⟩ hi

theorem equals_loop_iff (bytes : ByteArray) (start : Nat) (text : String) (fold : Bool) (i : Nat) :
    equals.loop bytes start text fold i = true ↔ ∀ j (hj : j < text.utf8ByteSize), i ≤ j →
      if fold then lower bytes[start + j]! = lower (text.getUTF8Byte ⟨j⟩ hj)
      else bytes[start + j]! = text.getUTF8Byte ⟨j⟩ hj := by
  rw [equals.loop]
  split
  · rename_i hi
    rw [Bool.and_eq_true, equals_loop_iff bytes start text fold (i + 1)]
    constructor
    · rintro ⟨head, tail⟩ j hj hij
      by_cases he : j = i
      · subst j
        cases fold <;> simpa using head
      · exact tail j hj (by omega)
    · intro h
      refine ⟨?_, fun j hj hij => h j hj (by omega)⟩
      have head := h i hi (by omega)
      cases fold <;> simpa using head
  · rename_i hi
    simp only [true_iff]
    intro j hj hij
    omega
termination_by text.utf8ByteSize - i

theorem equals_iff (bytes : ByteArray) (start stop : Nat) (text : String) (fold : Bool) :
    equals bytes start stop text fold = true ↔ TextGrammar bytes start stop text fold := by
  simp [equals, TextGrammar, equals_loop_iff]

/-- A literal-delimited lexical interval. Its endpoint is a grammatical witness,
not the output of a scan or a caller-supplied parser-correctness hypothesis. -/
def Delimited (bytes : ByteArray) (start stop : Nat) (accept : UInt8 → Bool) (last : Nat) : Prop :=
  start ≤ last ∧ last ≤ stop ∧ Octets bytes (fun b => accept b = true) start last ∧
    (last = stop ∨ accept bytes[last]! = false)

theorem delimited_iff (bytes : ByteArray) (start stop last : Nat) (accept : UInt8 → Bool)
    (hs : start ≤ stop) :
    Delimited bytes start stop accept last ↔ spanEnd bytes stop accept start = last := by
  constructor
  · rintro ⟨ha, hb, hc, hd⟩; exact spanEnd_complete bytes stop accept start last ha hb hc hd
  · intro h; subst last; exact spanEnd_spec bytes stop accept start hs

def AlphaOctet (b : UInt8) : Prop :=
  (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122)

def SchemeOctet (b : UInt8) : Prop :=
  AlphaOctet b ∨ DecimalOctet b ∨ b.toNat = 43 ∨ b.toNat = 45 ∨ b.toNat = 46

theorem alphaOctet_iff (b : UInt8) : alphaOctet b = true ↔ AlphaOctet b := by
  simp [alphaOctet, AlphaOctet, UInt8.le_iff_toNat_le]

theorem schemeOctet_iff (b : UInt8) : schemeOctet b = true ↔ SchemeOctet b := by
  unfold schemeOctet
  simp only [Bool.or_eq_true, alphaOctet_iff, decimalOctet_iff, beq_iff_eq]
  simp [SchemeOctet, ← UInt8.toNat_inj, or_assoc]

def SchemeGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  start < stop ∧ AlphaOctet bytes[start]! ∧ Octets bytes SchemeOctet (start + 1) stop

def PathGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  start ≤ stop ∧ stop ≤ bytes.size ∧ URIGrammar bytes PathOctet start stop

theorem pathGrammar_iff (bytes : ByteArray) (start stop : Nat) :
    PathGrammar bytes start stop ↔ validPathQuery bytes start stop = true :=
  (validPathQuery_iff bytes start stop).symm

/-- The authority form of an absolute URI: literal '//', an optional userinfo
only for non-HTTP schemes, a Host authority, and an optional slash/query suffix.
The literal boundaries are specified separately from all URI atom grammars. -/
def HierarchicalTargetGrammar (bytes : ByteArray) (first stop : Nat) (http : Bool)
    (info : TargetInfo) (colon : Nat) : Prop :=
  first + 2 ≤ stop ∧ bytes[first]! = 47 ∧ bytes[first + 1]! = 47 ∧
  ∃ path userEnd,
    Delimited bytes (first + 2) stop (fun b => b != 47 && b != 63) path ∧
    Delimited bytes (first + 2) path (fun b => b != 64) userEnd ∧
    let host := if userEnd < path then userEnd + 1 else first + 2
    (host = first + 2 ∨ (http = false ∧ host - 1 ≤ bytes.size ∧ first + 2 ≤ host - 1 ∧
      URIGrammar bytes FutureOctet (first + 2) (host - 1))) ∧
    (http = false ∨ (path ≠ host ∧ bytes[host]! ≠ 58)) ∧
    AuthorityGrammar bytes host path false ∧ PathGrammar bytes path stop ∧
    info = TargetInfo.mk path (some (host, path)) (some colon) (!http)

/-- Absolute URI with a valid scheme and either a hierarchy or a non-HTTP
path/query. Unsupported schemes remain grammatical and receive a later 501. -/
def AbsoluteTargetGrammar (bytes : ByteArray) (start stop : Nat) (info : TargetInfo) : Prop :=
  ∃ colon, Delimited bytes start stop (fun b => b != 58) colon ∧ colon < stop ∧
    SchemeGrammar bytes start colon ∧
    let http := equals bytes start colon "http" true || equals bytes start colon "https" true
    let first := colon + 1
    (HierarchicalTargetGrammar bytes first stop http info colon ∨
      ((first + 2 > stop ∨ bytes[first]! ≠ 47 ∨ bytes[first + 1]! ≠ 47) ∧ http = false ∧
        PathGrammar bytes first stop ∧
        info = { pathStart := first, schemeEnd := some colon, unsupportedScheme := true }))

/-- All four RFC 9112 request-target forms with exact returned metadata. Method
selection is explicit: CONNECT authority, OPTIONS '*', origin, or absolute URI. -/
noncomputable def TargetGrammar (bytes : ByteArray) (start stop : Nat) (options connect : Bool)
    (info : TargetInfo) : Prop := by
  classical
  exact start < stop ∧ stop ≤ bytes.size ∧
   if connect then AuthorityGrammar bytes start stop true ∧ info = { pathStart := start }
   else if TextGrammar bytes start stop "*" then options = true ∧ info = { pathStart := start }
   else if bytes[start]! = 47 then PathGrammar bytes start stop ∧ info = { pathStart := start }
   else AbsoluteTargetGrammar bytes start stop info

theorem uriFuture_iff (bytes : ByteArray) (start stop : Nat) :
    uriComponent bytes start stop futureOctet = true ↔
      start ≤ stop ∧ stop ≤ bytes.size ∧ URIGrammar bytes FutureOctet start stop := by
  rw [uriComponent_iff]
  have h : (fun b => futureOctet b = true) = FutureOctet := by
    funext b; exact propext (futureOctet_iff b)
  rw [h]

theorem parseHierarchicalTarget_iff (bytes : ByteArray) (first stop colon : Nat) (http : Bool)
    (info : TargetInfo) (hb : first + 2 ≤ stop) (h0 : bytes[first]! = 47)
    (h1 : bytes[first + 1]! = 47) :
    parseHierarchicalTarget bytes first stop http colon = .ok info ↔
      HierarchicalTargetGrammar bytes first stop http info colon := by
  let path := spanEnd bytes stop (fun b => b != 47 && b != 63) (first + 2)
  let userEnd := spanEnd bytes path (fun b => b != 64) (first + 2)
  let host := if userEnd < path then userEnd + 1 else first + 2
  have ps := spanEnd_spec bytes stop (fun b => b != 47 && b != 63) (first + 2) hb
  have us := spanEnd_spec bytes path (fun b => b != 64) (first + 2) ps.1
  have grammar : HierarchicalTargetGrammar bytes first stop http info colon ↔
      (host = first + 2 ∨ (http = false ∧ uriComponent bytes (first + 2) (host - 1) futureOctet = true)) ∧
      (http = false ∨ (path ≠ host ∧ bytes[host]! ≠ 58)) ∧
      validAuthority bytes host path false = true ∧ validPathQuery bytes path stop = true ∧
      info = TargetInfo.mk path (some (host, path)) (some colon) (!http) := by
    unfold HierarchicalTargetGrammar
    constructor
    · rintro ⟨_, _, _, p, u, hp, hu, tail⟩
      have ep : path = p := (delimited_iff _ _ _ _ _ hb).mp hp
      subst p
      have eu : userEnd = u := (delimited_iff _ _ _ _ _ ps.1).mp hu
      subst u
      obtain ⟨user, nonempty, auth, pathG, same⟩ := tail
      refine ⟨?_, nonempty, (validAuthority_iff _ _ _ _).mpr auth,
        (pathGrammar_iff _ _ _).mp pathG, same⟩
      rcases user with u | ⟨hc, hsize, hbound, atoms⟩
      · exact Or.inl u
      · exact Or.inr ⟨hc, (uriFuture_iff _ _ _).mpr ⟨hbound, hsize, atoms⟩⟩
    · intro tail
      refine ⟨hb, h0, h1, path, userEnd, ps, us, ?_⟩
      obtain ⟨user, nonempty, auth, pathG, same⟩ := tail
      refine ⟨?_, nonempty, (validAuthority_iff _ _ _ _).mp auth,
        (pathGrammar_iff _ _ _).mpr pathG, same⟩
      rcases user with u | ⟨hc, grammar⟩
      · exact Or.inl u
      · have hg := (uriFuture_iff _ _ _).mp grammar
        exact Or.inr ⟨hc, hg.2.1, hg.1, hg.2.2⟩
  rw [grammar]
  change (if (host != first + 2 && (http || !uriComponent bytes (first + 2) (host - 1) futureOctet)) ||
      (http && (path == host || bytes[host]! == 58)) ||
      !validAuthority bytes host path || !validPathQuery bytes path stop then Except.error 400
    else Except.ok (TargetInfo.mk path (some (host, path)) (some colon) (!http))) = Except.ok info ↔ _
  by_cases hu : host = first + 2 <;>
    cases http <;>
    cases huser : uriComponent bytes (first + 2) (host - 1) futureOctet <;>
    cases ha : validAuthority bytes host path false <;>
    cases hp : validPathQuery bytes path stop <;>
    simp [hu, huser, ha, hp, or_assoc, and_assoc] <;>
    (try split) <;> simp_all [and_assoc] <;> try exact eq_comm
  all_goals (intro hpath hcolon; simp_all)


theorem parseAbsoluteTarget_iff (bytes : ByteArray) (start stop : Nat) (info : TargetInfo)
    (hs : start < stop) :
    parseAbsoluteTarget bytes start stop = .ok info ↔ AbsoluteTargetGrammar bytes start stop info := by
  let colon := spanEnd bytes stop (fun b => b != 58) start
  let http := equals bytes start colon "http" true || equals bytes start colon "https" true
  have cs := spanEnd_spec bytes stop (fun b => b != 58) start (by omega)
  have grammar : AbsoluteTargetGrammar bytes start stop info ↔ colon < stop ∧
      SchemeGrammar bytes start colon ∧
      (HierarchicalTargetGrammar bytes (colon + 1) stop http info colon ∨
        ((colon + 1 + 2 > stop ∨ bytes[colon + 1]! ≠ 47 ∨ bytes[colon + 1 + 1]! ≠ 47) ∧
          http = false ∧ PathGrammar bytes (colon + 1) stop ∧
          info = TargetInfo.mk (colon + 1) none (some colon) true)) := by
    unfold AbsoluteTargetGrammar
    constructor
    · rintro ⟨c, hc, tail⟩
      have he : colon = c := (delimited_iff _ _ _ _ _ (by omega)).mp hc
      subst c
      exact tail
    · intro tail; exact ⟨colon, cs, tail⟩
  rw [grammar]
  unfold parseAbsoluteTarget
  change (do
    if colon == start || colon == stop then throw 400
    if !alphaOctet bytes[start]! || spanEnd bytes colon schemeOctet (start + 1) != colon then throw 400
    if colon + 1 + 2 > stop || bytes[colon + 1]! != 47 || bytes[colon + 1 + 1]! != 47 then
      if http || !validPathQuery bytes (colon + 1) stop then throw 400
      pure (TargetInfo.mk (colon + 1) none (some colon) true)
    else parseHierarchicalTarget bytes (colon + 1) stop http colon) = Except.ok info ↔ _
  by_cases he : colon = start
  · simp [he, SchemeGrammar, bind, Except.bind]
  by_cases hend : colon = stop
  · simp [hend, bind, Except.bind]
  have cstart : start < colon := by change start ≤ colon ∧ _ at cs; omega
  have cend : colon < stop := by change _ ∧ colon ≤ stop ∧ _ at cs; omega
  have scheme : SchemeGrammar bytes start colon ↔
      alphaOctet bytes[start]! = true ∧ spanEnd bytes colon schemeOctet (start + 1) = colon := by
    simp only [SchemeGrammar, cstart, true_and, alphaOctet_iff,
      spanEnd_eq_stop_iff bytes (start + 1) colon schemeOctet (by omega), schemeOctet_iff]
  rw [scheme]
  simp only [Bool.or_eq_true, beq_iff_eq, he, hend, false_or, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, throw, cend, true_and]
  by_cases halpha : alphaOctet bytes[start]! = true
  · by_cases hscheme : spanEnd bytes colon schemeOctet (start + 1) = colon
    · simp only [halpha, Bool.not_true, hscheme, bne_self_eq_false, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte, true_and]
      by_cases hh : colon + 1 + 2 > stop ∨ bytes[colon + 1]! ≠ 47 ∨ bytes[colon + 1 + 1]! ≠ 47
      · have noHierarchy : ¬ HierarchicalTargetGrammar bytes (colon + 1) stop http info colon := by
          intro h
          have hb := h.1
          have h0 := h.2.1
          have h1 := h.2.2.1
          rcases hh with hh | hh | hh
          · omega
          · exact hh h0
          · exact hh h1
        cases hc : http <;> cases hp : validPathQuery bytes (colon + 1) stop <;>
          simp only [hc] at noHierarchy ⊢ <;>
          simp [hh, noHierarchy, hp, pathGrammar_iff, or_assoc] <;> try exact eq_comm
      · have bounds : colon + 1 + 2 ≤ stop ∧ bytes[colon + 1]! = 47 ∧ bytes[colon + 1 + 1]! = 47 := by
          simpa using hh
        simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, or_assoc, hh, ↓reduceIte,
          false_and, or_false]
        exact parseHierarchicalTarget_iff bytes (colon + 1) stop colon http info bounds.1 bounds.2.1 bounds.2.2
    · simp [hscheme, throw]
  · simp [halpha, throw]

/-- Exact correctness of the production request-target parser for arbitrary
bytes, including rejected bounds, all four forms, authority selection and 501
scheme metadata. No HTTP parsing fact is assumed from lean-uv. -/
theorem parseTarget_iff (bytes : ByteArray) (start stop : Nat) (options connect : Bool)
    (info : TargetInfo) :
    parseTarget bytes start stop options connect = .ok info ↔ TargetGrammar bytes start stop options connect info := by
  classical
  unfold parseTarget TargetGrammar
  simp only [bind, Except.bind, pure, Except.pure]
  by_cases hs : start < stop
  · by_cases hb : stop ≤ bytes.size
    · simp only [show ¬ start ≥ stop by omega, show ¬ stop > bytes.size by omega,
        decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hs, hb, true_and]
      cases connect
      · simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases star : equals bytes start stop "*" = true
        · have hg := (equals_iff bytes start stop "*" false).mp star
          cases options <;> simp [star, hg] <;> try exact eq_comm
        · have hg : ¬ TextGrammar bytes start stop "*" := by
            simpa only [← equals_iff] using star
          simp only [star, hg, ↓reduceIte]
          by_cases slash : bytes[start]! = 47
          · cases hp : validPathQuery bytes start stop <;>
              simp [slash, hp, pathGrammar_iff] <;> try exact eq_comm
          · simp only [beq_iff_eq, slash, ↓reduceIte]
            exact parseAbsoluteTarget_iff bytes start stop info hs
      · cases ha : validAuthority bytes start stop true <;>
          simp [ha, ← validAuthority_iff] <;> try exact eq_comm
    · simp [hb, show stop > bytes.size by omega]
  · simp [hs, show start ≥ stop by omega]

end FastHTTP.Protocol
