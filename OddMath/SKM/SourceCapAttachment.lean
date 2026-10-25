import OddMath.SKM.SourceCapState
import OddMath.SKM.CapStrands
import OddMath.SKM.PointedMatching

/-! # Source cap attachment

Transport machinery for the isolated initial cap in the contextual sorting
construction of [BE2, Section 8]. Fresh counters and IDs shift together.

The main results are `cap_run` (literal state transport), `cap_strict_iff`,
`cap_pairing` and `cap_delete_iso`, and `onStrand_cap`. The construction `attach`
retains the residual pointed matching's serializer and places just the new cap's
dots before the cap. `labelEquiv` splits the actual strand counts, and
`attach_layers` gives the literal layer factorization. Finally,
`exists_pointed_cap_adapted` proves existence for every paired source class at
an arbitrary target; `cap_family_complete` transports residual completeness,
and `cap_pairing_iso_iff` reflects the isomorphisms needed for uniqueness.

These are cap attachment results, not the assembly of a complete source-sorting
choice including the distinct-endpoint crossing classes.
-/
namespace OddMath.SKM.SourceCapAttachment
open StringDiagrams StringDiagrams.Chord
variable {α : Type*}

namespace Shift
def idMap (f : ℕ → ℕ) (x : ℕ × α) : ℕ × α := (f x.1, x.2)

def rename (δ : ℕ) (f : ℕ → ℕ) (T : TState α) : TState α :=
  ⟨T.nxt + δ, T.st.map (idMap f), T.xs.map (Sym2.map f)⟩

private theorem idD_map (f : ℕ → ℕ) (s : List (ℕ × α)) (j : ℕ) (hj : j < s.length) :
    idD (s.map (idMap f)) j = f (idD s j) := by
  change (idAt (s.map (fun z => (f z.1, z.2))) j).getD 0 = f (idD s j)
  rw [idAt_map_fst s f j, idAt_eq_idD hj]
  rfl

private theorem rlId_map (f : ℕ → ℕ) (hf : Function.Injective f) (x y z : ℕ) :
    rlId (f x) (f y) (f z) = f (rlId x y z) := by
  simp only [rlId, hf.eq_iff]
  split_ifs <;> rfl

private theorem jn_map (f : ℕ → ℕ) (hf : Function.Injective f)
    (s : List (ℕ × α)) (r : ℕ) :
    jn (s.map (idMap f)) r = (jn s r).map (idMap f) := by
  simp only [jn, ← List.map_drop]
  cases s.drop r with
  | nil => rfl
  | cons A l =>
    cases l with
    | nil => rfl
    | cons B l =>
      simp only [List.map_cons, ← map_rmAt, List.map_map]
      apply List.map_congr_left
      intro z _
      exact Prod.ext (rlId_map f hf B.1 A.1 z.1) rfl

theorem ok (δ : ℕ) (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (m : TMove α) (hm : m.Ok d k T.st) :
    m.Ok d k (rename δ f T).st := by
  cases m with
  | mv m => cases m <;> simpa [TMove.Ok, rename] using hm
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    refine ⟨idMap f A, idMap f B, ?_, ?_, hl, hf.ne hn⟩
    · simp [rename, List.getElem?_map, hA]
    · simp [rename, List.getElem?_map, hB]

/-- Exact state transport, including the crossing-ID list. -/
theorem step (δ : ℕ) (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : f T.nxt = T.nxt + δ)
    (m : TMove α) (hm : m.Ok d k T.st) :
    tStep d k (rename δ f T) m = rename δ f (tStep d k T m) := by
  cases m with
  | mv m =>
    cases m with
    | cup g a => simp [tStep, rename, map_insAt, idMap, hfix, Nat.add_right_comm]
    | cross p =>
      have hp : k + p + 1 < T.st.length := hm
      simp only [tStep, rename, map_swapAt, List.map_append, List.map_cons, List.map_nil,
        idD_map f T.st (k + p) (by omega), idD_map f T.st (k + p + 1) hp]
      rfl
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [tStep, rename, jn_map f hf,
      idD_map f T.st (k + g) (by omega), idD_map f T.st (k + g + 1) hr]
    congr 1
    simp only [List.map_map, ← Sym2.map_comp]
    congr 2
    funext z
    exact rlId_map f hf _ _ z

private theorem next_le (d : α → α) (k : ℕ) (T : TState α) (m : TMove α) :
    T.nxt ≤ (tStep d k T m).nxt := by
  cases m with
  | mv m => cases m <;> simp [tStep]
  | cap g => rfl

/-- Every active move remains valid after injective source-ID relabelling. -/
theorem fits (δ : ℕ) (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n + δ)
    (R : List (TMove α)) (hR : TFits d k T R) : TFits d k (rename δ f T) R := by
  induction R generalizing T with
  | nil => trivial
  | cons m R ih =>
    refine ⟨ok δ d f hf k T m hR.1, ?_⟩
    rw [step δ d f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le d k T m).trans hn)) hR.2

/-- All state data, not only the terminal pairing, commute with relabelling. -/
theorem run (δ : ℕ) (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n + δ)
    (R : List (TMove α)) (hR : TFits d k T R) :
    tRun d k (rename δ f T) R = rename δ f (tRun d k T R) := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    change tRun d k (tStep d k (rename δ f T) m) R = rename δ f (tRun d k (tStep d k T m) R)
    rw [step δ d f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le d k T m).trans hn)) hR.2

/-- Exact transport of the critical-ID list, needed for strict representatives. -/
theorem critStep_map (δ : ℕ) (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : f T.nxt = T.nxt + δ)
    (cl : List ℕ) (m : TMove α) (hm : m.Ok d k T.st) :
    critStep k (rename δ f T) (cl.map f) m = (critStep k T cl m).map f := by
  cases m with
  | mv m => cases m <;> simp [critStep, rename, hfix]
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [critStep, rename, List.map_append, List.map_cons, List.map_nil,
      idD_map f T.st (k + g) (by omega), idD_map f T.st (k + g + 1) hr, List.map_map]
    congr 2
    funext z
    exact rlId_map f hf _ _ z

theorem crit (δ : ℕ) (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n + δ)
    (R : List (TMove α)) (hR : TFits d k T R) (cl : List ℕ) :
    tCrit d k (rename δ f T) (cl.map f) R = (tCrit d k T cl R).map f := by
  induction R generalizing T cl with
  | nil => rfl
  | cons m R ih =>
    simp only [tCrit]
    rw [critStep_map δ d f hf k T (hfix _ le_rfl) cl m hR.1,
      step δ d f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le d k T m).trans hn)) hR.2 _

/-- Cap renaming commutes with an injective ID map at valid active positions. -/
theorem stepRen_map (δ : ℕ) {I : Type*} (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState (Letter I)) (m : TMove (Letter I))
    (hm : m.Ok flipL k T.st) (x : ℕ) :
    stepRen k (rename δ f T) m (f x) = f (stepRen k T m x) := by
  cases m with
  | mv m => rfl
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [stepRen, rename, idD_map f T.st (k + g) (by omega),
      idD_map f T.st (k + g + 1) hr]
    exact rlId_map f hf _ _ x

/-- Full transport of distinguished-point strand IDs through subsequent caps. -/
theorem ren (δ : ℕ) {I : Type*} (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState (Letter I)) (hfix : ∀ n, T.nxt ≤ n → f n = n + δ)
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R) (x : ℕ) :
    tRen k (rename δ f T) R (f x) = f (tRen k T R x) := by
  induction R generalizing T x with
  | nil => rfl
  | cons m R ih =>
    simp only [tRen]
    rw [stepRen_map δ f hf k T m hR.1, step δ flipL f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le flipL k T m).trans hn)) hR.2 _

/-- Relabelling preserves the complete reducedness data at a valid state:
no repeated crossings, no diagonal crossings, and no repeated critical IDs. -/
theorem reducedData_iff (δ : ℕ) (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n + δ)
    (R : List (TMove α)) (hR : TFits d k T R) (cl : List ℕ) :
    ((tRun d k (rename δ f T) R).xs.Nodup ∧
      (∀ z ∈ (tRun d k (rename δ f T) R).xs, ¬ z.IsDiag) ∧
      (tCrit d k (rename δ f T) (cl.map f) R).Nodup) ↔
    ((tRun d k T R).xs.Nodup ∧
      (∀ z ∈ (tRun d k T R).xs, ¬ z.IsDiag) ∧
      (tCrit d k T cl R).Nodup) := by
  rw [run δ d f hf k T hfix R hR, crit δ d f hf k T hfix R hR cl]
  simp only [rename, List.nodup_map_iff (Sym2.map.injective hf),
    List.nodup_map_iff hf, List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨hn, hd, hc⟩
    refine ⟨hn, ?_, hc⟩
    intro z hz
    exact fun h => hd _ z hz rfl (h.map)
  · rintro ⟨hn, hd, hc⟩
    refine ⟨hn, ?_, hc⟩
    intro z x hx he
    subst z
    exact fun h => hd x hx ((Sym2.isDiag_map hf).mp h)

end Shift

namespace Frozen

/-- Insert the terminated source strand inside the frozen boundary. -/
def insert (p c : ℕ) (a b : α) (T : TState α) : TState α :=
  ⟨T.nxt, insAt T.st p (c, a) (c, b), T.xs⟩

/-- The terminated strand's ID is unavailable to the residual diagram. -/
def Safe (c : ℕ) (T : TState α) : Prop :=
  c < T.nxt ∧ ∀ z ∈ T.st, z.1 ≠ c

private theorem get_insert (s : List α) {p r : ℕ} (hpr : p ≤ r)
    (hr : r < s.length) (a b : α) :
    (insAt s p a b)[r + 2]? = s[r]? := by
  rw [getElem?_insAt s (by omega)]
  simp only [show ¬r + 2 < p by omega, show r + 2 ≠ p by omega,
    show r + 2 ≠ p + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]

private theorem idD_insert (s : List (ℕ × α)) {p r : ℕ} (hpr : p ≤ r)
    (hr : r < s.length) (a b : ℕ × α) :
    idD (insAt s p a b) (r + 2) = idD s r := by
  simp only [idD, idAt, get_insert s hpr hr]

private theorem rmAt_insert (s : List α) {p r : ℕ} (hpr : p ≤ r)
    (hr : r + 1 < s.length) (a b : α) :
    rmAt (insAt s p a b) (r + 2) = insAt (rmAt s r) p a b := by
  induction p generalizing s r with
  | zero => simp [insAt, rmAt]
  | succ p ih =>
    cases s with
    | nil => simp at hr
    | cons z s =>
      cases r with
      | zero => omega
      | succ r =>
        have hpr' : p ≤ r := by omega
        have hr' : r + 1 < s.length := by simpa using hr
        simpa [insAt, rmAt, Nat.add_assoc] using congrArg (List.cons z) (ih s hpr' hr')

private theorem jn_eq_map (s : List (ℕ × α)) {r : ℕ} (hr : r + 1 < s.length) :
    jn s r = (rmAt s r).map (rl (idD s (r + 1)) (idD s r)) := by
  obtain ⟨P, A, B, Q, rfl, rfl⟩ := exists_mid hr
  rw [jn_mid, rmAt_mid]
  simp [idD, idAt]

private theorem jn_insert (s : List (ℕ × α)) {p r c : ℕ} (hpr : p ≤ r)
    (hr : r + 1 < s.length) (hc : ∀ z ∈ s, z.1 ≠ c) (a b : α) :
    jn (insAt s p (c, a) (c, b)) (r + 2) = insAt (jn s r) p (c, a) (c, b) := by
  have hlen := length_insAt s (show p ≤ s.length by omega) (c, a) (c, b)
  have hb : idD s (r + 1) ≠ c := by
    rw [idD, idAt, List.getElem?_eq_getElem hr]
    exact hc _ (List.getElem_mem hr)
  rw [jn_eq_map _ (by omega), jn_eq_map _ hr,
    show r + 2 + 1 = (r + 1) + 2 by omega,
    idD_insert s (by omega) hr, idD_insert s hpr (by omega),
    rmAt_insert s hpr hr, map_insAt]
  simp [rl, rlId, Ne.symm hb]

private theorem state_ext {T U : TState α} (hn : T.nxt = U.nxt)
    (hs : T.st = U.st) (hx : T.xs = U.xs) : T = U := by
  cases T; cases U; cases hn; cases hs; cases hx; rfl

/-- Inserting a frozen pair leaves every active move valid. -/
theorem ok (d : α → α) {p k c : ℕ} (hpk : p ≤ k)
    (a b : α) (T : TState α) (hk : k ≤ T.st.length) (m : TMove α) (hm : m.Ok d k T.st) :
    m.Ok d (k + 2) (insert p c a b T).st := by
  have hlen := length_insAt T.st (show p ≤ T.st.length by omega) (c, a) (c, b)
  cases m with
  | mv m => cases m <;> simp only [TMove.Ok, insert] at * <;> omega
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    refine ⟨A, B, ?_, ?_, hl, hn⟩
    · change (insAt T.st p (c, a) (c, b))[k + 2 + g]? = some A
      rw [show k + 2 + g = (k + g) + 2 by omega, get_insert T.st (by omega) (by omega), hA]
    · change (insAt T.st p (c, a) (c, b))[k + 2 + g + 1]? = some B
      rw [show k + 2 + g + 1 = (k + g + 1) + 2 by omega,
        get_insert T.st (by omega) hr, hB]

/-- Actual active state evolution commutes with insertion of the isolated strand. -/
theorem step (d : α → α) {p k c : ℕ} (hpk : p ≤ k)
    (a b : α) (T : TState α) (hc : ∀ z ∈ T.st, z.1 ≠ c)
    (m : TMove α) (hm : m.Ok d k T.st) :
    tStep d (k + 2) (insert p c a b T) m = insert p c a b (tStep d k T m) := by
  cases m with
  | mv m =>
    cases m with
    | cup g x =>
      refine state_ext ?_ ?_ ?_ <;> try rfl
      change insAt (insAt T.st p (c, a) (c, b)) (k + 2 + g) _ _ = _
      rw [show k + 2 + g = (k + g) + 2 by omega, ← insAt_insAt T.st (by omega) hm]
      rfl
    | cross r =>
      have hr : k + r + 1 < T.st.length := hm
      refine state_ext ?_ ?_ ?_
      · rfl
      · change swapAt (insAt T.st p (c, a) (c, b)) (k + 2 + r) = _
        rw [show k + 2 + r = (k + r) + 2 by omega, ← insAt_swapAt_ge T.st (by omega) hr]
        rfl
      · change T.xs ++ [s(idD (insAt T.st p (c, a) (c, b)) (k + 2 + r),
          idD (insAt T.st p (c, a) (c, b)) (k + 2 + r + 1))] = _
        rw [show k + 2 + r = (k + r) + 2 by omega,
          idD_insert T.st (by omega) (by omega),
          show k + r + 2 + 1 = (k + r + 1) + 2 by omega,
          idD_insert T.st (by omega) hr]
        rfl
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    refine state_ext ?_ ?_ ?_
    · rfl
    · change jn (insAt T.st p (c, a) (c, b)) (k + 2 + g) = _
      rw [show k + 2 + g = (k + g) + 2 by omega, jn_insert T.st (by omega) hr hc]
      rfl
    · change T.xs.map (Sym2.map (rlId (idD (insAt T.st p (c, a) (c, b)) (k + 2 + g + 1))
        (idD (insAt T.st p (c, a) (c, b)) (k + 2 + g)))) = _
      rw [show k + 2 + g + 1 = (k + g + 1) + 2 by omega,
        show k + 2 + g = (k + g) + 2 by omega,
        idD_insert T.st (by omega) hr, idD_insert T.st (by omega) (by omega)]
      rfl

theorem safe_step (d : α → α) {c k : ℕ} (T : TState α) (hc : Safe c T)
    (m : TMove α) (hm : m.Ok d k T.st) : Safe c (tStep d k T m) := by
  cases m with
  | mv m =>
    cases m with
    | cup g a =>
      refine ⟨by change c < T.nxt + 1; have := hc.1; omega, ?_⟩
      intro z hz
      rcases mem_insAt hz with hz | rfl | rfl
      · exact hc.2 z hz
      · exact hc.1.ne'
      · exact hc.1.ne'
    | cross r => exact ⟨hc.1, fun z hz => hc.2 z (mem_swapAt hz)⟩
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    have hAc : A.1 ≠ c := hc.2 A (List.mem_of_getElem? hA)
    refine ⟨hc.1, ?_⟩
    intro z hz
    obtain ⟨z', hz', rfl⟩ := mem_jn hr hz
    have ha : idD T.st (k + g) = A.1 := by simp [idD, idAt, hA]
    change rlId _ _ z'.1 ≠ c
    rw [ha]
    unfold rlId
    split_ifs
    · exact hAc
    · exact hc.2 z' hz'

private theorem length_step (d : α → α) {k : ℕ} (T : TState α)
    (hk : k ≤ T.st.length) (m : TMove α) (hm : m.Ok d k T.st) :
    k ≤ (tStep d k T m).st.length := by
  cases m with
  | mv m =>
    cases m with
    | cup g a => simpa only [tStep, length_insAt T.st hm] using (by omega : k ≤ T.st.length + 2)
    | cross r => simpa [tStep] using hk
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    obtain ⟨P, A', B', Q, hs, hp⟩ := exists_mid hr
    simp only [tStep]
    rw [hs, ← hp, jn_mid]
    simp only [List.length_map, List.length_append]
    have hlen := congrArg List.length hs
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega

/-- Every residual run transports literally, with the same move word. -/
theorem run (d : α → α) {p k c : ℕ} (hpk : p ≤ k)
    (a b : α) (T : TState α) (hk : k ≤ T.st.length) (hc : Safe c T)
    (R : List (TMove α)) (hR : TFits d k T R) :
    TFits d (k + 2) (insert p c a b T) R ∧
      tRun d (k + 2) (insert p c a b T) R = insert p c a b (tRun d k T R) := by
  induction R generalizing T with
  | nil => exact ⟨trivial, rfl⟩
  | cons m R ih =>
    obtain ⟨hf, he⟩ := ih (tStep d k T m) (length_step d T hk m hR.1)
      (safe_step d T hc m hR.1) hR.2
    constructor
    · refine ⟨ok d hpk a b T hk m hR.1, ?_⟩
      rwa [step d hpk a b T hc.2 m hR.1]
    · change tRun d (k + 2) (tStep d (k + 2) (insert p c a b T) m) R = _
      rw [step d hpk a b T hc.2 m hR.1]
      exact he

private theorem critStep_eq (d : α → α) {p k c : ℕ} (hpk : p ≤ k)
    (a b : α) (T : TState α) (cl : List ℕ) (m : TMove α) (hm : m.Ok d k T.st) :
    critStep (k + 2) (insert p c a b T) cl m = critStep k T cl m := by
  cases m with
  | mv m => cases m <;> rfl
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [critStep, insert,
      show k + 2 + g = (k + g) + 2 by omega,
      show k + g + 2 + 1 = (k + g + 1) + 2 by omega,
      idD_insert (p := p) T.st (by omega) hr,
      idD_insert (p := p) T.st (by omega) (by omega : k + g < T.st.length)]

/-- The entire critical list is preserved by frozen insertion. -/
theorem crit (d : α → α) {p k c : ℕ} (hpk : p ≤ k)
    (a b : α) (T : TState α) (hc : Safe c T)
    (R : List (TMove α)) (hR : TFits d k T R) (cl : List ℕ) :
    tCrit d (k + 2) (insert p c a b T) cl R = tCrit d k T cl R := by
  induction R generalizing T cl with
  | nil => rfl
  | cons m R ih =>
    simp only [tCrit]
    rw [critStep_eq d hpk a b T cl m hR.1, step d hpk a b T hc.2 m hR.1]
    exact ih _ (safe_step d T hc m hR.1) hR.2 _

private theorem stepRen_eq {I : Type*} {p k c : ℕ} (hpk : p ≤ k)
    (a b : Letter I) (T : TState (Letter I)) (m : TMove (Letter I))
    (hm : m.Ok flipL k T.st) (z : ℕ) :
    stepRen (k + 2) (insert p c a b T) m z = stepRen k T m z := by
  cases m with
  | mv m => rfl
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [stepRen, insert,
      show k + 2 + g = (k + g) + 2 by omega,
      show k + g + 2 + 1 = (k + g + 1) + 2 by omega,
      idD_insert (p := p) T.st (by omega) hr,
      idD_insert (p := p) T.st (by omega) (by omega : k + g < T.st.length)]

/-- Point IDs follow the very same cap renamings after frozen insertion. -/
theorem ren {I : Type*} {p k c : ℕ} (hpk : p ≤ k)
    (a b : Letter I) (T : TState (Letter I)) (hc : Safe c T)
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R) (z : ℕ) :
    tRen (k + 2) (insert p c a b T) R z = tRen k T R z := by
  induction R generalizing T z with
  | nil => rfl
  | cons m R ih =>
    simp only [tRen]
    rw [stepRen_eq hpk a b T m hR.1, step flipL hpk a b T hc.2 m hR.1]
    exact ih _ (safe_step flipL T hc m hR.1) hR.2 _

private theorem critStep_safe (d : α → α) {k c : ℕ} (T : TState α) (hc : Safe c T)
    (cl : List ℕ) (m : TMove α) (hm : m.Ok d k T.st) :
    critStep k T (c :: cl) m = c :: critStep k T cl m ∧
      (c ∉ cl → c ∉ critStep k T cl m) := by
  cases m with
  | mv m =>
    cases m with
    | cup g a => simp [critStep, hc.1.ne]
    | cross r => exact ⟨rfl, id⟩
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have ha : A.1 ≠ c := hc.2 A (List.mem_of_getElem? hA)
    have hb : B.1 ≠ c := hc.2 B (List.mem_of_getElem? hB)
    simp only [critStep, idD, idAt, hA, hB, Option.map_some, Option.getD_some,
      List.map_cons, List.cons_append]
    constructor
    · simp [rlId, Ne.symm hb]
    · intro hcl h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨z, hz, he⟩ := List.mem_map.mp h
        unfold rlId at he
        split_ifs at he
        · exact ha he
        · exact hcl (he ▸ hz)
      · exact ha (List.mem_singleton.mp h).symm

/-- A reserved ID remains fixed, and never appears among residual critical IDs. -/
theorem crit_reserved (d : α → α) {k c : ℕ} (T : TState α) (hc : Safe c T)
    (R : List (TMove α)) (hR : TFits d k T R) (cl : List ℕ) :
    tCrit d k T (c :: cl) R = c :: tCrit d k T cl R ∧
      (c ∉ cl → c ∉ tCrit d k T cl R) := by
  induction R generalizing T cl with
  | nil => exact ⟨rfl, id⟩
  | cons m R ih =>
    obtain ⟨he, hn⟩ := critStep_safe d T hc cl m hR.1
    obtain ⟨he', hn'⟩ := ih (tStep d k T m) (safe_step d T hc m hR.1) hR.2 (critStep k T cl m)
    constructor
    · simpa only [tCrit, he] using he'
    · exact fun h => hn' (hn h)

theorem safe_run (d : α → α) {c k : ℕ} (T : TState α) (hc : Safe c T)
    (R : List (TMove α)) (hR : TFits d k T R) : Safe c (tRun d k T R) := by
  induction R generalizing T with
  | nil => exact hc
  | cons m R ih => exact ih _ (safe_step d T hc m hR.1) hR.2

theorem ren_reserved {I : Type*} {c k : ℕ} (T : TState (Letter I)) (hc : Safe c T)
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R) : tRen k T R c = c := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    have he : stepRen k T m c = c := by
      cases m with
      | mv m => rfl
      | cap g =>
        obtain ⟨A, B, hA, hB, hl, hn⟩ := hR.1
        have hb := hc.2 B (List.mem_of_getElem? hB)
        simp [stepRen, idD, idAt, hB, rlId, Ne.symm hb]
    simp only [tRen, he]
    exact ih _ (safe_step flipL T hc m hR.1) hR.2

end Frozen

variable {I : Type*}
open SourceCapState

/-- Leave IDs before the selected pair fixed and open a four-ID gap thereafter. -/
def liftId (q n : ℕ) : ℕ := if n < 2 * q then n else n + 4

theorem liftId_injective (q : ℕ) : Function.Injective (liftId q) := by
  intro a b h
  unfold liftId at h
  split_ifs at h <;> omega

theorem liftId_ne (q n : ℕ) : liftId q n ≠ 2 * q + 2 := by
  unfold liftId
  split_ifs <;> omega

private theorem indexed_map (f : ℕ → ℕ) (n m : ℕ) (w : List (Letter I))
    (h : ∀ j, j < w.length → f (n + 2 * j) = m + 2 * j) :
    (indexed n w).map (Shift.idMap f) = indexed m w := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < w.length
  · simp [indexed, hj, Shift.idMap, h j hj]
  · have hn : w.length ≤ j := by omega
    simp [indexed, hn]

private theorem map_flip (f : ℕ → ℕ) (s : List (ℕ × Letter I)) :
    (s.reverse.map flipSnd).map (Shift.idMap f) =
      (s.map (Shift.idMap f)).reverse.map flipSnd := by
  simp only [List.map_reverse, List.map_map]
  rfl

private theorem start_shift_st (L Q : List (Letter I)) :
    (Shift.rename 4 (liftId Q.length) (tStart (L ++ Q))).st =
      (before Q ++ after L Q) ++ (after L Q).reverse.map flipSnd ++
        (before Q).reverse.map flipSnd := by
  have he : cupLeft (dualW (L ++ Q)) = before Q ++ indexed (2 * Q.length) (dualW L) := by
    simp only [dualW_append]
    rw [show cupLeft (dualW Q ++ dualW L) = indexed 0 (dualW Q ++ dualW L) by simp [cupLeft, indexed]]
    rw [indexed_append]
    simp [before, length_dualW]
  have hb : (before Q).map (Shift.idMap (liftId Q.length)) = before Q := by
    apply indexed_map
    intro j hj
    simp only [length_dualW] at hj
    simp [liftId, hj]
  have ha : (indexed (2 * Q.length) (dualW L)).map (Shift.idMap (liftId Q.length)) = after L Q := by
    apply indexed_map
    intro j hj
    simp [liftId, show ¬2 * Q.length + 2 * j < 2 * Q.length by omega]
    omega
  simp only [Shift.rename, tStart, run_cupMoves, he, List.map_append, map_flip,
    List.reverse_append, hb, ha, List.append_assoc]

private theorem map_rl_fixed (s : List (ℕ × Letter I)) (u v : ℕ)
    (h : ∀ z ∈ s, z.1 ≠ u) : s.map (rl u v) = s := by
  conv_rhs => rw [← List.map_id s]
  apply List.map_congr_left
  intro z hz
  exact Prod.ext (by simp [rl, rlId, h z hz]) rfl

private theorem indexed_bounds (n : ℕ) (w : List (Letter I)) {z : ℕ × Letter I}
    (hz : z ∈ indexed n w) : n ≤ z.1 ∧ z.1 < n + 2 * w.length := by
  obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hz
  omega

/-- The explicit capped state is exactly a shifted residual start with its frozen pair inserted. -/
theorem capped_eq (L Q : List (Letter I)) (x : Letter I) :
    capped L Q x = Frozen.insert Q.length (2 * Q.length + 2) (flipL x) x
      (Shift.rename 4 (liftId Q.length) (tStart (L ++ Q))) := by
  have hb : ∀ z ∈ before Q, z.1 ≠ 2 * Q.length := by
    intro z hz
    have h := indexed_bounds 0 (dualW Q) hz
    simp only [length_dualW, zero_add] at h
    omega
  have ha : ∀ z ∈ after L Q, z.1 ≠ 2 * Q.length := by
    intro z hz
    have h := indexed_bounds (2 * Q.length + 4) (dualW L) hz
    omega
  have hf (s : List (ℕ × Letter I)) (h : ∀ z ∈ s, z.1 ≠ 2 * Q.length) :
      (s.reverse.map flipSnd).map (rl (2 * Q.length) (2 * Q.length + 2)) = s.reverse.map flipSnd := by
    apply map_rl_fixed
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact h w (List.mem_reverse.mp hw)
  apply Frozen.state_ext
  · simp [capped, Frozen.insert, Shift.rename, tStart, run_cupMoves, length_dualW]
    omega
  · change (capped L Q x).st = insAt (Shift.rename 4 (liftId Q.length) (tStart (L ++ Q))).st _ _ _
    rw [start_shift_st]
    simp only [capped, List.map_append, List.map_cons,
      map_rl_fixed _ _ _ hb, map_rl_fixed _ _ _ ha, hf _ hb, hf _ ha]
    have hp : Q.length = (before Q).length := by simp [before, length_dualW]
    rw [hp]
    simp [insAt, rl, rlId, List.append_assoc]
  · rfl

private theorem lift_fresh (L Q : List (Letter I)) (n : ℕ)
    (hn : (tStart (L ++ Q)).nxt ≤ n) : liftId Q.length n = n + 4 := by
  rw [residual_start] at hn
  change 2 * (L.length + Q.length) ≤ n at hn
  exact ite_eq_right (by omega)

private theorem shifted_safe (L Q : List (Letter I)) :
    Frozen.Safe (2 * Q.length + 2) (Shift.rename 4 (liftId Q.length) (tStart (L ++ Q))) := by
  constructor
  · simp only [Shift.rename, residual_start]
    omega
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact liftId_ne Q.length w.1

/-- The residual valid run attaches to the actual initial source cap.
No residual state-comparison premise is required. -/
theorem cap_run (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    TFits flipL (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
        (.cap L.length :: R) ∧
      tRun flipL (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
        (.cap L.length :: R) =
      Frozen.insert Q.length (2 * Q.length + 2) (flipL x) x
        (Shift.rename 4 (liftId Q.length) (tRun flipL (L ++ Q).length (tStart (L ++ Q)) R)) := by
  have hs := Shift.fits 4 flipL (liftId Q.length) (liftId_injective Q.length)
    (L ++ Q).length (tStart (L ++ Q)) (lift_fresh L Q) R hR
  have hk : (L ++ Q).length ≤ (Shift.rename 4 (liftId Q.length) (tStart (L ++ Q))).st.length := by
    simp [Shift.rename, tStart, run_cupMoves, length_dualW]
  obtain ⟨hf, he⟩ := Frozen.run flipL (show Q.length ≤ (L ++ Q).length by simp)
    (flipL x) x _ hk (shifted_safe L Q) R hs
  have hlen : (L ++ flipL x :: x :: Q).length = (L ++ Q).length + 2 := by simp; omega
  constructor
  · refine ⟨cap_ok L Q x, ?_⟩
    rw [start_cap, capped_eq, hlen]
    exact hf
  · change tRun flipL _ (tStep flipL _ _ _) R = _
    rw [start_cap, capped_eq, hlen, he,
      Shift.run 4 flipL (liftId Q.length) (liftId_injective Q.length) _ _ (lift_fresh L Q) R hR]

/-- Point strand IDs in the residual suffix are shifted by the same explicit map. -/
theorem cap_ren (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) (z : ℕ) :
    tRen (L ++ flipL x :: x :: Q).length (capped L Q x) R (liftId Q.length z) =
      liftId Q.length (tRen (L ++ Q).length (tStart (L ++ Q)) R z) := by
  have hs := Shift.fits 4 flipL (liftId Q.length) (liftId_injective Q.length)
    (L ++ Q).length (tStart (L ++ Q)) (lift_fresh L Q) R hR
  have hlen : (L ++ flipL x :: x :: Q).length = (L ++ Q).length + 2 := by simp; omega
  rw [capped_eq, hlen, Frozen.ren (show Q.length ≤ (L ++ Q).length by simp)
    (flipL x) x _ (shifted_safe L Q) R hs,
    Shift.ren 4 (liftId Q.length) (liftId_injective Q.length) _ _ (lift_fresh L Q) R hR]

/-- Full critical-ID formula: the initial cap is a new, disjoint critical strand. -/
theorem cap_crit (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    critPts₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R) =
      (2 * Q.length + 2) :: (critPts₂ (L ++ Q) R).map (liftId Q.length) := by
  have hs := Shift.fits 4 flipL (liftId Q.length) (liftId_injective Q.length)
    (L ++ Q).length (tStart (L ++ Q)) (lift_fresh L Q) R hR
  have hlen : (L ++ flipL x :: x :: Q).length = (L ++ Q).length + 2 := by simp; omega
  unfold critPts₂
  rw [crit_cap, capped_eq, hlen, Frozen.crit flipL (show Q.length ≤ (L ++ Q).length by simp)
    (flipL x) x _ (shifted_safe L Q) R hs,
    (Frozen.crit_reserved flipL _ (shifted_safe L Q) R hs []).1]
  congr 1
  exact Shift.crit 4 flipL (liftId Q.length) (liftId_injective Q.length) _ _ (lift_fresh L Q) R hR []

/-- Strictness is preserved and reflected by the actual cap attachment. -/
theorem cap_strict_iff (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    StrictReduced₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R) ↔ StrictReduced₂ (L ++ Q) R := by
  have hn : 2 * Q.length + 2 ∉ (critPts₂ (L ++ Q) R).map (liftId Q.length) := by
    intro h
    obtain ⟨n, hn, he⟩ := List.mem_map.mp h
    exact liftId_ne Q.length n he
  unfold StrictReduced₂ Reduced₂
  rw [(cap_run L Q x R hR).2, cap_crit L Q x R hR]
  simp only [Frozen.insert, Shift.rename, List.nodup_cons, hn, not_false_eq_true, true_and,
    List.nodup_map_iff (liftId_injective Q.length),
    List.nodup_map_iff (Sym2.map.injective (liftId_injective Q.length))]
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨⟨hn, hd⟩, hc⟩
    refine ⟨⟨hn, ?_⟩, hc⟩
    intro z hz hdiag
    exact hd _ z hz rfl hdiag.map
  · rintro ⟨⟨hn, hd⟩, hc⟩
    refine ⟨⟨hn, ?_⟩, hc⟩
    intro z w hw he hdiag
    subst z
    exact hd w hw ((Sym2.isDiag_map (liftId_injective Q.length)).mp hdiag)

/-- Attach a genuine strict residual matching, not merely state data. -/
theorem cap_matching {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ Q) Z R) :
    IsMatching₂ (L ++ flipL x :: x :: Q) Z (.cap L.length :: R) := by
  refine ⟨(cap_run L Q x R hR.1).1, ?_⟩
  change R.foldl tLet (tLet (L ++ flipL x :: x :: Q) (.cap L.length)) = Z
  rw [(tmLay_cap L Q (flipL x) x).2]
  exact hR.2

/-- Literal pairing formula, with the isolated pair at the selected frozen positions. -/
theorem cap_pairing (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    pairing₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R) =
      insAt ((pairing₂ (L ++ Q) R).map (Shift.idMap (liftId Q.length))) Q.length
        (2 * Q.length + 2, flipL x) (2 * Q.length + 2, x) := by
  exact congrArg TState.st (cap_run L Q x R hR).2

private theorem next_run_le (d : α → α) (k : ℕ) (T : TState α) (R : List (TMove α)) :
    T.nxt ≤ (tRun d k T R).nxt := by
  induction R generalizing T with
  | nil => exact le_rfl
  | cons m R ih => exact (Shift.next_le d k T m).trans (ih _)

private theorem run_length (a : List (Letter I)) (R : List (TMove (Letter I)))
    (hR : TFits flipL a.length (tStart a) R) :
    (tRun flipL a.length (tStart a) R).st.length = a.length + (R.foldl tLet a).length := by
  have h := congrArg List.length (letters_tRun (length_dualW a) R (tStart a) a (tStart_letters a) hR)
  simpa [length_dualW] using h

private theorem ren_after_prefix (L Q : List (Letter I)) (x : Letter I)
    (P R : List (TMove (Letter I)))
    (hP : TFits flipL (L ++ Q).length (tStart (L ++ Q)) P)
    (hR : TFits flipL (L ++ Q).length (tRun flipL (L ++ Q).length (tStart (L ++ Q)) P) R) (z : ℕ) :
    tRen ((L ++ Q).length + 2)
      (Frozen.insert Q.length (2 * Q.length + 2) (flipL x) x
        (Shift.rename 4 (liftId Q.length) (tRun flipL (L ++ Q).length (tStart (L ++ Q)) P)))
      R (liftId Q.length z) =
      liftId Q.length (tRen (L ++ Q).length (tRun flipL (L ++ Q).length (tStart (L ++ Q)) P) R z) := by
  have hfix : ∀ n, (tRun flipL (L ++ Q).length (tStart (L ++ Q)) P).nxt ≤ n →
      liftId Q.length n = n + 4 := fun n hn =>
    lift_fresh L Q n ((next_run_le flipL _ _ P).trans hn)
  have hs := Shift.fits 4 flipL (liftId Q.length) (liftId_injective Q.length) _ _ hfix R hR
  have hp := Shift.fits 4 flipL (liftId Q.length) (liftId_injective Q.length) _ _ (lift_fresh L Q) P hP
  have hc := Frozen.safe_run flipL _ (shifted_safe L Q) P hp
  rw [Shift.run 4 flipL (liftId Q.length) (liftId_injective Q.length) _ _ (lift_fresh L Q) P hP] at hc
  rw [Frozen.ren (show Q.length ≤ (L ++ Q).length by simp) (flipL x) x _ hc R hs,
    Shift.ren 4 (liftId Q.length) (liftId_injective Q.length) _ _ hfix R hR]

/-- Every bounded residual distinguished point is transported to the next height,
with its active position unchanged. Its terminal endpoint skips the frozen pair. -/
theorem onStrand_cap (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R)
    {j : ℕ} (hj : j < (pairing₂ (L ++ Q) R).length) {q : ℕ × ℕ}
    (hq : OnStrand₂ (L ++ Q) R j q) :
    OnStrand₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R) (insIdx Q.length j) (q.1 + 1, q.2) := by
  have hsplit := (tFits_append_at (L ++ Q).length (tStart (L ++ Q)) (R.take q.1) (R.drop q.1)).mp
    (by simpa using hR)
  have hp := (cap_run L Q x (R.take q.1) hsplit.1).2
  have hlen : (L ++ flipL x :: x :: Q).length = (L ++ Q).length + 2 := by simp; omega
  have hactive : (L ++ Q).length + q.2 <
      (tRun flipL (L ++ Q).length (tStart (L ++ Q)) (R.take q.1)).st.length := by
    rw [run_length _ _ hsplit.1]
    exact Nat.add_lt_add_left hq.1 _
  have hfinal : Q.length ≤ (pairing₂ (L ++ Q) R).length := by
    change Q.length ≤ (tRun flipL _ _ R).st.length
    rw [run_length _ _ hR]
    simp only [List.length_append]
    omega
  constructor
  · simpa only [List.take_succ_cons, List.foldl_cons, (tmLay_cap L Q (flipL x) x).2] using hq.1
  · change tRen _ (tRun flipL _ _ ((.cap L.length :: R).take (q.1 + 1)))
      ((.cap L.length :: R).drop (q.1 + 1))
      (idD (tRun flipL _ _ ((.cap L.length :: R).take (q.1 + 1))).st
        ((L ++ flipL x :: x :: Q).length + q.2)) = _
    rw [List.take_succ_cons, List.drop_succ_cons, hp, hlen]
    change tRen _ _ _ (idD (insAt
      ((tRun flipL (L ++ Q).length (tStart (L ++ Q)) (R.take q.1)).st.map (Shift.idMap (liftId Q.length)))
      Q.length _ _) ((L ++ Q).length + 2 + q.2)) = _
    rw [show (L ++ Q).length + 2 + q.2 = ((L ++ Q).length + q.2) + 2 by omega,
      Frozen.idD_insert _ (by simp only [List.length_append]; omega) (by simpa using hactive),
      Shift.idD_map _ _ _ hactive, ren_after_prefix L Q x _ _ hsplit.1 hsplit.2, hq.2,
      cap_pairing L Q x R hR]
    simp only [idD]
    rw [idAt_insAt_insIdx (s := (pairing₂ (L ++ Q) R).map (Shift.idMap (liftId Q.length)))
      (g := Q.length) (by simpa using hfinal)]
    change liftId Q.length (idD (pairing₂ (L ++ Q) R) j) =
      idD ((pairing₂ (L ++ Q) R).map (Shift.idMap (liftId Q.length))) j
    exact (Shift.idD_map _ _ _ hj).symm

private theorem boundary_le (L Q : List (Letter I)) (R : List (TMove (Letter I)))
    (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    Q.length ≤ (pairing₂ (L ++ Q) R).length := by
  change Q.length ≤ (tRun flipL _ _ R).st.length
  rw [run_length _ _ hR]
  simp only [List.length_append]
  omega

/-- The attached strand really pairs the selected adjacent source endpoints. -/
theorem cap_same (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    Same (pairing₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R)) Q.length (Q.length + 1) := by
  rw [cap_pairing L Q x R hR]
  have hp : Q.length ≤ ((pairing₂ (L ++ Q) R).map (Shift.idMap (liftId Q.length))).length := by
    simpa using boundary_le L Q R hR
  have hc : ∀ z ∈ (pairing₂ (L ++ Q) R).map (Shift.idMap (liftId Q.length)), z.1 ≠ 2 * Q.length + 2 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact liftId_ne _ _
  exact (same_insAt_iff hp hc (flipL x) x).2 (Or.inl ⟨rfl, rfl⟩)

/-- Deleting the attached pair recovers the residual pairing up to injective ID renaming. -/
theorem cap_delete_iso (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    Iso (pairing₂ (L ++ Q) R)
      (rmAt (pairing₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R)) Q.length) := by
  rw [cap_pairing L Q x R hR, rmAt_insAt _ _ _ _ (by simpa using boundary_le L Q R hR)]
  exact (iso_map_of_injOn _ (liftId Q.length) (fun _ _ _ _ h => liftId_injective Q.length h)).symm

/-- The initial cap can be pointed before it is consumed, at its left active leg. -/
theorem onStrand_initial_cap (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (hR : TFits flipL (L ++ Q).length (tStart (L ++ Q)) R) :
    OnStrand₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R) Q.length (0, L.length) := by
  have hs := Shift.fits 4 flipL (liftId Q.length) (liftId_injective Q.length)
    (L ++ Q).length (tStart (L ++ Q)) (lift_fresh L Q) R hR
  have hlen : (L ++ flipL x :: x :: Q).length = (L ++ Q).length + 2 := by simp; omega
  constructor
  · simp
  · change tRen _ (tStart _) (.cap L.length :: R)
      (idD (tStart (L ++ flipL x :: x :: Q)).st ((L ++ flipL x :: x :: Q).length + L.length)) = _
    rw [(cap_ids L Q x).1, ren_cap]
    simp only [rlId, show 2 * Q.length + 2 ≠ 2 * Q.length by omega, ↓reduceIte]
    rw [capped_eq, hlen, Frozen.ren (show Q.length ≤ (L ++ Q).length by simp)
      (flipL x) x _ (shifted_safe L Q) R hs,
      Frozen.ren_reserved _ (shifted_safe L Q) R hs, cap_pairing L Q x R hR]
    simp [idD, idAt_insAt (s := (pairing₂ (L ++ Q) R).map (Shift.idMap (liftId Q.length)))
      (g := Q.length) (by simpa using boundary_le L Q R hR)]

/-- Explicit splitting of attached strands into the isolated cap and residual strands. -/
noncomputable def strandEquiv {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ Q) Z R) :
    MatchingStrand (L ++ flipL x :: x :: Q) (.cap L.length :: R) ≃
      Unit ⊕ MatchingStrand (L ++ Q) R :=
  matchingStrandEquivOfCap (cap_matching x hR).pairing_properties.1
    (cap_same L Q x R hR.1) (cap_delete_iso L Q x R hR.1)

/-- Every pairing with the selected adjacent source pair has an actual strict
representative beginning with this cap, for an arbitrary target word. -/
theorem exists_cap_adapted {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ flipL x :: x :: Q) Z R)
    (hc : Same (pairing₂ (L ++ flipL x :: x :: Q) R) Q.length (Q.length + 1)) :
    ∃ S, IsMatching₂ (L ++ Q) Z S ∧ StrictReduced₂ (L ++ Q) S ∧
      IsMatching₂ (L ++ flipL x :: x :: Q) Z (.cap L.length :: S) ∧
      StrictReduced₂ (L ++ flipL x :: x :: Q) (.cap L.length :: S) ∧
      Iso (pairing₂ (L ++ flipL x :: x :: Q) (.cap L.length :: S))
        (pairing₂ (L ++ flipL x :: x :: Q) R) := by
  obtain ⟨hv, hl, hw⟩ := hR.pairing_properties
  have hletters : (rmAt (pairing₂ (L ++ flipL x :: x :: Q) R) Q.length).map Prod.snd =
      dualW (L ++ Q) ++ Z := by
    rw [map_rmAt, hw]
    simp only [dualW_append, dualW_cons, List.append_assoc, List.cons_append, List.nil_append]
    rw [← length_dualW Q]
    simp [rmAt]
  obtain ⟨S, hS, hs, hi⟩ := exists_strictReduced_matching (hv.rmAt hc) (hl.rmAt hc.lt_right) hletters
  have hA := cap_matching x hS
  refine ⟨S, hS, hs, hA, (cap_strict_iff L Q x S hS.1).2 hs, ?_⟩
  exact cap_iso_of_deleted hA.pairing_properties.1 hv (cap_same L Q x S hS.1) hc
    (hA.pairing_properties.2.2.trans hw.symm) ((cap_delete_iso L Q x S hS.1).symm.trans hi)

private theorem rmIdx_ne (p j : ℕ) : rmIdx p j ≠ p := by
  unfold rmIdx
  split_ifs <;> omega

/-- Exact strand enumeration for the actual attached matching. -/
theorem leftEnds_cap_perm {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ Q) Z R) :
    (leftEnds₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R)).Perm
      (Q.length :: (leftEnds₂ (L ++ Q) R).map (rmIdx Q.length)) := by
  let e := strandEquiv x hR
  have hn : (Q.length :: (leftEnds₂ (L ++ Q) R).map (rmIdx Q.length)).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, (nodup_leftEnds₂ _ _).map (fun _ _ h => rmIdx_inj.mp h)⟩
    intro h
    obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    exact rmIdx_ne _ _ he
  apply (List.perm_ext_iff_of_nodup (nodup_leftEnds₂ _ _) hn).mpr
  intro j
  simp only [List.mem_cons, List.mem_map]
  constructor
  · intro hj
    have he := congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩)
    cases hz : e ⟨j, hj⟩ with
    | inl u =>
      cases u
      rw [hz] at he
      exact Or.inl he.symm
    | inr z =>
      rw [hz] at he
      exact Or.inr ⟨z.val, z.property, he⟩
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact (e.symm (Sum.inl ())).property
    · exact (e.symm (Sum.inr ⟨z, hz⟩)).property

/-- The cap is pointed at height zero; all residual points move up one height. -/
def capPoints (l q : ℕ) (pts : ℕ → ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  if j = q then (0, l) else ((pts (capDown q j)).1 + 1, (pts (capDown q j)).2)

/-- Counts on the new cap and on the unchanged residual strands. -/
def capCounts (q b : ℕ) (n : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = q then b else n (capDown q j)

/-- Literal serializer: cap dots, initial cap, then the inherited residual serializer. -/
def capMoves (l b : ℕ) (ds : List (DTMove I)) : List (DTMove I) :=
  List.replicate b (.dt l) ++ .tm (.cap l) :: ds

private theorem capMoves_spec (l b : ℕ) (ds : List (DTMove I)) :
    DTMove.tmoves (capMoves l b ds) = .cap l :: DTMove.tmoves ds ∧
    DTMove.dotPts (capMoves l b ds) = List.replicate b (0, l) ++
      (DTMove.dotPts ds).map (fun z => (z.1 + 1, z.2)) := by
  induction b with
  | zero => simp [capMoves, DTMove.tmoves, DTMove.dotPts]
  | succ b ih => simpa [capMoves, List.replicate_succ, DTMove.tmoves, DTMove.dotPts] using ih

/-- The inherited serializer has exactly the cap-adapted points and counts. -/
theorem decorates_capMoves {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ Q) Z R) (b : ℕ)
    {pts : ℕ → ℕ × ℕ} {n : ℕ → ℕ} {ds : List (DTMove I)}
    (hd : Decorates₂ (L ++ Q) R pts n ds) :
    Decorates₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R)
      (capPoints L.length Q.length pts) (capCounts Q.length b n) (capMoves L.length b ds) := by
  constructor
  · rw [(capMoves_spec L.length b ds).1, hd.1]
  · rw [(capMoves_spec L.length b ds).2]
    have hp := (leftEnds_cap_perm x hR).flatMap_right
      (fun j => List.replicate (capCounts Q.length b n j) (capPoints L.length Q.length pts j))
    simp only [List.flatMap_cons, List.flatMap_map, capPoints, capCounts,
      ite_eq_right (rmIdx_ne _ _), capDown_rmIdx, ite_true] at hp
    have hd' := (hd.2.map (fun z => (z.1 + 1, z.2))).append_left (List.replicate b (0, L.length))
    simp only [List.map_flatMap, List.map_replicate] at hd'
    exact hd'.trans hp.symm

/-- Both boundedness and actual strand membership of every transported point. -/
theorem capPoints_spec {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ Q) Z R)
    {pts : ℕ → ℕ × ℕ}
    (hb : ∀ j ∈ leftEnds₂ (L ++ Q) R, (pts j).1 ≤ R.length)
    (hp : ∀ j ∈ leftEnds₂ (L ++ Q) R, OnStrand₂ (L ++ Q) R j (pts j)) :
    ∀ j ∈ leftEnds₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R),
      (capPoints L.length Q.length pts j).1 ≤ (.cap L.length :: R).length ∧
      OnStrand₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R) j (capPoints L.length Q.length pts j) := by
  intro j hj
  have h := (leftEnds_cap_perm x hR).mem_iff.mp hj
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨z, hz, rfl⟩
  · simp only [capPoints, ite_true]
    exact ⟨Nat.zero_le _, onStrand_initial_cap L Q x R hR.1⟩
  · simp only [capPoints, ite_eq_right (rmIdx_ne _ _), capDown_rmIdx]
    exact ⟨Nat.add_le_add_right (hb z hz) 1,
      onStrand_cap L Q x R hR.1 (mem_leftEnds₂.mp hz).1 (hp z hz)⟩

private theorem capCounts_on_strands {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ Q) Z R)
    (n : MatchingStrand (L ++ flipL x :: x :: Q) (.cap L.length :: R) → ℕ)
    (j : ℕ) (hj : j ∈ leftEnds₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R)) :
    capCounts Q.length
      (n (capStrand (cap_matching x hR).pairing_properties.1 (cap_same L Q x R hR.1)))
      (strandCounts (fun z => n (capRemainingStrand (cap_matching x hR).pairing_properties.1
        (cap_same L Q x R hR.1) (cap_delete_iso L Q x R hR.1) z))) j = strandCounts n j := by
  classical
  have h := (leftEnds_cap_perm x hR).mem_iff.mp hj
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨z, hz, rfl⟩
  · simp [capCounts, strandCounts, hj, capStrand]
  · simp [capCounts, rmIdx_ne, capDown_rmIdx, strandCounts, hz, hj, capRemainingStrand]

/-- Actual cap-adapted pointed attachment. The original points and serializer
are retained in the suffix; only the new cap's dots precede the cap. -/
noncomputable def attach {L Q Z : List (Letter I)} (x : Letter I)
    (F : PointedMatching (L ++ Q) Z) : PointedMatching (L ++ flipL x :: x :: Q) Z := by
  let hv := (cap_matching x F.matching).pairing_properties.1
  let hc := cap_same L Q x F.moves F.matching.1
  let hi := cap_delete_iso L Q x F.moves F.matching.1
  refine ⟨.cap L.length :: F.moves, cap_matching x F.matching,
    (cap_strict_iff L Q x F.moves F.matching.1).2 F.strict,
    capPoints L.length Q.length F.points,
    fun j hj => (capPoints_spec x F.matching F.bounded F.onStrand j hj).1,
    fun j hj => (capPoints_spec x F.matching F.bounded F.onStrand j hj).2,
    fun n => capMoves L.length (n (capStrand hv hc))
      (F.serialize (fun z => n (capRemainingStrand hv hc hi z))), ?_⟩
  intro n
  have hd := decorates_capMoves x F.matching (n (capStrand hv hc))
    (F.decorates (fun z => n (capRemainingStrand hv hc hi z)))
  refine ⟨hd.1, hd.2.trans ?_⟩
  apply List.Perm.of_eq
  apply List.flatMap_congr
  intro j hj
  rw [capCounts_on_strands x F.matching n j hj]

@[simp] theorem attach_moves {L Q Z : List (Letter I)} (x : Letter I)
    (F : PointedMatching (L ++ Q) Z) : (attach x F).moves = .cap L.length :: F.moves := rfl

@[simp] theorem attach_points {L Q Z : List (Letter I)} (x : Letter I)
    (F : PointedMatching (L ++ Q) Z) :
    (attach x F).points = capPoints L.length Q.length F.points := rfl

/-- Complete existence of cap-adapted pointed representatives with actual serializers. -/
theorem exists_pointed_cap_adapted {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ flipL x :: x :: Q) Z R)
    (hc : Same (pairing₂ (L ++ flipL x :: x :: Q) R) Q.length (Q.length + 1)) :
    ∃ F : PointedMatching (L ++ Q) Z,
      Iso (pairing₂ (L ++ flipL x :: x :: Q) (attach x F).moves)
        (pairing₂ (L ++ flipL x :: x :: Q) R) := by
  obtain ⟨S, hS, hs, _, _, hi⟩ := exists_cap_adapted x hR hc
  exact ⟨PointedMatching.ofStrict hS hs, hi⟩

/-- The serializer evaluates to cap dots, the actual contextual cap layers,
and exactly the inherited residual layers. -/
theorem capMoves_layers (L Q : List (Letter I)) (x : Letter I) (b : ℕ) (ds : List (DTMove I)) :
    dLay (L ++ flipL x :: x :: Q) (capMoves L.length b ds) =
      (List.replicate b (dotOn (L ++ flipL x :: x :: Q) L.length)).flatten ++
        (xCapL x).map (xwhL L Q) ++ dLay (L ++ Q) ds := by
  induction b with
  | zero => simp [capMoves, dLay, (tmLay_cap L Q (flipL x) x).1, (tmLay_cap L Q (flipL x) x).2]
  | succ b ih =>
    change dotOn _ _ ++ dLay _ (capMoves L.length b ds) = _
    rw [ih]
    simp [List.replicate_succ, List.append_assoc]

/-- Pairing isomorphism of actual cap attachments is exactly residual pairing
isomorphism; in particular uniqueness of a residual family is retained. -/
theorem cap_pairing_iso_iff {L Q Z : List (Letter I)} (x : Letter I)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (L ++ Q) Z R) (hS : IsMatching₂ (L ++ Q) Z S) :
    Iso (pairing₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R))
        (pairing₂ (L ++ flipL x :: x :: Q) (.cap L.length :: S)) ↔
      Iso (pairing₂ (L ++ Q) R) (pairing₂ (L ++ Q) S) := by
  constructor
  · intro hi
    exact (cap_delete_iso L Q x R hR.1).trans
      ((hi.rmAt (cap_same L Q x R hR.1).lt_right).trans (cap_delete_iso L Q x S hS.1).symm)
  · intro hi
    have hA := cap_matching x hR
    have hB := cap_matching x hS
    exact cap_iso_of_deleted hA.pairing_properties.1 hB.pairing_properties.1
      (cap_same L Q x R hR.1) (cap_same L Q x S hS.1)
      (hA.pairing_properties.2.2.trans hB.pairing_properties.2.2.symm)
      ((cap_delete_iso L Q x R hR.1).symm.trans (hi.trans (cap_delete_iso L Q x S hS.1)))

/-- Any complete residual family yields a complete *actual* cap-adapted family,
with no separately assumed cap comparison or realization map. -/
theorem cap_family_complete {L Q Z : List (Letter I)} (x : Letter I)
    (M : Set (List (TMove (Letter I))))
    (hm : ∀ S ∈ M, IsMatching₂ (L ++ Q) Z S)
    (hcomplete : ∀ R, IsMatching₂ (L ++ Q) Z R → StrictReduced₂ (L ++ Q) R →
      ∃ S ∈ M, Iso (pairing₂ (L ++ Q) S) (pairing₂ (L ++ Q) R))
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ flipL x :: x :: Q) Z R)
    (hc : Same (pairing₂ (L ++ flipL x :: x :: Q) R) Q.length (Q.length + 1)) :
    ∃ S ∈ M, Iso (pairing₂ (L ++ flipL x :: x :: Q) (.cap L.length :: S))
      (pairing₂ (L ++ flipL x :: x :: Q) R) := by
  obtain ⟨T, hT, ht, _, _, hi⟩ := exists_cap_adapted x hR hc
  obtain ⟨S, hS, hST⟩ := hcomplete T hT ht
  exact ⟨S, hS, ((cap_pairing_iso_iff x (hm S hS) hT).2 hST).trans hi⟩

/-- Natural strand counts split bijectively into one cap count and residual counts. -/
noncomputable def labelEquiv {L Q Z : List (Letter I)} (x : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ Q) Z R) :
    (MatchingStrand (L ++ flipL x :: x :: Q) (.cap L.length :: R) → ℕ) ≃
      ℕ × (MatchingStrand (L ++ Q) R → ℕ) :=
  capLabelEquiv (cap_matching x hR).pairing_properties.1
    (cap_same L Q x R hR.1) (cap_delete_iso L Q x R hR.1)

/-- Serializer compatibility uses the constructed label equivalence. -/
theorem attach_serialize {L Q Z : List (Letter I)} (x : Letter I)
    (F : PointedMatching (L ++ Q) Z)
    (n : MatchingStrand (L ++ flipL x :: x :: Q) (attach x F).moves → ℕ) :
    (attach x F).serialize n = capMoves L.length ((labelEquiv x F.matching) n).1
      (F.serialize ((labelEquiv x F.matching) n).2) := rfl

/-- The attached pointed representative has precisely the expected layer factorization. -/
theorem attach_layers {L Q Z : List (Letter I)} (x : Letter I)
    (F : PointedMatching (L ++ Q) Z)
    (n : MatchingStrand (L ++ flipL x :: x :: Q) (attach x F).moves → ℕ) :
    (attach x F).layers n =
      (List.replicate ((labelEquiv x F.matching) n).1
        (dotOn (L ++ flipL x :: x :: Q) L.length)).flatten ++
      (xCapL x).map (xwhL L Q) ++ F.layers ((labelEquiv x F.matching) n).2 := by
  exact capMoves_layers L Q x _ _

end OddMath.SKM.SourceCapAttachment
