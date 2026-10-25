import OddMath.SKM.PositiveMatchingLayers
import OddMath.SKM.Nondegeneracy
import OddMath.SKM.MatchingChoiceCast
import OddMath.SKM.CupAttachmentReduced
import OddMath.QuiverHecke.Spanning
import Categorification.TypeA.NormalForm

/-!
# Canonical Coxeter words as upward matching diagrams

The crossing skeletons for the PBW-to-matching comparison in BE2 §8 and §11.
Coxeter words are reversed before being read bottom-to-top, matching `cw`.
-/
namespace OddMath.SKM.CanonicalUpward
open StringDiagrams StringDiagrams.Chord Categorification.TypeA
open OddMath.QuiverHecke
variable {I : Type*}

def crossingMoves (σ : List ℕ) : List (TMove (Letter I)) :=
  σ.reverse.map (fun p => .mv (.cross p))

@[simp] theorem crossingMoves_nil : crossingMoves (I := I) [] = [] := rfl

theorem crossingMoves_cons (p : ℕ) (σ : List ℕ) :
    crossingMoves (I := I) (p :: σ) = crossingMoves σ ++ [.mv (.cross p)] := by
  simp [crossingMoves]

private theorem tau_add (k p q : ℕ) : tau (k + p) (k + q) = k + tau p q := by
  unfold tau
  split_ifs <;> omega

private theorem swapAt_prefix {α : Type*} (P S : List α) {p : ℕ} (hp : p + 1 < S.length) :
    swapAt (P ++ S) (P.length + p) = P ++ swapAt S p := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_swapAt (P ++ S) (by simp; omega)]
  by_cases hi : i < P.length
  · have ht : tau (P.length + p) i = i := by unfold tau; split_ifs <;> omega
    simp [ht, List.getElem?_append, hi]
  · have he : i = P.length + (i - P.length) := by omega
    rw [he, tau_add]
    simp only [List.getElem?_append, Nat.add_sub_cancel_left, getElem?_swapAt S hp]
    split_ifs <;> first | rfl | omega

private theorem act_cross_eq_swapAt {α : Type*} (S : List α) {p : ℕ} (hp : p + 1 < S.length) :
    (PG.cross p).act S = swapAt S p := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < S.length
  · have hi' : i < ((PG.cross p).act S).length := by simpa using hi
    have ht : tau p i < S.length := by unfold tau; split_ifs <;> omega
    rw [getElem?_swapAt S hp, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem ht]
    congr 1
    exact act_cross_getElem hp i hi'
  · have hi' : ((PG.cross p).act S)[i]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)
    have hi'' : (swapAt S p)[i]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)
    rw [hi', hi'']

/-- The active endpoint state follows exactly the positional Coxeter word. -/
theorem crossing_run_state (σ : List ℕ) {P S : List (ℕ × Letter I)}
    {T : TState (Letter I)} (hs : T.st = P ++ S) (hv : ValidWord S.length σ) :
    (tRun flipL P.length T (crossingMoves σ)).st = P ++ tgt S (cw σ) := by
  induction σ with
  | nil => simpa [crossingMoves, tRun, cw, tgt] using hs
  | cons p σ ih =>
    have hσ : ValidWord S.length σ := fun q hq => hv q (List.mem_cons_of_mem _ hq)
    have hp : p + 1 < S.length := hv p List.mem_cons_self
    rw [crossingMoves_cons, tRun, List.foldl_append]
    change swapAt (tRun flipL P.length T (crossingMoves σ)).st (P.length + p) = _
    rw [ih hσ, swapAt_prefix _ _ (by simpa using hp)]
    simp only [cw_cons, tgt_append, tgt]
    rw [act_cross_eq_swapAt _ (by simpa using hp)]

private theorem fits_append {α : Type*} (d : α → α) (k : ℕ) (T : TState α)
    (R S : List (TMove α)) :
    TFits d k T (R ++ S) ↔ TFits d k T R ∧ TFits d k (tRun d k T R) S := by
  induction R generalizing T with
  | nil => simp [TFits, tRun]
  | cons m R ih => simp only [List.cons_append, TFits, ih, tRun, List.foldl_cons, and_assoc]

theorem crossing_fits (σ : List ℕ) {P S : List (ℕ × Letter I)}
    {T : TState (Letter I)} (hs : T.st = P ++ S) (hv : ValidWord S.length σ) :
    TFits flipL P.length T (crossingMoves σ) := by
  induction σ with
  | nil => trivial
  | cons p σ ih =>
    have hσ : ValidWord S.length σ := fun q hq => hv q (List.mem_cons_of_mem _ hq)
    rw [crossingMoves_cons, fits_append]
    refine ⟨ih hσ, ?_, trivial⟩
    change P.length + p + 1 < (tRun flipL P.length T (crossingMoves σ)).st.length
    rw [crossing_run_state σ hs hσ]
    have hp := hv p List.mem_cons_self
    simp only [List.length_append, length_tgt]
    omega


private theorem tgt_cw_map {α β : Type*} (f : α → β) (S : List α) (σ : List ℕ)
    (hv : ValidWord S.length σ) : tgt (S.map f) (cw σ) = (tgt S (cw σ)).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < S.length := by simpa using hi
    rw [tgt_cw_getElem hv (by simp) ⟨i, hi'⟩, List.getElem_map,
      List.getElem_map, tgt_cw_getElem hv rfl ⟨i, hi'⟩]

/-- Every valid Coxeter word is an actual matching, before reducedness is used. -/
theorem crossing_matching (A : List (Letter I)) (σ : List ℕ) (hv : ValidWord A.length σ) :
    IsMatching₂ A (tgt A (cw σ)) (crossingMoves σ) := by
  let P := (tStart A).st.take A.length
  let S := (tStart A).st.drop A.length
  have hs : (tStart A).st = P ++ S := (List.take_append_drop _ _).symm
  have hp : P.length = A.length := by
    simp only [P, List.length_take, (tStart_mirror A).1]
    omega
  have hlen : S.length = A.length := by
    simp only [S, List.length_drop, (tStart_mirror A).1]
    omega
  have hP : P.map Prod.snd = dualW A := by
    simp only [P, List.map_take, tStart_letters]
    rw [List.take_append_of_le_length (by rw [length_dualW]), show A.length = (dualW A).length from (length_dualW A).symm,
      List.take_length]
  have hS : S.map Prod.snd = A := by
    simp only [S, List.map_drop, tStart_letters]
    rw [← length_dualW A, List.drop_left]
  have hvS : ValidWord S.length σ := hlen ▸ hv
  have hf := crossing_fits σ hs hvS
  rw [hp] at hf
  refine ⟨hf, ?_⟩
  have he := congrArg (List.map Prod.snd) (crossing_run_state σ hs hvS)
  rw [hp, List.map_append, hP, ← tgt_cw_map Prod.snd S σ hvS, hS] at he
  have hl := letters_tRun (length_dualW A) (crossingMoves σ) _ A (tStart_letters A) hf
  rw [hl] at he
  exact List.append_cancel_left he


private theorem pairing_state (A : List (Letter I)) (σ : List ℕ) (hv : ValidWord A.length σ) :
    pairing₂ A (crossingMoves σ) = (tStart A).st.take A.length ++
      tgt ((tStart A).st.drop A.length) (cw σ) := by
  have hp : ((tStart A).st.take A.length).length = A.length := by
    simp only [List.length_take, (tStart_mirror A).1]; omega
  have hS : ((tStart A).st.drop A.length).length = A.length := by
    simp only [List.length_drop, (tStart_mirror A).1]; omega
  have h := crossing_run_state σ (P := (tStart A).st.take A.length)
    (S := (tStart A).st.drop A.length) (T := tStart A)
    (List.take_append_drop A.length (tStart A).st).symm (by rw [hS]; exact hv)
  rw [hp] at h
  exact h

private theorem pairing_get_left (A : List (Letter I)) (σ : List ℕ)
    (hv : ValidWord A.length σ) {j : ℕ} (hj : j < A.length) :
    (pairing₂ A (crossingMoves σ))[j]? = (tStart A).st[j]? := by
  rw [pairing_state A σ hv, List.getElem?_append_left]
  · exact List.getElem?_take_of_lt hj
  · simp only [List.length_take, (tStart_mirror A).1]; omega

private theorem pairing_get_right (A : List (Letter I)) (σ : List ℕ)
    (hv : ValidWord A.length σ) (j : Fin A.length) :
    (pairing₂ A (crossingMoves σ))[A.length + j.val]? =
      (tStart A).st[A.length + ((wordProd A.length σ)⁻¹ j).val]? := by
  let S := (tStart A).st.drop A.length
  have hS : S.length = A.length := by simp only [S, List.length_drop, (tStart_mirror A).1]; omega
  have hp : ((tStart A).st.take A.length).length = A.length := by
    simp only [List.length_take, (tStart_mirror A).1]; omega
  rw [pairing_state A σ hv, List.getElem?_append_right (by rw [hp]; omega), hp,
    Nat.add_sub_cancel_left]
  have h := tgt_cw_getElem hv hS j
  have he : (tgt S (cw σ))[j.val]? = S[((wordProd A.length σ)⁻¹ j).val]? := by
    rw [List.getElem?_eq_getElem (by simpa only [length_tgt, hS] using j.isLt),
      List.getElem?_eq_getElem (by rw [hS]; exact ((wordProd A.length σ)⁻¹ j).isLt)]
    exact congrArg some h
  rw [he]
  exact List.getElem?_drop

/-- The bottom-to-top endpoint permutation is the Coxeter word product,
with no identification of strands of repeated colour. -/
theorem crossing_pairing (A : List (Letter I)) (σ : List ℕ) (hv : ValidWord A.length σ)
    (j : Fin A.length) :
    Same (pairing₂ A (crossingMoves σ)) (A.length - 1 - j.val)
      (A.length + (wordProd A.length σ j).val) := by
  have hj : A.length - 1 - j.val < A.length := by omega
  have hm := (tStart_mirror A).2 (A.length - 1 - j.val) hj
  have he : 2 * A.length - 1 - (A.length - 1 - j.val) = A.length + j.val := by omega
  rw [he] at hm
  refine ⟨by omega, ?_, ?_⟩
  · change ((pairing₂ A (crossingMoves σ))[A.length - 1 - j.val]?).map Prod.fst ≠ none
    rw [pairing_get_left A σ hv hj]
    exact hm.2.1
  · change ((pairing₂ A (crossingMoves σ))[A.length - 1 - j.val]?).map Prod.fst =
      ((pairing₂ A (crossingMoves σ))[A.length + (wordProd A.length σ j).val]?).map Prod.fst
    rw [pairing_get_left A σ hv hj, pairing_get_right A σ hv]
    change idAt (tStart A).st (A.length - 1 - j.val) =
      idAt (tStart A).st (A.length + ((wordProd A.length σ).symm ((wordProd A.length σ) j)).val)
    rw [Equiv.symm_apply_apply]
    exact hm.2.2

@[simp] theorem ncr_crossingMoves (σ : List ℕ) : ncr₂ (crossingMoves (I := I) σ) = σ.length := by
  simp [crossingMoves, ncr₂, List.countP_map]


private theorem run_length (σ : List ℕ) (k : ℕ) (T : TState (Letter I)) :
    (tRun flipL k T (crossingMoves σ)).st.length = T.st.length := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    rw [crossingMoves_cons, tRun, List.foldl_append]
    change (swapAt (tRun flipL k T (crossingMoves σ)).st (k + p)).length = _
    rw [length_swapAt, ih]

theorem crossing_valid (A : List (Letter I)) (σ : List ℕ)
    (hf : TFits flipL A.length (tStart A) (crossingMoves σ)) : ValidWord A.length σ := by
  induction σ with
  | nil => exact fun _ h => False.elim (List.not_mem_nil h)
  | cons p σ ih =>
    rw [crossingMoves_cons, fits_append] at hf
    have hp : p + 1 < A.length := by
      have hh := hf.2.1
      change A.length + p + 1 < (tRun flipL A.length (tStart A) (crossingMoves σ)).st.length at hh
      rw [run_length, (tStart_mirror A).1] at hh
      omega
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ih hf.1 q hq

/-- Crossing-only matching syntax has a unique positional word. -/
theorem exists_crossingWord (R : List (TMove (Letter I)))
    (h : ∀ m ∈ R, ∃ p, m = TMove.mv (.cross p)) : ∃ σ, crossingMoves σ = R := by
  suffices hh : ∃ ρ : List ℕ, ρ.map (fun p => TMove.mv (Move.cross p)) = R by
    obtain ⟨ρ, rfl⟩ := hh
    exact ⟨ρ.reverse, by simp [crossingMoves]⟩
  induction R with
  | nil => exact ⟨[], rfl⟩
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := h m List.mem_cons_self
    obtain ⟨ρ, rfl⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨p :: ρ, rfl⟩

theorem critPts_crossingMoves (A : List (Letter I)) (σ : List ℕ) :
    critPts₂ A (crossingMoves σ) = [] := by
  have aux (ρ : List ℕ) (T : TState (Letter I)) (cl : List ℕ) :
      tCrit flipL A.length T cl (ρ.map (fun p => TMove.mv (.cross p))) = cl := by
    induction ρ generalizing T with
    | nil => rfl
    | cons p ρ ih => exact ih _
  exact aux σ.reverse (tStart A) []


theorem crossing_matching_ofFn {n : ℕ} (a : Fin n → I) (σ : List ℕ) (hv : ValidWord n σ) :
    IsMatching₂ (List.ofFn fun j => (true, a j))
      (List.ofFn fun j => (true, a ((wordProd n σ)⁻¹ j))) (crossingMoves σ) := by
  let A := List.ofFn fun j => (true, a j)
  have hA : A.length = n := List.length_ofFn
  have hm := crossing_matching A σ (by rwa [hA])
  have ht : tgt A (cw σ) = List.ofFn (fun j => (true, a ((wordProd n σ)⁻¹ j))) := by
    apply List.ext_getElem
    · simp [A]
    · intro j hj hj'
      have hjn : j < n := by simpa using hj'
      rw [tgt_cw_getElem hv hA ⟨j, hjn⟩]
      simp only [A, List.getElem_ofFn]
  exact ht ▸ hm

/-- A reduced Coxeter word is strictly reduced in the matching sense.
The proof compares minimal Coxeter length with an existing strictly reduced
positive realization of the same pairing; no inversion-count formula is needed. -/
theorem crossing_strict_of_reduced {n : ℕ} (a : Fin n → I) (σ : List ℕ)
    (hr : IsReduced n σ) : StrictReduced₂ (List.ofFn fun j => (true, a j)) (crossingMoves σ) := by
  let A := List.ofFn fun j => (true, a j)
  have hA : A.length = n := List.length_ofFn
  have hv : ValidWord A.length σ := by rw [hA]; exact hr.1
  have hM := crossing_matching_ofFn a σ hr.1
  obtain ⟨hvP, hlP, hsP⟩ := hM.pairing_properties
  obtain ⟨S, hS, hrS, hi⟩ := exists_strictReduced_matching hvP hlP hsP
  obtain ⟨τ, rfl⟩ := exists_crossingWord S
    (hS.positive_crossing_moves a (fun j => a ((wordProd n σ)⁻¹ j)) hrS)
  have hτ : ValidWord A.length τ := crossing_valid A τ hS.1
  have he : wordProd A.length τ = wordProd A.length σ := by
    apply Equiv.ext
    intro j
    have h₁ := (hi.2 _ _).mp (crossing_pairing A τ hτ j)
    have h₂ := crossing_pairing A σ hv j
    have hpos := hvP.unique h₁ h₂
    apply Fin.ext
    omega
  have hlen : σ.length ≤ τ.length := by
    rw [hr.2]
    exact length_le_of_wordProd_eq (hA ▸ hτ) (hA ▸ he)
  have hslen : τ.length ≤ cr (pairing₂ A (crossingMoves τ)) := by
    have hh := length_xs_le_cr ((tInv_tStart A).run hS.1) hrS.1.1 hrS.1.2
    change (tRun flipL A.length (tStart A) (crossingMoves τ)).xs.length ≤
      cr (pairing₂ A (crossingMoves τ)) at hh
    simpa only [length_xs_tRun, ncr_crossingMoves, show (tStart A).xs.length = 0 from rfl,
      Nat.zero_add] using hh
  have hlow : σ.length ≤ cr (pairing₂ A (crossingMoves σ)) :=
    hlen.trans (hslen.trans (cr_le_of_iso hi))
  refine ⟨?_, ?_⟩
  · apply reduced_of_length_xs_eq_cr ((tInv_tStart A).run hM.1)
    apply le_antisymm _ (cr_le_length_xs ((tInv_tStart A).run hM.1))
    change (tRun flipL A.length (tStart A) (crossingMoves σ)).xs.length ≤
      cr (pairing₂ A (crossingMoves σ))
    simpa only [length_xs_tRun, ncr_crossingMoves, show (tStart A).xs.length = 0 from rfl,
      Nat.zero_add] using hlow
  · rw [critPts_crossingMoves]
    exact List.nodup_nil

/-- The exact canonical PBW skeleton is an existing strict upward matching. -/
theorem canonical_matching {n : ℕ} (a : Fin n → I) (w : Equiv.Perm (Fin n)) :
    IsMatching₂ (List.ofFn fun j => (true, a j))
      (List.ofFn fun j => (true, a (w⁻¹ j))) (crossingMoves (canWord n w)) ∧
    StrictReduced₂ (List.ofFn fun j => (true, a j)) (crossingMoves (canWord n w)) := by
  refine ⟨?_, crossing_strict_of_reduced a _ (isReduced_canWord n w)⟩
  simpa only [wordProd_canWord] using crossing_matching_ofFn a _ (validWord_canWord n w)


theorem wordProd_eq_of_pairing_iso (A : List (Letter I)) (σ τ : List ℕ)
    (hσ : ValidWord A.length σ) (hτ : ValidWord A.length τ)
    (hi : Iso (pairing₂ A (crossingMoves σ)) (pairing₂ A (crossingMoves τ))) :
    wordProd A.length σ = wordProd A.length τ := by
  apply Equiv.ext
  intro j
  have h₁ := (hi.2 _ _).mp (crossing_pairing A σ hσ j)
  have h₂ := crossing_pairing A τ hτ j
  have hv := ((tInv_tStart A).run (crossing_matching A τ hτ).1).valid
  have hp := hv.unique h₁ h₂
  apply Fin.ext
  omega

theorem pairing_iso_of_wordProd_eq (A : List (Letter I)) (σ τ : List ℕ)
    (hσ : ValidWord A.length σ) (hτ : ValidWord A.length τ)
    (he : wordProd A.length σ = wordProd A.length τ) :
    Iso (pairing₂ A (crossingMoves σ)) (pairing₂ A (crossingMoves τ)) := by
  have hS : ((tStart A).st.drop A.length).length = A.length := by
    simp only [List.length_drop, (tStart_mirror A).1]; omega
  rw [pairing_state A σ hσ, pairing_state A τ hτ, tgt_cw_eq hσ hτ he hS]
  exact Iso.refl _

/-- Canonical PBW skeletons with the prescribed actual source and target. -/
noncomputable def members {n : ℕ} (a b : Fin n → I) : Set (List (TMove (Letter I))) :=
  {R | ∃ w : Equiv.Perm (Fin n), R = crossingMoves (canWord n w) ∧
    IsMatching₂ (List.ofFn fun j => (true, a j)) (List.ofFn fun j => (true, b j)) R}

theorem members_matching {n : ℕ} (a b : Fin n → I) (R) (hR : R ∈ members a b) :
    IsMatching₂ (List.ofFn fun j => (true, a j)) (List.ofFn fun j => (true, b j)) R ∧
      StrictReduced₂ (List.ofFn fun j => (true, a j)) R := by
  obtain ⟨w, rfl, hm⟩ := hR
  exact ⟨hm, (canonical_matching a w).2⟩

theorem members_unique {n : ℕ} (a b : Fin n → I) (R) (hR : R ∈ members a b)
    (S) (hS : S ∈ members a b)
    (hi : Iso (pairing₂ (List.ofFn fun j => (true, a j)) R)
      (pairing₂ (List.ofFn fun j => (true, a j)) S)) : R = S := by
  obtain ⟨w, rfl, _⟩ := hR
  obtain ⟨v, rfl, _⟩ := hS
  have he := wordProd_eq_of_pairing_iso (List.ofFn fun j => (true, a j))
    (canWord n w) (canWord n v)
    (by simpa only [List.length_ofFn] using validWord_canWord n w)
    (by simpa only [List.length_ofFn] using validWord_canWord n v) hi
  have hn : (List.ofFn fun j => (true, a j)).length = n := List.length_ofFn
  have transfer (m n : ℕ) (h : m = n) (ρ τ : List ℕ) :
      wordProd m ρ = wordProd m τ → wordProd n ρ = wordProd n τ := by
    cases h
    exact id
  have he' : wordProd n (canWord n w) = wordProd n (canWord n v) :=
    transfer _ _ hn _ _ he
  have hw : w = v := by simpa only [wordProd_canWord] using he'
  rw [hw]

theorem members_complete {n : ℕ} (a b : Fin n → I) (R)
    (hR : IsMatching₂ (List.ofFn fun j => (true, a j)) (List.ofFn fun j => (true, b j)) R)
    (hr : StrictReduced₂ (List.ofFn fun j => (true, a j)) R) :
    ∃ S ∈ members a b, Iso (pairing₂ (List.ofFn fun j => (true, a j)) S)
      (pairing₂ (List.ofFn fun j => (true, a j)) R) := by
  let A := List.ofFn fun j => (true, a j)
  have hA : A.length = n := List.length_ofFn
  obtain ⟨σ, rfl⟩ := exists_crossingWord R (hR.positive_crossing_moves a b hr)
  have hvA := crossing_valid A σ hR.1
  let w := wordProd n σ
  have hc : ValidWord A.length (canWord n w) := by rw [hA]; exact validWord_canWord n w
  have he : wordProd A.length (canWord n w) = wordProd A.length σ := by
    rw [hA, wordProd_canWord]
  have hm := crossing_matching A (canWord n w) hc
  have ht : tgt A (cw (canWord n w)) = List.ofFn (fun j => (true, b j)) := by
    rw [tgt_cw_eq hc hvA he rfl]
    exact (crossing_matching A σ hvA).2.symm.trans hR.2
  rw [ht] at hm
  exact ⟨crossingMoves (canWord n w), ⟨w, rfl, hm⟩,
    pairing_iso_of_wordProd_eq A _ _ hc hvA he⟩

/-- A complete matching choice whose literal skeletons are the PBW canonical
crossing words. The bottom-sorted point transformer may now be applied. -/
noncomputable def choice {n : ℕ} (a b : Fin n → I) :
    MatchingBasisChoice (List.ofFn fun j => (true, a j)) (List.ofFn fun j => (true, b j)) := by
  classical
  have hp (R : members a b) := matching_bounded_points (members_matching a b R R.property).1
  choose q hq using hp
  have hd (R : members a b) (c : MatchingStrand (List.ofFn fun j => (true, a j)) R.val → ℕ) :=
    exists_decorates₂_of_bounded_points _ R.val (q R)
      (fun j hj => (hq R j hj).2) (fun j hj => (hq R j hj).1) c
  choose τ hτ using hd
  exact ⟨members a b, members_matching a b, members_unique a b, members_complete a b,
    q, fun R j hj => (hq R j hj).2, τ, fun R c => (hτ R c).1⟩

@[simp] theorem choice_members {n : ℕ} (a b : Fin n → I) :
    (choice a b).members = members a b := rfl


private theorem ofFn_up_get (t : List I) :
    (List.ofFn fun j : Fin t.length => (true, t.get j)) = ups t := by
  simpa only [List.map_ofFn, Function.comp_def, ups, up] using
    congrArg (List.map (fun i : I => (true, i))) (List.ofFn_get t)

private theorem ofFn_up_get_cast (t t' : List I) (h : t.length = t'.length) :
    (List.ofFn fun j : Fin t.length => (true, t'.get (Fin.cast h j))) = ups t' := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn, ups, List.length_map] using h
  · intro i hi hj
    simp only [List.getElem_ofFn, ups, List.getElem_map, List.get_eq_getElem, Fin.val_cast]

/-- Literal-list version of the canonical skeleton family, aligned with the
quiver-Hecke PBW source and target words. -/
noncomputable def choiceList (t t' : List I) (h : t.length = t'.length) :
    MatchingBasisChoice (ups t) (ups t') :=
  (choice t.get (fun j => t'.get (Fin.cast h j))).cast
    (ofFn_up_get t) (ofFn_up_get_cast t t' h)

private theorem cast_members {a b a' b' : List (Letter I)} (F : MatchingBasisChoice a b)
    (ha : a = a') (hb : b = b') : (F.cast ha hb).members = F.members := by
  subst a' b'
  rfl

theorem choiceList_canonical (t t' : List I) (h : t.length = t'.length)
    (R : (choiceList t t' h).members) :
    ∃ w : Equiv.Perm (Fin t.length), R.val = crossingMoves (canWord t.length w) := by
  have hR := R.property
  change R.val ∈ ((choice t.get (fun j => t'.get (Fin.cast h j))).cast
    (ofFn_up_get t) (ofFn_up_get_cast t t' h)).members at hR
  rw [cast_members, choice_members] at hR
  obtain ⟨w, hw, _⟩ := hR
  exact ⟨w, hw⟩

noncomputable def choiceList_word (t t' : List I) (h : t.length = t'.length)
    (R : (choiceList t t' h).members) : Equiv.Perm (Fin t.length) :=
  (choiceList_canonical t t' h R).choose

theorem choiceList_word_spec (t t' : List I) (h : t.length = t'.length)
    (R : (choiceList t t' h).members) :
    R.val = (canWord t.length (choiceList_word t t' h R)).reverse.map
      (fun p => TMove.mv (Move.cross p)) := (choiceList_canonical t t' h R).choose_spec

end OddMath.SKM.CanonicalUpward
