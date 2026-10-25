import OddMath.QuiverHecke.UpwardMatchingIndependence
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
open CategoryTheory StringDiagrams StringDiagrams.Chord OddMath.QuiverHecke OddMath.SKM
open scoped Classical
open OddMath.SKM.MixedCrossingLocalExamples

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def bubbles : CScalars params where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [params]

private def t : List Bool := [false, true]
private def F := CanonicalUpward.choiceList t t rfl
private def representative : F.members := by
  have hm : IsMatching₂ (ups t) (ups t) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (ups t) [] := by
    constructor
    · change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
      simp
    · change ([] : List ℕ).Nodup
      simp
  let h := F.complete [] hm hr
  exact ⟨h.choose, h.choose_spec.1⟩

private def label : (F.atBottomSortedUp t t).Labels := ⟨representative, fun _ => 0⟩
private def i : {i : Bool // oddDatum.parity i = 1} := ⟨false, rfl⟩
private def j : {i : Bool // oddDatum.parity i = 1} := ⟨true, rfl⟩

/-- A nonzero two-odd coefficient on an actual inhabited canonical matching
family remains nonzero under the proved matching-to-affine reindexing. -/
example : canonicalChoiceReindex oddDatum F (CanonicalUpward.choiceList_word t t rfl)
    (CanonicalUpward.choiceList_word_spec t t rfl)
    (Finsupp.single label (SYM.coefficientBasis oddDatum ℚ (0, {i, j}))) ≠ 0 := by
  simpa only [canonicalChoiceReindex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    ne_eq, Finsupp.single_eq_zero] using (SYM.coefficientBasis oddDatum ℚ).ne_zero (0, {i, j})

/-- The only remaining premise is the actual fixed-weight action observation
family. Canonical matching independence is now a conclusion, not an input. -/
example (hobs : ∀ a b : List Bool, wt oddDatum 0 (ups a) = wt oddDatum 0 (ups b) →
    ∀ μ : Bool → ℤ, FiniteUpwardObservations oddDatum params bubbles μ a b) :
    WeakMate.UpwardIndependence bubbles :=
  upward_independence_of_finite_observations oddDatum params bubbles hobs

#print axioms canonicalChoice_independence
#print axioms upward_independence_of_coefficientMap
#print axioms upward_independence_of_finite_observations
