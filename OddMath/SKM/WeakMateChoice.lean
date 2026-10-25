import OddMath.SKM.WeakMateCoverage
import OddMath.SKM.WeakMatchingChoice

/-!
# Complete decorated inverse-mate families

The literal weak inverse mates cover each oriented matching class exactly once.
This assembles their endpoint bijection and actual dot serializers into the
weak realization used to transfer independence to strict choices in BE2 §8.
-/
noncomputable section
namespace OddMath.SKM.WeakMate
open StringDiagrams StringDiagrams.Chord DTMove
variable {I : Type*} {l : List I} {a b w : List (Letter I)}
  (U : MatchingBasisChoice (ups l ++ a) (b ++ w))
  (F : MatchingBasisChoice (a ++ dualW w) (dns l ++ b))

private theorem exists_target (R : U.members) :
    ∃ S : F.members, Iso (pairing₂ (a ++ dualW w) (matching l b w R.val))
      (pairing₂ (a ++ dualW w) S.val) := by
  have hm := isMatching (U.matching R.val R.property).1
  obtain ⟨hv, hl, hs⟩ := hm.pairing_properties
  obtain ⟨S, hS, hr, hi⟩ := exists_strictReduced_matching hv hl hs
  obtain ⟨T, hT, hTiso⟩ := F.complete S hS hr
  exact ⟨⟨T, hT⟩, hi.symm.trans hTiso.symm⟩

def target (R : U.members) : F.members := (exists_target U F R).choose

theorem target_pairing (R : U.members) :
    Iso (pairing₂ (a ++ dualW w) (matching l b w R.val))
      (pairing₂ (a ++ dualW w) (target U F R).val) := (exists_target U F R).choose_spec

theorem target_injective : Function.Injective (target U F) := by
  intro R S h
  apply Subtype.ext
  apply U.unique R.val R.property S.val S.property
  apply (pairing_iso_iff (U.matching R.val R.property).1 (U.matching S.val S.property).1).mp
  exact (target_pairing U F R).trans (h ▸ (target_pairing U F S).symm)

theorem target_surjective : Function.Surjective (target U F) := by
  intro S
  obtain ⟨R, hR, hred, hi⟩ := exists_strict_preimage (F.matching S.val S.property).1
  obtain ⟨T, hT, hTi⟩ := U.complete R hR hred
  refine ⟨⟨T, hT⟩, Subtype.ext ?_⟩
  apply F.unique _ (target U F ⟨T, hT⟩).property _ S.property
  exact (target_pairing U F ⟨T, hT⟩).symm.trans
    (((pairing_iso_iff (U.matching T hT).1 hR).mpr hTi).trans hi)

/-- The bijection is between the actual representative families, witnessed by
pairings of their literal cup/cap inverse mates. -/
def representativesEquiv : U.members ≃ F.members :=
  Equiv.ofBijective (target U F) ⟨target_injective U F, target_surjective U F⟩

theorem representativesEquiv_pairing (R : U.members) :
    Iso (pairing₂ (a ++ dualW w) (matching l b w R.val))
      (pairing₂ (a ++ dualW w) (representativesEquiv U F R).val) := target_pairing U F R

/-- The actual inverse-mate serializer, indexed by the strict target classes.
The bounded-point hypothesis holds for the top serializers used upstairs. -/
def weakChoice
    (hq : ∀ R : U.members, ∀ j ∈ leftEnds₂ (ups l ++ a) R.val,
      (U.points R j).1 ≤ R.val.length) : WeakMatchingChoice F where
  representative S := matching l b w ((representativesEquiv U F).symm S).val
  matching S := isMatching (U.matching _ ((representativesEquiv U F).symm S).property).1
  reduced S := reduced (U.matching _ ((representativesEquiv U F).symm S).property).1
    (U.matching _ ((representativesEquiv U F).symm S).property).2.1
  pairing S := by
    have h := representativesEquiv_pairing U F ((representativesEquiv U F).symm S)
    simpa only [Equiv.apply_symm_apply] using h
  points S := points (U.matching _ ((representativesEquiv U F).symm S).property).1
    (U.points ((representativesEquiv U F).symm S))
  onStrand S j hj := by
    exact (points_spec (U.matching _ ((representativesEquiv U F).symm S).property).1 _
      (fun z hz => ⟨hq _ z hz, U.onStrand _ z hz⟩) ⟨j, hj⟩).2
  serialize S n := moves l b w
    (U.serialize ((representativesEquiv U F).symm S)
      (n ∘ strandEquiv (U.matching _ ((representativesEquiv U F).symm S).property).1))
  decorates S n := by
    have hd := decorates (U.matching _ ((representativesEquiv U F).symm S).property).1
      (U.points ((representativesEquiv U F).symm S))
      (n ∘ strandEquiv (U.matching _ ((representativesEquiv U F).symm S).property).1)
      (U.decorates ((representativesEquiv U F).symm S) _)
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hd


/-- Reindex the actual weak serializer by its original upward matching and
strand counts. The direction makes the literal evaluation identity definitional. -/
def sourceLabelsEquiv
    (hq : ∀ R : U.members, ∀ j ∈ leftEnds₂ (ups l ++ a) R.val,
      (U.points R j).1 ≤ R.val.length) : F.Labels ≃ U.Labels :=
  Equiv.sigmaCongr (representativesEquiv U F).symm fun S =>
    Equiv.arrowCongr
      ((matchingStrandEquivOfIso ((weakChoice U F hq).pairing S)).symm.trans
        (strandEquiv (U.matching _ ((representativesEquiv U F).symm S).property).1).symm)
      (Equiv.refl ℕ)

theorem sourceLabelsEquiv_openDots
    (hq : ∀ R : U.members, ∀ j ∈ leftEnds₂ (ups l ++ a) R.val,
      (U.points R j).1 ≤ R.val.length) (t : F.Labels) :
    U.openDots (sourceLabelsEquiv U F hq t) = F.openDots t := by
  exact ((matchingStrandEquivOfIso ((weakChoice U F hq).pairing t.1)).symm.trans
    (strandEquiv (U.matching _ ((representativesEquiv U F).symm t.1).property).1).symm).symm.sum_comp t.2

/-- The weak family is precisely the literal inverse mate of the upstairs
serializer, not just a family with the same pairing or degree. -/
theorem weakChoice_layers
    (hq : ∀ R : U.members, ∀ j ∈ leftEnds₂ (ups l ++ a) R.val,
      (U.points R j).1 ≤ R.val.length) (t : F.Labels) :
    (weakChoice U F hq).layers t = dLay (a ++ dualW w)
      (moves l b w (U.serialize (sourceLabelsEquiv U F hq t).1
        (sourceLabelsEquiv U F hq t).2)) := rfl

end OddMath.SKM.WeakMate
