import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedModuleDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Induction along the weighted quotient
The actual quotient functor has a full-image restriction on modules. Its
balanced induction counit is an equivalence, proved by lifting quotient
arrows and balancing, without flatness (SwappedVacuumCoordinates §6).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
  (J : C ⥤ D) [J.Full] (M : D ⥤ SVec k) [M.Additive] [M.Linear k]

/-- Fullness supplies the balancing arrow needed for the second counit
inverse product at an object in the literal image. -/
theorem unit_counit_of_full (v₀ : C) :
    (unit J (J ⋙ M) v₀).comp (counit J M (J.obj v₀)) = LinearMap.id := by
  apply hom_ext
  intro v h m
  calc
    (unit J (J ⋙ M) v₀ ∘ₗ counit J M (J.obj v₀)) (tensor J (J ⋙ M) v h m) =
        unit J (J ⋙ M) v₀ (M.map h m) :=
      congrArg (unit J (J ⋙ M) v₀) (counit_tensor J M (J.obj v₀) v h m)
    _ = tensor J (J ⋙ M) v₀ (𝟙 _) (M.map h m) := unit_apply J (J ⋙ M) v₀ _
    _ = tensor J (J ⋙ M) v h m := by
      have hb := balance J (J ⋙ M) (J.preimage h) (𝟙 (J.obj v₀)) m
      change tensor J (J ⋙ M) v ((J.map (J.preimage h)) ≫ 𝟙 (J.obj v₀)) m =
        tensor J (J ⋙ M) v₀ (𝟙 (J.obj v₀)) (M.map (J.map (J.preimage h)) m) at hb
      rw [Category.comp_id, Functor.map_preimage] at hb
      exact hb.symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- Lift an ordinary module isomorphism with even components. -/
def moduleIsoOfEvenNatIso (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) : F ≅ G where
  hom := SuperNatTrans.ofNatTrans e.hom hh
  inv := SuperNatTrans.ofNatTrans e.inv hi
  hom_inv_id := by
    apply Superfunctor.hom_ext_parity
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]
  inv_hom_id := by
    apply Superfunctor.hom_ext_parity
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N

instance oldTruncateFunctor_full : (Q).Full where
  map_surjective {v w} f := truncateOld_surjective D Sc cutoff N v.word w.word f

/-- The inverse uses the old word with the same literal boundary. -/
def quotientInductionCounitInverse (w : TruncatedCategory D Sc cutoff N) :
    M.obj w →ₗ[k] BalancedInduction.Obj Q (Q ⋙ M.toFunctor) w :=
  BalancedInduction.unit Q (Q ⋙ M.toFunctor) ⟨w.word⟩

theorem quotientInductionCounit_right_inv (w : TruncatedCategory D Sc cutoff N) :
    (BalancedInduction.counit Q M.toFunctor w).comp
      (quotientInductionCounitInverse D Sc cutoff N M w) = LinearMap.id :=
  BalancedInduction.counit_unit Q M.toFunctor ⟨w.word⟩

theorem quotientInductionCounit_left_inv (w : TruncatedCategory D Sc cutoff N) :
    (quotientInductionCounitInverse D Sc cutoff N M w).comp
      (BalancedInduction.counit Q M.toFunctor w) = LinearMap.id :=
  BalancedInduction.unit_counit_of_full Q M.toFunctor ⟨w.word⟩

/-- The pointwise equivalence is natural for the actual module action. -/
def quotientInductionCounitNatIso :
    (BalancedInduction.induced Q (weightedRestriction D Sc cutoff N M)).toFunctor ≅
      M.toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := BalancedInduction.counit Q M.toFunctor w
      inv := quotientInductionCounitInverse D Sc cutoff N M w
      hom_inv_id := quotientInductionCounit_left_inv D Sc cutoff N M w
      inv_hom_id := quotientInductionCounit_right_inv D Sc cutoff N M w })
    (fun a => BalancedInduction.counit_naturality Q M.toFunctor a)

/-- The actual quotient-induction counit is an even module isomorphism,
with the existing counit as its forward parity-zero component. -/
def quotientInductionCounitIso :
    BalancedInduction.induced Q (weightedRestriction D Sc cutoff N M) ≅ M :=
  moduleIsoOfEvenNatIso _ _ (quotientInductionCounitNatIso D Sc cutoff N M)
    (fun w => BalancedInduction.counit_mem Q M w)
    (fun w => BalancedInduction.unit_mem Q (weightedRestriction D Sc cutoff N M) ⟨w.word⟩)

end OddMath.QuiverHecke.ELVOld
