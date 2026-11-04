import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPathCoordinates

/-! # The raw restricted probe dot in the successor source chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
the raw probe dot on the upper loop follows the same selected successor
chart as the whole-weight left cap, at every input weight module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u

private theorem rightWhisker_total
    {k : Type u} [CommRing k] {A B C : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (f : F ⟶ G) (Z : B ⟶ C) (N : A) :
    (f ▷ Z).total N = Z.map (f.total N) := by
  change Z.map (f.app 0 N) + Z.map (f.app 1 N) = Z.map (f.app 0 N + f.app 1 N)
  exact (Functor.map_add Z.toFunctor).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x)
local notation "ε" => blockSucc D Λ i h δ
local notation "perm" => probeOldBlockTarget_perm D i Λ h δ ε rfl
local notation "R" => probeOldBlockRes D Sc m i Λ h δ

/-- The raw upper-loop dot commutes with the selected successor source
chart, without a moment hypothesis or a choice of inverse dot. -/
theorem probeOldWeightFollowing_dot :
    ((probeOldActionDot D Sc m i Λ h ▷ probeOldF D Sc m i Λ h).total M) δ ≫
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) =
    eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) ≫
      (R).map (probeAppendToDotComponent D Sc m δ.1.toList i ε.1.toList perm (M δ)) := by
  rw [rightWhisker_total, probeOldWeightFollowing_eqToHom]
  change (R).map ((probeOldActionDot D Sc m i Λ h).total M ε) ≫ _ = _
  rw [probeOldActionDot_via_total D Sc m i Λ h δ ε rfl M]
  simp only [Category.assoc, ← Functor.map_comp,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

end OddMath.QuiverHecke
