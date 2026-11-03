import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedCoordinates

/-! # The selected probe weight cup and cap in mixed coordinates

Brundan–Ellis (1.12): paste the actual weight adjunction maps through
the occupied stored-content coordinates of the prescribed crossing.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u

private theorem unit_transport
    {C A : Type*} [Category* C] [Category* A] (E : C ⥤ A) (F : A ⥤ C) (a : E ⊣ F)
    {P Q : C} {W : A} (hPQ : P = Q) (hWP : W = E.obj P) (hWQ : W = E.obj Q) :
    ((a.unit.app P ≫ F.map (eqToHom hWP.symm)) ≫ F.map (eqToHom hWQ)) =
      eqToHom hPQ ≫ a.unit.app Q := by
  subst Q
  subst W
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem map_counit_transport
    {A E : Type*} [Category* A] [Category* E] (L : A ⥤ E)
    {Y Z T : A} {P Q : E} (hYZ : Y = Z) (hP : P = L.obj Y)
    (hQ : Q = L.obj T) (hPZ : P = L.obj Z) (f : Z ⟶ T) :
    (eqToHom hP ≫ L.map (eqToHom hYZ ≫ f) ≫ eqToHom hQ.symm) ≫ eqToHom hQ =
      eqToHom hPZ ≫ L.map f := by
  subst Z
  subst P
  subst Q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "ν" => Multiset.toList (Subtype.val β)
local notation "νj" => Multiset.toList (Subtype.val δj)
local notation "νi" => Multiset.toList (Subtype.val δi)
local notation "ν₂" => Multiset.toList (Subtype.val ε)
local notation "hj" => probeOldBlockTarget_perm D j Λ h₁ β δj rfl
local notation "hi" => probeOldBlockTarget_perm D i Λ h₃ β δi rfl
local notation "hL" => probeOldBlockTarget_perm D i Λ h₂ δj ε hComm
local notation "hU" => probeOldBlockTarget_perm D j Λ h₄ δi ε rfl
local notation "Fj" => probeOldF D Sc m j Λ h₁
local notation "Ei" => probeOldE D Sc m i Λ h₃
local notation "IndU" => probeOldBlockInd D Sc m j Λ h₄ δi
local notation "ResU" => probeOldBlockRes D Sc m j Λ h₄ δi
local notation "IndL" => probeOldBlockIndTo D Sc m i Λ h₂ δj ε hComm
local notation "sourcePairEq" => probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε rfl
local notation "targetPairEq" => probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hComm

/-- The selected upper cup respects the source and pair coordinates. -/
theorem probeOldWeightMixedUnit_comparison (M : ProbeOldWeightProduct D Sc m Λ xj) :
    probeOldWeightUnitApp D Sc m j Λ h₄ δi ((Ei).obj ((Fj).obj M)) ≫
        (ResU).map (eqToHom (Functor.congr_obj sourcePairEq ((Fj).obj M))) =
      eqToHom (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M) ≫
        (probeAppendToUnit D Sc m νi j ν₂ hU).app
          ((probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj (M δj)) := by
  have h := unit_transport (IndU).toFunctor (ResU).toFunctor (probeOldBlockAdj D Sc m j Λ h₄ δi)
    (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    (Functor.congr_obj sourcePairEq ((Fj).obj M))
  dsimp only [probeOldWeightUnitApp, probeOldBlockAdj, probeAppendToAdjunction] at h ⊢
  exact h

/-- The selected lower cap respects the pair and target coordinates. -/
theorem probeOldWeightMixedCounit_comparison (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldInductionComponent D Sc m i Λ h₂ ε).map
        ((probeOldWeightCounit D Sc m j Λ h₁).app M) ≫
        eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M) =
      eqToHom (Functor.congr_obj targetPairEq ((Fj).obj M)) ≫
        (IndL).map ((probeAppendToCounit D Sc m ν j νj hj).app (M δj)) := by
  have hm := probeOldInductionComponent_map_of D Sc m i Λ h₂ δj ε hComm
    ((probeOldWeightCounit D Sc m j Λ h₁).app M)
  dsimp only [probeOldWeightCounit] at hm
  rw [probeOldWeightCounitComponent_blockSucc] at hm
  have ht := congrArg (fun f => f ≫
    eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)) hm
  have h := map_counit_transport (IndL).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₁ β ((Fj).obj M))
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm
      ((probeOldE D Sc m j Λ h₁).obj ((Fj).obj M)))
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)
    (Functor.congr_obj targetPairEq ((Fj).obj M))
    ((probeOldBlockAdj D Sc m j Λ h₁ β).counit.app (M δj))
  dsimp only [probeOldBlockAdj, probeAppendToAdjunction] at h ht ⊢
  exact ht.trans h

end OddMath.QuiverHecke
