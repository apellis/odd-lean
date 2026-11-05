import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMateComparison
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # Invertibility of the distinct OLD probe weight mate

Brundan–Ellis (1.12): paste the prescribed unit, positive distinct crossing
and counit through their occupied stored-content coordinates. The same
local inverse gives the global inverse; absent coordinates vanish.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
private theorem mate_transport
    {A B : Type*} [Category* A] [Category* B] (R : A ⥤ B)
    {P Q : B} {S T V S' T' V' : A}
    (hP : P = Q) (hS : S = S') (hT : T = T') (hV : V = V')
    (η : P ⟶ R.obj S) (χ : S ⟶ T) (ε : T ⟶ V)
    (η' : Q ⟶ R.obj S') (χ' : S' ⟶ T') (ε' : T' ⟶ V')
    (hu : η ≫ R.map (eqToHom hS) = eqToHom hP ≫ η')
    (hx : χ = (eqToHom hS ≫ χ') ≫ eqToHom hT.symm)
    (hc : ε ≫ eqToHom hV = eqToHom hT ≫ ε') :
    ((η ≫ R.map χ) ≫ R.map ε) ≫ R.map (eqToHom hV) =
      eqToHom hP ≫ (η' ≫ R.map χ' ≫ R.map ε') := by
  subst Q
  subst S'
  subst T'
  subst V'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu hx hc ⊢
  rw [hu, hx, hc]
  exact Category.assoc _ _ _

private theorem isIso_of_homogeneous_components
    {k C B : Type*} [CommRing k] [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) F G p) (hi : ∀ M, IsIso (f.app p M)) : IsIso f := by
  let e : ∀ M, F.obj M ≅ G.obj M := fun M => by
    let : IsIso (f.app p M) := hi M
    exact asIso (f.app p M)
  have he (M) : (e M).hom = f.total M :=
    (HomogeneousSuperfunctorIso.total_eq_app f hf M).symm
  rw [← HomogeneousSuperfunctorIso.ofHom_hom f hf e he]
  infer_instance

private theorem storedMate_expansion
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i j : I) {νj νi ν₂ : List I}
    (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
    (hL : (i :: νj).Perm ν₂) (hU : (j :: νi).Perm ν₂)
    (p : ZMod 2) (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMate D Sc m ν i j hj hi hL hU).app p N =
      (probeAppendToUnit D Sc m νi j ν₂ hU).app
          ((probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj N) ≫
        (probeEvaluatedRestrictTo D Sc m νi j ν₂ hU).map
          ((probeAppendToCross D Sc m ν i j hj hi hL hU).app p
            ((probeEvaluatedRestrictTo D Sc m ν j νj hj).obj N)) ≫
        (probeEvaluatedRestrictTo D Sc m νi j ν₂ hU).map
          ((probeEvaluatedAppendTo D Sc m νj i ν₂ hL).map
            ((probeAppendToCounit D Sc m ν j νj hj).app N)) := by
  let J := oldContentAppendTo D Sc (probeCutoff D m) ν j νj hj
  let K := oldContentAppendTo D Sc (probeCutoff D m) ν i νi hi
  let L := oldContentAppendTo D Sc (probeCutoff D m) νj i ν₂ hL
  let U := oldContentAppendTo D Sc (probeCutoff D m) νi j ν₂ hU
  let hc := oldAppendToCross_supernatural D Sc (probeCutoff D m) ν i j hj hi hL hU
  apply InducedCategory.hom_ext
  change (rectangularMateHom J K L U hc).app p N.obj =
    (adjunctionUnit U).app (induced K ((restriction J).obj N.obj)) ≫
      (restriction U).map ((rectangularCrossComponent_supernatural J K L U hc).toSuperNatTrans.app p
        ((restriction J).obj N.obj)) ≫
      (restriction U).map ((induction L).map ((adjunctionCounit J).app N.obj))
  by_cases hp : p = D.parity i * D.parity j
  · subst p
    rw [rectangularMateHom, IsSupernatural.toSuperNatTrans_app, IsSupernatural.toSuperNatTrans_app]
    rfl
  · simp only [rectangularMateHom, IsSupernatural.toSuperNatTrans, hp, ite_false,
      Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

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
local notation "Cross" => probeOldActionCross D Sc m Λ j i h₃ h₄ h₁ h₂
local notation "LocalCross" => probeAppendToCross D Sc m ν i j hj hi hL hU
local notation "LocalMate" => probeAppendToDistinctMate D Sc m ν i j hj hi hL hU
local notation "LocalSource" => probeAppendToDistinctMateSource D Sc m ν i j hj hi

/-- The prescribed weight mate is the same local mate on every occupied block. -/
theorem probeOldWeightMixedMate_comparison (hij : i ≠ j) (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app p M δi ≫
        eqToHom (probeOldWeightMixedTarget_obj D Sc m i j Λ h₁ h₂ h₃ h₄ β M) =
      eqToHom (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M) ≫
        (LocalMate).app p (M δj) := by
  have hu := probeOldWeightMixedUnit_comparison D Sc m i j Λ h₁ h₃ h₄ β M
  have hx := probeOldWeightMixedCross_comparison D Sc m i j Λ h₁ h₂ h₃ h₄ β hij p M
  have hc := probeOldWeightMixedCounit_comparison D Sc m i j Λ h₁ h₂ h₃ h₄ β M
  have hp := mate_transport (ResU).toFunctor
    (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M)
    (Functor.congr_obj sourcePairEq ((Fj).obj M))
    (Functor.congr_obj targetPairEq ((Fj).obj M))
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)
    (probeOldWeightUnitApp D Sc m j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    ((Cross).app p ((Fj).obj M) ε)
    ((probeOldInductionComponent D Sc m i Λ h₂ ε).map
      ((probeOldWeightCounit D Sc m j Λ h₁).app M))
    ((probeAppendToUnit D Sc m νi j ν₂ hU).app ((LocalSource).obj (M δj)))
    ((LocalCross).app p (((Fj).obj M) β))
    ((IndL).map ((probeAppendToCounit D Sc m ν j νj hj).app (M δj)))
    hu hx hc
  rw [eqToHom_map] at hp
  have hl := storedMate_expansion D Sc m ν i j hj hi hL hU p (M δj)
  have hr := congrArg (fun f =>
    eqToHom (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M) ≫ f) hl.symm

  have ha := congrArg (fun f => f ≫
    eqToHom (probeOldWeightMixedTarget_obj D Sc m i j Λ h₁ h₂ h₃ h₄ β M))
    (probeOldWeightMixedMate_app_block D Sc m i j Λ h₁ h₂ h₃ h₄ p M δi)
  exact ha.trans (hp.trans hr)

/-- The chosen mixed map has the stored-target inverse on an occupied block. -/
theorem probeOldWeightMixedMate_supported_isIso (hij : i ≠ j)
    (M : ProbeOldWeightProduct D Sc m Λ xj) :
    IsIso ((probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M δi) := by
  have he := probeAppendToDistinctMateModuleIso_hom D Sc m ν i j hj hi hL hU hij (M δj)
  have ht := HomogeneousSuperfunctorIso.total_eq_app (LocalMate)
    (probeAppendToDistinctMate_mem D Sc m ν i j hj hi hL hU) (M δj)
  let : IsIso ((LocalMate).app (D.parity i * D.parity j) (M δj)) := by
    rw [← ht, ← he]
    infer_instance
  let : IsIso ((probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M δi ≫
      eqToHom (probeOldWeightMixedTarget_obj D Sc m i j Λ h₁ h₂ h₃ h₄ β M)) := by
    rw [probeOldWeightMixedMate_comparison D Sc m i j Λ h₁ h₂ h₃ h₄ β hij]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (eqToHom (probeOldWeightMixedTarget_obj D Sc m i j Λ h₁ h₂ h₃ h₄ β M))

/-- Occupied and absent coordinates exhaust the output weight product. -/
theorem probeOldWeightMixedMate_coordinate_isIso (hij : i ≠ j)
    (M : ProbeOldWeightProduct D Sc m Λ xj) (δ : WeightBlocks D Λ xi) :
    IsIso ((probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M δ) := by
  by_cases hδ : ∃ β, blockSucc D Λ i h₃ β = δ
  · obtain ⟨β, rfl⟩ := hδ
    exact probeOldWeightMixedMate_supported_isIso D Sc m i j Λ h₁ h₂ h₃ h₄ β hij M
  · exact probeOldWeightMixedMate_absent_isIso D Sc m i j Λ h₁ h₂ h₃ h₄ hij δ hδ
      (D.parity i * D.parity j) M

/-- The whole product-module component retains the inverse of its selected map. -/
theorem probeOldWeightMixedMate_component_isIso (hij : i ≠ j)
    (M : ProbeOldWeightProduct D Sc m Λ xj) :
    IsIso ((probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M) :=
  (isIso_pi_iff _).mpr (probeOldWeightMixedMate_coordinate_isIso D Sc m i j Λ h₁ h₂ h₃ h₄ hij M)

/-- BE (1.12): the selected distinct probe weight cup-crossing-cap is invertible. -/
theorem probeOldWeightMixedMate_isIso (hij : i ≠ j) :
    IsIso (probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄) :=
  isIso_of_homogeneous_components _ (probeOldWeightMixedMate_mem D Sc m i j Λ h₁ h₂ h₃ h₄)
    (probeOldWeightMixedMate_component_isIso D Sc m i j Λ h₁ h₂ h₃ h₄ hij)

/-- The presentation mate uses the same chosen global adjunction maps. -/
theorem probeOldActionCrossMate_eq :
    SKM.crossMate
      (E₃ := probeOldE D Sc m j Λ h₁) (E₄ := probeOldE D Sc m j Λ h₄)
      (probeOldActionAdjunction D Sc m i Λ h₃) (probeOldActionAdjunction D Sc m i Λ h₂)
      (probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄) =
      probeOldWeightMixedMate D Sc m j i Λ h₃ h₄ h₁ h₂ :=
  SKM.crossMate_piscat_eq_rectangular _ _ _ _ _

/-- The exact distinct-colour inversion map of the chosen probe generators. -/
theorem probeOldActionCrossMate_isIso (hij : i ≠ j) :
    IsIso (SKM.crossMate
      (E₃ := probeOldE D Sc m j Λ h₁) (E₄ := probeOldE D Sc m j Λ h₄)
      (probeOldActionAdjunction D Sc m i Λ h₃) (probeOldActionAdjunction D Sc m i Λ h₂)
      (probeOldActionCross D Sc m Λ i j h₁ h₂ h₃ h₄)) := by
  rw [probeOldActionCrossMate_eq]
  exact probeOldWeightMixedMate_isIso D Sc m j i Λ h₃ h₄ h₁ h₂ hij.symm

/-- The `invNe` conclusion for the bundled chosen probe Rouquier data. -/
theorem probeOldRouquierData_invNe (hij : i ≠ j) :
    IsIso (SKM.crossMate
      (E₃ := (probeOldRouquierData D Sc m Λ).E j h₁)
      (E₄ := (probeOldRouquierData D Sc m Λ).E j h₄)
      (probeOldRouquierDataAdjunction D Sc m Λ i h₃)
      (probeOldRouquierDataAdjunction D Sc m Λ i h₂)
      ((probeOldRouquierData D Sc m Λ).cross i j h₁ h₂ h₃ h₄)) :=
  probeOldActionCrossMate_isIso D Sc m i j Λ h₁ h₂ h₃ h₄ hij

end OddMath.QuiverHecke
