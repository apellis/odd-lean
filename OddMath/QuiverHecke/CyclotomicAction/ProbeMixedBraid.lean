import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightBraid
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightQuadratic
import OddMath.QuiverHecke.CyclotomicAction.WeightDenominators
import OddMath.QuiverHecke.SwappedAssembly.Sectors
import OddMath.SKM.RouquierFTriangle
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeToReservoirBend
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirToProbeBend
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ProductCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff
import OddMath.QuiverHecke.SwappedAssembly.Sigma.FiniteBendEvaluation

/-!
# Probe mixed braid

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The corrected braid field of the selected probe Rouquier data

Brundan–Ellis (1.9): decode the whole-weight polynomial braid as the
literal dotted Rouquier relation, retaining the chosen induction, crossing
and dot maps and the original scalar coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u v w r
section Decode
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (obj : X → B)
  (E : ∀ (i : I) {x y : X}, x + D.α i = y → (obj x ⟶ obj y))
  (dot : ∀ (i : I) {x y : X} (h : x + D.α i = y), End (E i h))
  (dot_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    dot i h ∈ parity (R := k) _ _ (D.parity i))
  (cross : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    E j h₁ ≫ E i h₂ ⟶ E i h₃ ≫ E j h₄)
  (cross_mem : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    cross i j h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _ (D.parity i * D.parity j))
  (i j : I) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "F₁" => E i hab
local notation "F₂" => E j hbc
local notation "F₃" => E i hcd
local notation "a₀" => E i hab ◁ cross i j hbc hcd hbe hed
local notation "a₁" => Iso.inv (associator (E i hab) (E i hbe) (E j hed)) ≫
  cross i i hab hbe hab hbe ▷ E j hed ≫
  Iso.hom (associator (E i hab) (E i hbe) (E j hed))
local notation "a₂" => E i hab ◁ cross j i hbe hed hbc hcd
local notation "b₀" => Iso.inv (associator (E i hab) (E j hbc) (E i hcd)) ≫
  cross j i hab hbc haf hfc ▷ E i hcd ≫
  Iso.hom (associator (E j haf) (E i hfc) (E i hcd))
local notation "b₁" => E j haf ◁ cross i i hfc hcd hfc hcd
local notation "b₂" => Iso.inv (associator (E j haf) (E i hfc) (E i hcd)) ≫
  cross i j haf hfc hab hbc ▷ E i hcd ≫
  Iso.hom (associator (E i hab) (E j hbc) (E i hcd))

private theorem mixedBraid_of_generators
    (h : a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End (F₁ ≫ F₂ ≫ F₃)) D Sc i j
        (dot i hab ▷ (F₂ ≫ F₃)) (F₁ ◁ (dot j hbc ▷ F₃)) (F₁ ◁ F₂ ◁ dot i hcd)) :
    rouquierMixedBraidEquation D Sc
      { obj := obj, E := E, dot := dot, dot_mem := dot_mem,
        cross := cross, cross_mem := cross_mem } i j hab haf hbc hbe hfc hcd hed := by
  exact rouquierMixedBraidEquation_of_polynomial D Sc _ i j hab haf hbc hbe hfc hcd hed h
end Decode

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "F₀" => probeOldE D Sc' m i Λ hab ≫ probeOldE D Sc' m j Λ hbc ≫ probeOldE D Sc' m i Λ hcd
local notation "a₀" => probeOldWeightCrossSuffix D Sc' m i j i Λ hab hbc hbe hcd hed
local notation "a₁" => probeOldWeightCrossPrefix D Sc' m j i i Λ hab hab hbe hbe hed
local notation "a₂" => probeOldWeightCrossSuffix D Sc' m j i i Λ hab hbe hbc hed hcd
local notation "b₀" => probeOldWeightCrossPrefix D Sc' m i j i Λ hab haf hbc hfc hcd
local notation "b₁" => probeOldWeightCrossSuffix D Sc' m i i j Λ haf hfc hfc hcd hcd
local notation "b₂" => probeOldWeightCrossPrefix D Sc' m i i j Λ haf hab hfc hbc hcd
local notation "x₀" => probeOldWeightTripleFirstDot D Sc' m i j i Λ hab hbc hcd
local notation "x₁" => probeOldWeightTripleMiddleDot D Sc' m i j i Λ hab hbc hcd
local notation "x₂" => probeOldWeightTripleLastDot D Sc' m i j i Λ hab hbc hcd

private theorem probeMixedBraidField_of_polynomial
    (h : a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial D Sc (R := End F₀) i j x₀ x₁ x₂) :
    rouquierMixedBraidEquation D Sc (probeOldRouquierData D Sc' m Λ) i j
      hab haf hbc hbe hfc hcd hed := by
  dsimp only [probeOldWeightCrossPrefix, probeOldWeightCrossSuffix,
    probeOldWeightTripleFirstDot, probeOldWeightTripleMiddleDot,
    probeOldWeightTripleLastDot] at h
  exact mixedBraid_of_generators D Sc
    (probeOldWeightSpace D Sc' m Λ)
    (fun i _ _ h => probeOldE D Sc' m i Λ h)
    (fun i _ _ h => probeOldActionDot D Sc' m i Λ h)
    (fun i _ _ h => probeOldActionDot_mem D Sc' m i Λ h)
    (fun i j _ _ _ _ h₁ h₂ h₃ h₄ => probeOldActionCross D Sc' m Λ i j h₁ h₂ h₃ h₄)
    (fun i j _ _ _ _ h₁ h₂ h₃ h₄ => probeOldActionCross_mem D Sc' m Λ i j h₁ h₂ h₃ h₄)
    i j hab haf hbc hbe hfc hcd hed h

/-- The prescribed probe generators satisfy the literal corrected braid field.
The coefficients are `Sc`; the acting category uses `parameterTwist D Sc`. -/
theorem probeOldRouquierData_braidEq (hne : i ≠ j) :
    rouquierMixedBraidEquation D Sc (probeOldRouquierData D Sc' m Λ) i j
      hab haf hbc hbe hfc hcd hed := by
  exact probeMixedBraidField_of_polynomial D Sc m i j Λ hab haf hbc hbe hfc hcd hed
    (probeOldActionCross_mixedBraid D Sc m i j Λ hab haf hbc hbe hfc hcd hed hne)

end OddMath.QuiverHecke
end

end

section

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
end

end

section

/-! # The multicolour relations of the chosen OLD probe family

Brundan–Ellis Definition 1.5, (1.7)–(1.9), (1.12): assemble all seven
fields for the prescribed scalar-evaluated probe family. The acting
scalar family is parameterTwist Sc; the presentation parameters remain
Sc. No action, local inverse or generator comparison is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u v w r
section Field
variable {k : Type u} [CommRing k] {B : Type v} [BicategoryStruct.{w,r} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (T : SKM.RouquierFamily (k := k) (B := B) D)

/-- Decode the named dotted equation while the family is abstract; the
closed chosen action is substituted only after this conversion. -/
private theorem braidEq_field
    (h : ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
      (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
      (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
      (hed : e + D.α j = d),
      rouquierMixedBraidEquation D Sc T.toRouquierData i j hab haf hbc hbe hfc hcd hed)
: ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
    (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
    (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
    (hed : e + D.α j = d),
    T.E i hab ◁ T.cross i j hbc hcd hbe hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).inv ≫
        T.cross i i hab hbe hab hbe ▷ T.E j hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).hom ≫
        T.E i hab ◁ T.cross j i hbe hed hbc hcd -
      ((associator (T.E i hab) (T.E j hbc) (T.E i hcd)).inv ≫
        T.cross j i hab hbc haf hfc ▷ T.E i hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).hom ≫
        T.E j haf ◁ T.cross i i hfc hcd hfc hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).inv ≫
        T.cross i j haf hfc hab hbc ▷ T.E i hcd ≫
        (associator (T.E i hab) (T.E j hbc) (T.E i hcd)).hom) =
      ∑ s ∈ Finset.range (D.dn i j),
        (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (SKM.rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ SKM.rouquierPower (T.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
        (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (SKM.rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ (SKM.rouquierPower (T.dot j hbc) q ▷ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ SKM.rouquierPower (T.dot i hcd) (p - 1 - s)) := by
  intro i j hij a b c d e f hab haf hbc hbe hfc hcd hed
  exact h i j hij hab haf hbc hbe hfc hcd hed
end Field

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (Λ : X) (hcutoff : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
local notation "Sc'" => parameterTwist D Sc

/-- All multicolour fields hold for the chosen OLD probe family and original parameters. -/
theorem probeOldRouquierMulticolour :
    SKM.RouquierMulticolour (probeOldRouquierFamily D Sc' m Λ hcutoff) Sc := by
  refine {
    quadZero := ?_
    quadNe := ?_
    slideLeft := ?_
    slideRight := ?_
    braid := ?_
    braidEq := ?_
    invNe := ?_ }
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_quadZero D Sc m i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_quadNe D Sc m i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_slideLeft D Sc m i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_slideRight D Sc m i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j l hb a bl bj bi clj cli cji d hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    change rouquierMulticolourBraidEquation D (probeOldRouquierData D Sc' m Λ)
      i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    exact probeOldRouquierData_generalBraid D Sc m i j l Λ
      hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ hb
  · apply braidEq_field D Sc (probeOldRouquierFamily D Sc' m Λ hcutoff)
    intro i j hij a b c d e f hab haf hbc hbe hfc hcd hed
    exact probeOldRouquierData_braidEq D Sc m i j Λ hab haf hbc hbe hfc hcd hed hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_invNe D Sc' m i j Λ h₁ h₂ h₃ h₄ hij

end OddMath.QuiverHecke
end

end

section

/-! # The OLD probe and truncated ELV reservoir

SwappedActionAssembly F1–F2 and Brundan–Ellis Definition 1.5: use the
untruncated scalar-evaluated OLD probe with invertible dots and the
specified truncated ELV reservoir. Both retain their original-weight
actions and presentation parameters. The probe's normalized shifted
left adjunctions are constructed from its complete Rouquier family.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance elvProbeReservoirHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc

/-- The specified asymmetric pair of complete factor families, with their actual highest weights. -/
def elvProbeReservoir : ProbeReservoir k (PiSCat.{u,u,u + 1} k) D Sc where
  T := probeOldRouquierFamily D Sc' m ΛP hP
  W := elvRouquierFamily D Sc' cutoff bound ΛR hR
  leftAdj := (probeOldRouquierFamily D Sc' m ΛP hP).leftAdjoints
  probeRel := probeOldRouquierMulticolour D Sc m ΛP hP
  reservoirRel := elvRouquierMulticolour D Sc cutoff bound ΛR hR
  ΛP := ΛP
  ΛR := ΛR

theorem elvProbeReservoir_W :
    (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).W =
      elvRouquierFamily D Sc' cutoff bound ΛR hR := rfl

/-- The whole chosen probe dot is a unit, as required by the mixed denominators. -/
theorem elvProbeReservoir_dot_isUnit [Fact Sc.PureNilpotent] [Fintype I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsUnit (show End ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).T.E i h) from
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).T.dot i h) :=
  probeOldRouquierFamily_dot_isUnit D Sc' m ΛP hP i h

end OddMath.QuiverHecke
end

end

section

/-! # Output evaluation for the two prescribed mixed bends

`SwappedHomInversion.md` §3 (3)–(6): total evaluation on the full Hom
category, including the parity shifts and the successor block used by
reservoir restriction. These comparisons keep the coefficient carriers
of the bends in `Sigma/ProbeToReservoirBend` and
`Sigma/ReservoirToProbeBend`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction
universe u

local instance bendEvaluationHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

/-- Ordinary total evaluation on a category of superfunctors. -/
def homTotalEvaluation {k C B : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category B] [Preadditive B] [Linear k B] [Supercategory k B] (M : C) :
    Superfunctor k C B ⥤ B where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M

instance {k C B : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category B] [Preadditive B] [Linear k B] [Supercategory k B] (M : C) :
    (homTotalEvaluation (k := k) (B := B) M).Additive where
  map_add := (supernaturalTotalLinearMap _ _ M).map_add _ _

instance {k C B : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category B] [Preadditive B] [Linear k B] [Supercategory k B] (M : C) :
    (homTotalEvaluation (k := k) (B := B) M).Linear k where
  map_smul f r := (supernaturalTotalLinearMap _ _ M).map_smul r f

/-- Evaluation at a probe input and an exact reservoir content block. -/
def homContentEvaluation {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (A : PiSCat.{u,u,u+1} k) (M : A) (δ : WeightBlocks D Λ x) :
    (A ⟶ elvWeightSpace D Sc cutoff bound Λ x) ⥤ ContentModules D Sc cutoff bound δ.1 :=
  homTotalEvaluation M ⋙ Pi.eval _ δ

instance homContentEvaluation_additive {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (A : PiSCat.{u,u,u+1} k) (M : A) (δ : WeightBlocks D Λ x) :
    (homContentEvaluation D Sc cutoff bound Λ x A M δ).Additive where
  map_add := by
    intro F G f g
    exact congrArg (fun a => a δ) ((supernaturalTotalLinearMap F G M).map_add f g)

instance homContentEvaluation_linear {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (A : PiSCat.{u,u,u+1} k) (M : A) (δ : WeightBlocks D Λ x) :
    (homContentEvaluation D Sc cutoff bound Λ x A M δ).Linear k where
  map_smul f r :=
    congrArg (fun a => a δ) ((supernaturalTotalLinearMap _ _ M).map_smul r f)

section Product
variable {k J : Type u} [CommRing k] (C : J → Type (u+1))
  [∀ j, Category.{u} (C j)] [∀ j, Preadditive (C j)]
  [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)] [∀ j, PiSupercategory k (C j)]

/-- Componentwise parity transport of an endomorphism. It is a ring map,
so it preserves finite nilpotence bounds without any bound on the product. -/
def productPiEndEvaluation (M : ∀ j, C j) (j : J) :
    letI := productPiSupercategory (k := k) C
    End (M j) →+* End ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) := by
  let _ := productPiSupercategory (k := k) C
  let e : ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) ≅ M j :=
    { hom := (PiSupercategory.ζ (R := k) M).hom j
      inv := (PiSupercategory.ζ (R := k) M).inv j
      hom_inv_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).hom_inv_id
      inv_hom_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).inv_hom_id }
  exact
    { toFun := fun f => e.hom ≫ twist k 1 f ≫ e.inv
      map_zero' := by
        change e.hom ≫ twist k 1 (0 : End (M j)) ≫ e.inv = 0
        rw [map_zero, Limits.zero_comp, Limits.comp_zero]
      map_one' := by
        change e.hom ≫ twist k 1 (𝟙 (M j)) ≫ e.inv = 𝟙 _
        rw [twist_id, Category.id_comp, Iso.hom_inv_id]
      map_add' := by
        intro f g
        change e.hom ≫ twist k 1 (f + g) ≫ e.inv =
          (e.hom ≫ twist k 1 f ≫ e.inv) + (e.hom ≫ twist k 1 g ≫ e.inv)
        rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
      map_mul' := by
        intro f g
        change e.hom ≫ twist k 1 (g ≫ f) ≫ e.inv =
          (e.hom ≫ twist k 1 g ≫ e.inv) ≫ (e.hom ≫ twist k 1 f ≫ e.inv)
        simp only [twist_comp, Category.assoc, Iso.inv_hom_id_assoc] }

/-- Parity transport at one block depends only on that same block. -/
theorem productPi_map_end_component (M : ∀ j, C j) (f : End M) (j : J) :
    letI := productPiSupercategory (k := k) C
    ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).map f) j =
      productPiEndEvaluation C M j (f j) := by
  let _ := productPiSupercategory (k := k) C
  rw [PiSupercategory.pi_map_eq]
  change (PiSupercategory.ζ (R := k) M).hom j ≫ (twist k 1 f) j ≫
    (PiSupercategory.ζ (R := k) M).inv j =
    (PiSupercategory.ζ (R := k) M).hom j ≫ twist k 1 (f j) ≫
    (PiSupercategory.ζ (R := k) M).inv j
  have ht : (twist k 1 f) j = twist k 1 (f j) :=
    map_twist (R := k) (Pi.eval C j) 1 f
  rw [ht]

end Product

section Components
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (A : PiSCat.{u,u,u+1} k)
local notation "B" => elvWeightSpace D Sc cutoff bound Λ x

/-- A further Hom parity shift preserves a nilpotence bound at the
same reservoir block, including on odd maps. -/
theorem homParityShift_component_isNilpotent (p : ZMod 2) (F : A ⟶ B)
    (f : End F) (M : A) (δ : WeightBlocks D Λ x)
    (hf : IsNilpotent (End.of (f.total M δ))) :
    IsNilpotent (End.of (((SKM.homParityShift (k := k) (C := A ⟶ B) p).map f).total M δ)) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · let Q : ((A ⟶ B) ⥤ (A ⟶ B)) → Prop :=
      fun G => IsNilpotent (End.of ((G.map f).total M δ))
    exact (congrArg Q (SKM.homParityShift_zero (k := k) (C := A ⟶ B))).mpr hf
  · rw [SKM.homParityShift_one]
    let _ := elvWeightPi D Sc cutoff bound Λ x
    change IsNilpotent (End.of
      (((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 0 M)) δ +
       ((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 1 M)) δ))
    rw [productPi_map_end_component, productPi_map_end_component]
    let ψ := productPiEndEvaluation (k := k)
      (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) (F.obj M) δ
    have h := hf.map ψ
    change IsNilpotent (ψ (End.of (f.app 0 M δ) + End.of (f.app 1 M δ))) at h
    exact (ψ.map_add (End.of (f.app 0 M δ)) (End.of (f.app 1 M δ))) ▸ h

end Components

section Restriction
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y) (A : PiSCat.{u,u,u+1} k)
  (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ y) (f : End F)

/-- Reservoir restriction reads precisely the successor of the output
content block. The input probe module remains arbitrary. -/
theorem homPost_elvF_total (M : A) (δ : WeightBlocks D Λ x) :
    (((SKM.homPost (k := k) (elvF D Sc cutoff bound i Λ h)).map f).total M) δ =
      (elvBlockRes D Sc cutoff bound i Λ h δ).map
        ((f.total M) (blockSucc D Λ i h δ)) := by
  change (elvBlockRes D Sc cutoff bound i Λ h δ).map
      (f.app 0 M (blockSucc D Λ i h δ)) +
    (elvBlockRes D Sc cutoff bound i Λ h δ).map
      (f.app 1 M (blockSucc D Λ i h δ)) = _
  rw [← Functor.map_add]
  rfl

/-- Restriction and the prescribed extra parity shift preserve a bound
constructed at the successor content block. -/
theorem shiftedPostRestriction_component_isNilpotent (p : ZMod 2)
    (M : A) (δ : WeightBlocks D Λ x)
    (hf : IsNilpotent (End.of (f.total M (blockSucc D Λ i h δ)))) :
    IsNilpotent
      (End.of (((SKM.homParityShift (k := k) p ⋙ SKM.homPost (k := k)
        (elvF D Sc cutoff bound i Λ h)).map f).total M δ)) := by
  let g := (SKM.homParityShift (k := k) p).map f
  let R := (elvBlockRes D Sc cutoff bound i Λ h δ).toFunctor
  let V := ((SKM.homParityShift (k := k) p).obj F).obj M (blockSucc D Λ i h δ)
  let ψ : End V →*₀ End (R.obj V) :=
    { R.mapEnd V with map_zero' := R.map_zero V V }
  have hg := homParityShift_component_isNilpotent D Sc cutoff bound Λ y A p F f M
    (blockSucc D Λ i h δ) hf
  have hmap := hg.map ψ
  change IsNilpotent (End.of
    (R.map (g.app 0 M (blockSucc D Λ i h δ)) + R.map (g.app 1 M (blockSucc D Λ i h δ))))
  change IsNilpotent (End.of (R.map
    (g.app 0 M (blockSucc D Λ i h δ) + g.app 1 M (blockSucc D Λ i h δ)))) at hmap
  rw [Functor.map_add] at hmap
  exact hmap

end Restriction

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Dot bounds before input evaluation

`SwappedHomInversion.md` §3 (3)–(6): the fixed-content source bound
annihilates the dot uniformly in the input module. Parity shifts,
precomposition and reservoir restriction preserve the same exponent.
No exponent uniform over a weight fibre is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction SwappedAssembly
universe u
local instance outputBoundHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

section Shift
variable (Λ x : X) (A : PiSCat.{u,u,u+1} k)
local notation "Wgt" => elvWeightSpace D Sc cutoff bound Λ x

/-- A parity shift preserves a specified exponent at the same output. -/
theorem homParityShift_component_pow_zero (p : ZMod 2) (F : A ⟶ Wgt)
    (f : End F) (M : A) (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : End.of (f.total M δ) ^ n = 0) :
    End.of (((SKM.homParityShift (k := k) (C := A ⟶ Wgt) p).map f).total M δ) ^ n = 0 := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · let Q : ((A ⟶ Wgt) ⥤ (A ⟶ Wgt)) → Prop :=
      fun G => End.of ((G.map f).total M δ) ^ n = 0
    exact (congrArg Q (SKM.homParityShift_zero (k := k) (C := A ⟶ Wgt))).mpr hf
  · rw [SKM.homParityShift_one]
    let _ := elvWeightPi D Sc cutoff bound Λ x
    change End.of
      (((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 0 M)) δ +
       ((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 1 M)) δ) ^ n = 0
    rw [productPi_map_end_component, productPi_map_end_component]
    let ψ := productPiEndEvaluation (k := k)
      (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) (F.obj M) δ
    have h : ψ (End.of (f.total M δ)) ^ n = 0 := by
      rw [← map_pow, hf, map_zero]
    change ψ (End.of (f.app 0 M δ) + End.of (f.app 1 M δ)) ^ n = 0 at h
    exact (ψ.map_add (End.of (f.app 0 M δ)) (End.of (f.app 1 M δ))) ▸ h

/-- Probe precomposition preserves the exponent and changes only its input. -/
theorem shiftedPrecomposition_component_pow_zero
    (A' : PiSCat.{u,u,u+1} k) (K : A' ⟶ A) (p : ZMod 2)
    (F : A ⟶ Wgt) (f : End F) (M : A') (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : End.of (f.total (K.obj M) δ) ^ n = 0) :
    End.of (((SKM.homPre (k := k) K ⋙ SKM.homParityShift (k := k) p).map f).total M δ) ^ n = 0 := by
  exact homParityShift_component_pow_zero D Sc cutoff bound Λ x A' p
    ((SKM.homPre (k := k) K).obj F) ((SKM.homPre (k := k) K).map f) M δ n hf

/-- A bound uniform in the input annihilates the whole projected map. -/
theorem outputEnd_pow_zero (F : A ⟶ Wgt) (f : End F)
    (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : ∀ M : A, End.of (f.total M δ) ^ n = 0) :
    ((RegularReservoir.evalHomFunctor (k := k)
      (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) A δ).mapEnd F f) ^ n = 0 := by
  apply supernatural_hom_ext_total (k := k) (C := A)
    (B := ContentModules D Sc cutoff bound δ.1)
  intro M
  let L := RegularReservoir.evalHomFunctor (k := k)
    (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) A δ
  change (supernaturalEndEvaluation (k := k) (L.obj F) M) ((L.mapEnd F f) ^ n) =
    (supernaturalEndEvaluation (k := k) (L.obj F) M) 0
  rw [map_pow, map_zero]
  exact hf M
end Shift

section Restriction
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y) (A : PiSCat.{u,u,u+1} k)
  (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ y) (f : End F)

/-- Restriction reads the successor block and preserves its fixed exponent. -/
theorem shiftedPostRestriction_component_pow_zero (p : ZMod 2)
    (M : A) (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : End.of (f.total M (blockSucc D Λ i h δ)) ^ n = 0) :
    End.of (((SKM.homParityShift (k := k) p ⋙ SKM.homPost (k := k)
      (elvF D Sc cutoff bound i Λ h)).map f).total M δ) ^ n = 0 := by
  let g := (SKM.homParityShift (k := k) p).map f
  let R := (elvBlockRes D Sc cutoff bound i Λ h δ).toFunctor
  let V := ((SKM.homParityShift (k := k) p).obj F).obj M (blockSucc D Λ i h δ)
  have hg := homParityShift_component_pow_zero D Sc cutoff bound Λ y A p F f M
    (blockSucc D Λ i h δ) n hf
  have hmap : (R.mapEnd V) (End.of (g.total M (blockSucc D Λ i h δ))) ^ n = 0 := by
    rw [← map_pow, hg, Functor.mapEnd_apply, R.map_zero]
  change End.of (((SKM.homPost (k := k) (elvF D Sc cutoff bound i Λ h)).map g).total M δ) ^ n = 0
  rw [homPost_elvF_total]
  exact hmap
end Restriction

section PostDot
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A : PiSCat.{u,u,u+1} k} (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)

/-- The actual postdot has one exponent for every input at a fixed output. -/
theorem elvPostEndEvaluation_dot_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (δ : WeightBlocks D Λ y) :
    ∃ n : ℕ, 0 < n ∧ ∀ M : A,
      elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ
        (elvPostDot D Sc cutoff bound i Λ h F) ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := elvWeightDotComponent_pow_zero D Sc cutoff bound i Λ h hdot δ
  refine ⟨n, hn, fun M => ?_⟩
  rw [elvPostEndEvaluation_of_mem D Sc cutoff bound i Λ h F M δ _
    (elvPostDot_mem D Sc cutoff bound i Λ h F)]
  exact hp (F.obj M)

/-- The same module-uniform exponent survives the chosen content shift. -/
theorem elvShiftedPostEndEvaluation_dot_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (κ : ZMod 2)
    (δ : WeightBlocks D Λ y) :
    ∃ n : ℕ, 0 < n ∧ ∀ M : A,
      elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F κ M δ
        (elvShiftedPostDot D Sc cutoff bound i Λ h F κ) ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := elvPostEndEvaluation_dot_pow_zero D Sc cutoff bound i Λ h F hdot δ
  refine ⟨n, hn, fun M => ?_⟩
  exact homParityShift_component_pow_zero D Sc cutoff bound Λ y A κ
    (elvPostInduction D Sc cutoff bound i Λ h F) (elvPostDot D Sc cutoff bound i Λ h F) M δ n (hp M)
end PostDot
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The two dots on the OLD-probe and ELV-reservoir Hom summand

SwappedActionAssembly F2–F3: prewhisker the prescribed unit probe dot,
then apply the actual shifted ELV postcomposition. This uses only the
checked generator data, before packaging the full factor pair. Both
mixed denominators are constructed without a whole-weight nilpotence bound.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
local instance mixedDotsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private theorem mixedProbeStep {I X : Type u} [AddCommGroup X]
    (D : SKM.Datum I X) (Λ : X) (β : I →₀ ℕ) (i : I) :
    -(Λ - SwappedAssembly.contentWeight D β) + D.α i =
      -(Λ - SwappedAssembly.contentWeight D (β + Finsupp.single i 1)) := by
  rw [SwappedAssembly.contentWeight_add_single]
  abel

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (i : I) (β : I →₀ ℕ) {x y : X} (h : x + D.α i = y)
variable (Z : probeOldWeightSpace D (parameterTwist D Sc) m ΛP
    (-(ΛP - SwappedAssembly.contentWeight D (β + Finsupp.single i 1))) ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR x)
local notation "Sc'" => parameterTwist D Sc
local notation "w" γ => -(ΛP - SwappedAssembly.contentWeight D γ)

/-- The actual probe raising functor precomposed with the input Hom object. -/
abbrev probeELVMixedBase : probeOldWeightSpace D Sc' m ΛP (w β) ⟶
    elvWeightSpace D Sc' cutoff bound ΛR x := probeOldE D Sc' m i ΛP (mixedProbeStep D ΛP β i) ≫ Z
local notation "F" => probeELVMixedBase (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z)

/-- The original whole probe dot, with its independently chosen input Hom object. -/
abbrev probeELVMixedPreDot : End F :=
  probeOldActionDot D Sc' m i ΛP (mixedProbeStep D ΛP β i) ▷ Z
local notation "α" => probeELVMixedPreDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z)

theorem probeELVMixedPreDot_mem : α ∈ parity (R := k) _ _ (D.parity i) :=
  TwoSupercategory.whiskerRight_mem Z (probeOldActionDot_mem D Sc' m i ΛP (mixedProbeStep D ΛP β i))

/-- The known probe dot unit survives arbitrary Hom precomposition. -/
theorem probeELVMixedPreDot_isUnit [Fact Sc.PureNilpotent] [Finite I] : IsUnit α := by
  let _ := Fintype.ofFinite I
  exact (probeOldActionDot_isUnit D Sc' m i ΛP (mixedProbeStep D ΛP β i)).map
    ((SKM.homPost (k := k) Z).mapEnd (probeOldE D Sc' m i ΛP (mixedProbeStep D ΛP β i)))

/-- The postinduced actual probe map with the specified content parity shift. -/
abbrev probeELVMixedInnerDot (κ : ZMod 2) :=
  elvShiftedPostEnd D Sc' cutoff bound i ΛR h F
    (elvPostProbeDot D Sc' cutoff bound i ΛR h F α) κ

/-- The actual full-ELV postdot with precisely the same content shift. -/
abbrev probeELVMixedOuterDot (κ : ZMod 2) :=
  elvShiftedPostDot D Sc' cutoff bound i ΛR h F κ

/-- The even difference denominator on the literal generator Hom object is a unit. -/
theorem probeELVMixed_difference_isUnit [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
    (κ : ZMod 2) (hi : D.parity i = 0) :
    IsUnit (probeELVMixedOuterDot D Sc m cutoff bound ΛP ΛR i β h Z κ -
      probeELVMixedInnerDot D Sc m cutoff bound ΛP ΛR i β h Z κ) :=
  elvShiftedPostProbe_difference_isUnit D Sc' cutoff bound i ΛR h F hdot κ hi α
    (hi ▸ probeELVMixedPreDot_mem (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))
    (probeELVMixedPreDot_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))

/-- The odd square-difference denominator is also constructed on this same Hom object. -/
theorem probeELVMixed_square_difference_isUnit [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
    (κ : ZMod 2) (hi : D.parity i = 1) :
    IsUnit (probeELVMixedInnerDot D Sc m cutoff bound ΛP ΛR i β h Z κ ^ 2 -
      probeELVMixedOuterDot D Sc m cutoff bound ΛP ΛR i β h Z κ ^ 2) :=
  elvShiftedPostProbe_square_difference_isUnit D Sc' cutoff bound i ΛR h F hdot κ hi α
    (hi ▸ probeELVMixedPreDot_mem (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))
    (probeELVMixedPreDot_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))

end OddMath.QuiverHecke
end

end

section

/-! # Mixed denominator units for the OLD probe and ELV reservoir

SwappedActionAssembly F2–F3 and (A6): identify the actual mixed RP dots
with the prescribed shifted ELV dots, then construct their denominator
units from the whole probe-dot unit and component reservoir bounds.
The constructed coefficient is supernatural by its inverse identities
and these denominator units. No global reservoir nilpotence exponent
is assumed.
-/
noncomputable section
open scoped Classical BigOperators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance probeDenominatorHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

section Mixed
variable (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
  (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
    (nextSector (true, i) true (nextSector (true, i) false t)))
local notation "tR" => nextSector (true, i) false t
local notation "h" => ProbeReservoir.muM_postE (P) i hv
local notation "κ" => SKM.homContentShift D i (Prod.fst t)

/-- The literal probe-precomposition Hom object before reservoir induction. -/
abbrev elvProbeMixedBase : (P).T.obj (-(P).muP tR) ⟶
    elvWeightSpace D Sc' cutoff bound ΛR ((P).muM tR) := ((P).step (true, i) true tR (by trivial)).obj Z
local notation "F" => elvProbeMixedBase D Sc m cutoff bound ΛP ΛR hP hR i t Z

/-- The actual chosen probe dot, whiskered by the input Hom object. -/
abbrev elvProbeMixedPreDot : End F := (P).T.dot i ((P).muP_preE i tR) ▷ Z
local notation "α" => elvProbeMixedPreDot D Sc m cutoff bound ΛP ΛR hP hR i t Z

/-- Total evaluation of the literal mixed carrier at one input and reservoir block. -/
def elvProbeMixedEndEvaluation (M : (P).T.obj (-(P).muP t))
    (δ : WeightBlocks D ΛR ((P).muM t)) :
    End ((P).rpObj i i t hv Z) →ₐ[k] End ((((P).rpObj i i t hv Z).obj M) δ) :=
  elvShiftedPostEndEvaluation D Sc' cutoff bound i ΛR h F κ M δ

/-- The selected outer dot has a constructed bound at this component. -/
theorem elvProbeMixedPostDot_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    IsNilpotent (elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
      ((P).rpPostDot i t hv Z)) :=
  elvShiftedPostEndEvaluation_dot_isNilpotent D Sc' cutoff bound i ΛR h F hdot κ M δ

end Mixed

/-- Both mixed denominators are units on the specified complete factor pair, given
nilpotence of the appended dot for the twisted parameters. -/
theorem elvProbeCrossDenominatorUnitsOf [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) : (P).CrossDenominatorUnits where
  even i hi t hv Z := by
    change IsUnit (probeELVMixedOuterDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1) -
      probeELVMixedInnerDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1))
    exact probeELVMixed_difference_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) hdot (SKM.homContentShift D i t.1) hi
  odd i hi t hv Z := by
    change IsUnit (probeELVMixedInnerDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1) ^ 2 -
      probeELVMixedOuterDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1) ^ 2)
    exact probeELVMixed_square_difference_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) hdot (SKM.homContentShift D i t.1) hi

/-- The coefficient chosen from the constructed mixed denominator units, given nilpotence of
the appended dot for the twisted parameters. The units need the pure coefficients in a
nilpotent ideal; without that, the coefficient is set to zero and no property is claimed. -/
def elvProbeCrossCoeffOf [Finite I] (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    (P).CrossCoeff Sc :=
  if h : Sc.PureNilpotent then
    have : Fact Sc.PureNilpotent := ⟨h⟩
    (P).crossCoeffOfDenominatorUnits
      (elvProbeCrossDenominatorUnitsOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
  else ⟨fun _ _ _ _ => 0⟩

theorem elvProbeCrossCoeffOf_eq [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot =
      (P).crossCoeffOfDenominatorUnits
        (elvProbeCrossDenominatorUnitsOf D Sc m cutoff bound ΛP ΛR hP hR hdot) := by
  unfold elvProbeCrossCoeffOf
  simp only [Fact.out, ↓reduceDIte]

/-- This coefficient has both prescribed even and odd inverse identities. -/
theorem elvProbeCrossCoeffOf_isInverse [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot).IsInverse := by
  rw [elvProbeCrossCoeffOf_eq]
  exact (P).crossCoeffOfDenominatorUnits_isInverse _

/-- This coefficient is supernatural at its prescribed parity. -/
theorem elvProbeCrossCoeffOf_isSupernatural [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot).IsSupernatural :=
  ProbeReservoir.CrossCoeff.isSupernatural_of_isInverse (P)
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot)
    (elvProbeCrossDenominatorUnitsOf D Sc m cutoff bound ΛP ΛR hP hR hdot)

end OddMath.QuiverHecke
end

end

section

/-! # Component bounds in the prescribed ELV mixed bends

`SwappedHomInversion.md` §3 (3)–(6): the same selected crossing
coefficient enters both mixed bends. Its output bounds are constructed
at the source content read by the chosen lowering functor. In
particular, restriction uses the successor reservoir block; probe
precomposition uses the transformed probe input. No bound on a whole
weight fibre is required.
-/
noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance finiteBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "Sc'" => parameterTwist D Sc

private theorem evaluated_conjugation_isNilpotent
    {C E : Type*} [Category C] [Preadditive C] [Category E] [Preadditive E]
    (L : C ⥤ E) [L.Additive] {A B : C} (e : A ≅ B) (f : End A)
    (hf : IsNilpotent ((L.mapEnd A) f)) :
    IsNilpotent ((L.mapEnd B) (bendConjugation e f)) := by
  have h := hf.map (bendConjugation (L.mapIso e))
  change IsNilpotent (End.of (L.map e.inv ≫ L.map f ≫ L.map e.hom)) at h
  change IsNilpotent (End.of (L.map (e.inv ≫ f ≫ e.hom)))
  simpa only [Functor.map_comp] using h

/-- Literal output evaluation with the complete factor Hom category as
its declared domain, retaining its chosen preadditive structure. -/
def elvProbeBendOutputEvaluation (t : Sector I)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤
      ContentModules D Sc' cutoff bound δ.1 :=
  homContentEvaluation D Sc' cutoff bound ΛR ((P).muM t)
    ((P).T.obj (-(P).muP t)) M δ

instance elvProbeBendOutputEvaluation_additive (t : Sector I)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    (elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hP hR t M δ).Additive where
  map_add := by
    intro F G f g
    exact congrArg (fun a => a δ) ((supernaturalTotalLinearMap F G M).map_add f g)

local notation "out" "[" t "," M "," δ "]" =>
  elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hP hR t M δ

private theorem probeToReservoirInnerStepValid (i : I) (t : Sector I) :
    StepValid (true, i) false (nextSector (false, i) false t) := by
  simp [StepValid, nextSector]

section ProbeToReservoir
local notation "dFP" "[" i "," t "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preE i t)
local notation "dFR" "[" i "," t "]" =>
  SKM.homContentPostF (P).T.obj (P).W i (Prod.fst t) ((P).muP t) ((P).muM_postF i t)
local notation "ds" "[" i "," t "]" => nextSector (false, i) false t
local notation "dh" "[" i "," t "]" =>
  (probeToReservoirInnerStepValid i t)
local notation "dU" "[" i "," t "," Z "]" =>
  ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ (dFP[i,t]).obj Z)
local notation "dφ" "[" i "," t "," Z "," M "," δ "]" =>
  probeToReservoirBendCoefficientEvaluation (P) i t Z (out[t,M,δ])

/-- The XP-to-YR bend reads a constructed bound at the successor of its
literal output block. The probe input and Hom object are arbitrary. -/
theorem elvProbeDxOuterDot_isNilpotent [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) :
    IsNilpotent (dφ[i,t,Z,M,δ] ((P).rpPostDot i ds[i,t] dh[i,t] dU[i,t,Z])) := by
  let J := (dFR[i,t]) ⋙ out[t,M,δ]
  let y := (P).rpPostDot i ds[i,t] dh[i,t] dU[i,t,Z]
  have hy : IsNilpotent ((J.mapEnd _) y) := by
    change IsNilpotent (End.of (((dFR[i,t]).map y).total M δ))
    exact shiftedPostRestriction_component_isNilpotent D Sc' cutoff bound i ΛR
      ((P).muM_postF i t) ((P).T.obj (-(P).muP t)) ((P).rpObj i i ds[i,t] dh[i,t] dU[i,t,Z]) y
      (SKM.homContentShift D i t.1) M δ
      (elvProbeMixedPostDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i ds[i,t] dh[i,t] dU[i,t,Z] hdot M
        (blockSucc D ΛR i ((P).muM_postF i t) δ))
  exact evaluated_conjugation_isNilpotent J
    ((P).probeToReservoirCoefficientIso i t ((dFP[i,t]).obj Z)) y hy

end ProbeToReservoir

section ReservoirToProbe
local notation "cFP" "[" i "," t "," hb "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preF i hb)
local notation "cFR" "[" i "," t "," hv "]" =>
  SKM.homContentPostF (P).T.obj (P).W i (Prod.fst t) ((P).muP t) ((P).muM_postE i hv)
local notation "cs" "[" i "," t "]" => nextSector (false, i) true t
local notation "cU" "[" i "," t "," hb "," hv "," Z "]" =>
  ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ (cFR[i,t,hv]).obj Z)
local notation "cφ" "[" i "," t "," hb "," hv "," Z "," M "," δ "]" =>
  reservoirToProbeBendCoefficientEvaluation (P) i t hb hv Z (out[t,M,δ])

end ReservoirToProbe
end OddMath.QuiverHecke
end

end
