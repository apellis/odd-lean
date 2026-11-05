import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalFields

/-! # The chosen rank-one probe weight mate in stored coordinates

Brundan–Ellis (1.13)–(1.14): the principal entry uses the prescribed
negative equal crossing, the upper unit and the lower counit. Its
occupied coordinate is the same selected stored-target Rouquier mate.
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

private theorem storedMate_expansion
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i : I) {ν₁ ν₂ : List I}
    (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
    (p : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν₁) :
    (probeAppendToMate D Sc m ν i h₁ h₂).app p N =
      (probeAppendToUnit D Sc m ν₁ i ν₂ h₂).app
          ((probeEvaluatedAppendTo D Sc m ν i ν₁ h₁).obj
            ((probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁).obj N)) ≫
        (probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂).map
          ((probeAppendToEqualCross D Sc m ν i h₁ h₂).app p
            ((probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁).obj N)) ≫
        (probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂).map
          ((probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂).map
            ((probeAppendToCounit D Sc m ν i ν₁ h₁).app N)) := by
  unfold probeAppendToMate
  erw [SKM.rouquierMate_piscat_app]
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "A₁" => probeOldActionAdjunction D Sc m i Λ h₁
local notation "A₂" => probeOldActionAdjunction D Sc m i Λ h₂
local notation "Cross" => probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂
local notation "φ" => SKM.rouquierMate A₁ A₂ Cross
local notation "E" => probeOldE D Sc m i Λ h₁
local notation "F" => probeOldF D Sc m i Λ h₁

/-- The prescribed rank-one mate is the same selected cup-crossing-cap. -/
theorem probeOldWeightRouquierMate_eq :
    φ = probeOldWeightMixedMate D Sc m i i Λ h₁ h₂ h₁ h₂ :=
  SKM.rouquierMate_piscat_eq_rectangular A₁ A₂ Cross

theorem probeOldWeightRouquierMate_mem : φ ∈ parity (R := k) _ _ (D.parity i) := by
  rw [probeOldWeightRouquierMate_eq]
  simpa only [SKM.zmod2_mul_self] using
    probeOldWeightMixedMate_mem D Sc m i i Λ h₁ h₂ h₁ h₂

variable (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "ν" => Multiset.toList (Subtype.val β)
local notation "ν₁" => Multiset.toList (Subtype.val δ)
local notation "ν₂" => Multiset.toList (Subtype.val ε)
local notation "hl" => probeOldBlockTarget_perm D i Λ h₁ β (blockSucc D Λ i h₁ β) rfl
local notation "hu" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "Res" => probeOldBlockRes D Sc m i Λ h₂ δ
local notation "Ind" => probeOldBlockInd D Sc m i Λ h₂ δ
local notation "pairEq" => probeOldEFunctor_comp₂_to D Sc m i i Λ h₁ h₂ β ε rfl

/-- Both negative equal crossings are the same whole selected stored map. -/
theorem probeOldBlockEqualCross_stored_eq :
    probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β =
      probeAppendToEqualCross D Sc m ν i hl hu := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  apply InducedCategory.hom_ext
  rw [probeOldBlockEqualCross_total, probeAppendToEqualCross_total]

private theorem cross_comparison (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    (Cross).app p ((F).obj M) ε =
      (eqToHom (Functor.congr_obj pairEq ((F).obj M)) ≫
        (probeAppendToEqualCross D Sc m ν i hl hu).app p (((F).obj M) β)) ≫
        eqToHom (Functor.congr_obj pairEq ((F).obj M)).symm := by
  rw [probeOldActionCross_equal]
  change probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p ((F).obj M) ε = _
  rw [probeOldWeightEqualCrossComponent_of D Sc m i Λ h₁ h₂ p ((F).obj M) β ε rfl,
    probeOldWeightEqualCrossVia_component, probeOldBlockEqualCross_stored_eq]
  simp only [Category.assoc]

/-- Every occupied principal component retains the selected stored mate at every parity. -/
theorem probeOldWeightRouquierMate_comparison (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    (φ).app p M δ ≫
        eqToHom (probeOldWeightMixedTarget_obj D Sc m i i Λ h₁ h₂ h₁ h₂ β M) =
      eqToHom (probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M) ≫
        (probeAppendToMate D Sc m ν i hl hu).app p (M δ) := by
  have hU := probeOldWeightMixedUnit_comparison D Sc m i i Λ h₁ h₁ h₂ β M
  have hX := cross_comparison D Sc m i Λ h₁ h₂ β p M
  have hC := probeOldWeightMixedCounit_comparison D Sc m i i Λ h₁ h₂ h₁ h₂ β M
  have hp := mate_transport (Res).toFunctor
    (probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M)
    (Functor.congr_obj pairEq ((F).obj M))
    (Functor.congr_obj pairEq ((F).obj M))
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)
    (probeOldWeightUnitApp D Sc m i Λ h₂ δ ((E).obj ((F).obj M)))
    ((Cross).app p ((F).obj M) ε)
    ((probeOldInductionComponent D Sc m i Λ h₂ ε).map
      ((probeOldWeightCounit D Sc m i Λ h₁).app M))
    ((probeAppendToUnit D Sc m ν₁ i ν₂ hu).app
      ((probeEvaluatedAppendTo D Sc m ν i ν₁ hl).obj
        ((probeEvaluatedRestrictTo D Sc m ν i ν₁ hl).obj (M δ))))
    ((probeAppendToEqualCross D Sc m ν i hl hu).app p (((F).obj M) β))
    ((Ind).map ((probeAppendToCounit D Sc m ν i ν₁ hl).app (M δ)))
    hU hX hC
  rw [eqToHom_map] at hp
  have hlc := storedMate_expansion D Sc m ν i hl hu p (M δ)
  have hr := congrArg (fun f =>
    eqToHom (probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M) ≫ f) hlc.symm
  have ha := congrArg (fun f => f ≫
    eqToHom (probeOldWeightMixedTarget_obj D Sc m i i Λ h₁ h₂ h₁ h₂ β M))
    (probeOldWeightMixedMate_app_block D Sc m i i Λ h₁ h₂ h₁ h₂ p M δ)
  rw [probeOldWeightRouquierMate_eq]
  exact ha.trans (hp.trans hr)

end OddMath.QuiverHecke
