import OddMath.QuiverHecke.CyclotomicAction.DistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockMatrix
import OddMath.SKM.RouquierHomPostInverse
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.CategoryGrading
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight

/-!
# Content triple

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The OLD correction in the three prescribed append dots

Brundan–Ellis (1.9): identify the full untruncated OLD coefficient braid
correction with the polynomial in three independent positional dots.
Its original-parameter ordered induction operator is retained on every
module. No source braid, polynomial-naturality or comparison premise is
introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction Distinct
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local notation "A" i => append D Sc cutoff i

/-- The first dot, independently appended twice to the three-letter source. -/
def tripleFirstDot (i j : I) (s : OldCategory D Sc cutoff) : End ((tripleAppend D Sc cutoff i j i).obj s) :=
  (A i).map (pairFirstDot D Sc cutoff i j s)

/-- The middle dot, appended once to the three-letter source. -/
def tripleMiddleDot (i j : I) (s : OldCategory D Sc cutoff) : End ((tripleAppend D Sc cutoff i j i).obj s) :=
  (A i).map (pairSecondDot D Sc cutoff i j s)

/-- The last independent moving dot in the same source endomorphism algebra. -/
def tripleLastDot (i j : I) (s : OldCategory D Sc cutoff) : End ((tripleAppend D Sc cutoff i j i).obj s) :=
  oldAppendDotComponent D Sc cutoff i (((A i) ⋙ (A j)).obj s)

theorem tripleFirstDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    tripleFirstDot D Sc cutoff i j s = oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s)
      (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) s.word.length) := by
  rw [tripleFirstDot, pairFirstDot_affine]
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [i] (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
    (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length ▷ (pres D Sc).obj (ob D [i]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i] ++ [j]) [i] s.word.length (by simp)]
  rfl

theorem tripleMiddleDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    tripleMiddleDot D Sc cutoff i j s = oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s)
      (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) (s.word.length + 1)) := by
  rw [tripleMiddleDot, pairSecondDot_affine]
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [i] (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1)))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
    (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1) ▷ (pres D Sc).obj (ob D [i]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i] ++ [j]) [i] (s.word.length + 1) (by simp)]
  rfl

theorem tripleLastDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    tripleLastDot D Sc cutoff i j s = oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s)
      (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) (s.word.length + 2)) := by
  rw [tripleLastDot, oldAppendDotComponent_eq, appendMovingPower, pow_one]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
    (dotE D Sc (s.word ++ [i] ++ [j] ++ [i]) (s.word ++ [i] ++ [j]).length)) = _
  simp only [List.length_append, List.length_singleton, Nat.add_assoc]
  rfl

/-- The coefficient correction is exactly the polynomial of the three chosen OLD dots. -/
theorem tripleCorrection_tripleDots (i j : I) (s : OldCategory D Sc cutoff) :
    tripleCorrection D Sc cutoff i j s =
      tripleDotCorrectionPolynomial D Sc i j
        (tripleLastDot D Sc cutoff i j s) (tripleMiddleDot D Sc cutoff i j s)
        (tripleFirstDot D Sc cutoff i j s) := by
  rw [tripleLastDot_affine, tripleMiddleDot_affine, tripleFirstDot_affine,
    ← tripleDotCorrectionPolynomial_map]
  change oldAffineEndAlgHom D Sc cutoff ((tripleAppend D Sc cutoff i j i).obj s) (coefficientCorrection D Sc s.word i j) = _
  congr 1
  simp only [coefficientCorrection, positionalCorrection, tripleDotCorrectionPolynomial,
    tripleDotCorrectionSum, pow_zero, mul_one]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Unit inversion on content with no lower predecessor

BE (1.14): the zero principal source and the ordinary upper unit columns
retain the constructed weighted inverse. The following F/E object is
kept and is not declared zero from the absence of the moving colour.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I) (hi : i ∉ β)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "U" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sq" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
variable (M : ContentModules D Sc cutoff N β)
local notation "P" => induced (contentInclusion D Sc cutoff N β) M
local notation "FE" => Functor.obj (restriction (truncatedAppend D Sc cutoff N [i]))
  (induced (truncatedAppend D Sc cutoff N [i]) (induced (contentInclusion D Sc cutoff N β) M))
local notation "Target" => fullSquareTargetRetargetIso K U Q T sq M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M

include hi in
/-- The prescribed unit columns on an absent-colour content have all local
inverse identities, with their zero principal source and exact finite count. -/
theorem contentAbsentUnitInverse_nonempty :
    Nonempty (SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M))
      (unitDotColumn K hDot M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i β)) := by
  refine ⟨?_⟩
  have hh := contentCrossingHeight_nonneg_of_not_mem D cutoff β.toList i
    (by simpa only [Multiset.mem_toList] using hi)
  rw [Multiset.coe_toList] at hh
  let J := weightedContentLocalInverseFrom D Sc cutoff N i P β hh
  let a := Target
  let c := Value
  have h0 := elvZeroModule_isZero D Sc cutoff N β
  have hGlobal := truncatedIndRes_restriction_isZero D Sc cutoff N i β hi P
  let b := h0.iso hGlobal
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [h0.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 (ContentModules D Sc cutoff N β)) a b c
    (contentUnitTargetIso_hom_mem D Sc cutoff N β i M) hb
    (contentUnitValueIso_hom_mem D Sc cutoff N β M)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N β)).map
      ((restriction Q).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M)) :=
    h0.eq_of_src _ _
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N β)).map
      ((restriction Q).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDot M n := by
    have hu := contentUnitDotColumn_square D Sc cutoff N β i M n
    change unitDotColumn K hDot M n ≫ a.hom =
      c.hom ≫ (restriction Q).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n) at hu
    have he := congrArg (fun f => f ≫ a.inv) hu
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  simpa only [hf, hg] using H

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Whiskering of crossings on three content induction functors -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K K' : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
variable (L L' : C ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  [L'.Additive] [L'.Linear k] [IsSuperfunctor k L']

/-- Outer whiskering with independently recast source and target functors. -/
theorem compForward_outer_arrow_recast (e : J ⋙ K = L) (e' : J ⋙ K' = L')
    {p : ZMod 2} {a : ∀ w, K.obj w ⟶ K'.obj w} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L'.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (a (J.obj v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    (moduleIsoLinearEquiv ((inductionCompOfEq J K L e).app M) z).toLinearMap ∘ₗ
        transformLinear ha (induced J M) z =
      transformLinear hb M z ∘ₗ
        (moduleIsoLinearEquiv ((inductionCompOfEq J K' L' e').app M) z).toLinearMap := by
  subst L
  subst L'
  have hab' : (fun v => a (J.obj v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_outer J ha M z
/-- Recast both ends of inner whiskering without identifying the append words. -/
theorem compForward_inner_arrow_recast
    (J' : C ⥤ D) [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
    (e : J ⋙ K = L) (e' : J' ⋙ K = L')
    {p : ZMod 2} {a : ∀ v, J.obj v ⟶ J'.obj v} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L'.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (K.map (a v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    (moduleIsoLinearEquiv ((inductionCompOfEq J K L e).app M) z).toLinearMap ∘ₗ
        mapComponent K (transformComponent ha M) p z =
      transformLinear hb M z ∘ₗ
        (moduleIsoLinearEquiv ((inductionCompOfEq J' K L' e').app M) z).toLinearMap := by
  subst L
  subst L'
  have hab' : (fun v => K.map (a v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_inner K ha M z
end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
open MonoidalCategory
open scoped TensorProduct
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem arrowRecast_map_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

theorem appendComponent_leftContext_arrow_heq (v σ τ τ' : List I)
    (a : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D τ')) :
    HEq (truncatedAppendComponent D Sc cutoff N a ⟨v ++ σ⟩)
      (truncatedAppendComponent D Sc cutoff N
        ((pres D Sc).obj (ob D σ) ◁ a) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) (𝟙 ((pres D Sc).obj (ob D σ))) a
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq ((pres D Sc).obj (ob D (v ++ σ)) ◁ a)
      ((pres D Sc).obj (ob D v) ◁ ((pres D Sc).obj (ob D σ) ◁ a)) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ'))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact arrowRecast_map_heq
    (i := ((v ++ σ) ++ τ, (v ++ σ) ++ τ')) (j := (v ++ (σ ++ τ), v ++ (σ ++ τ')))
    (A := fun w : List I × List I => (pres D Sc).obj (ob D w.1) ⟶ (pres D Sc).obj (ob D w.2))
    (B := fun w : List I × List I => TruncatedOld D Sc cutoff N w.1 w.2)
    (fun w f => (truncatedIdeal D Sc cutoff N w.1 w.2).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (Prod.ext (List.append_assoc v σ τ) (List.append_assoc v σ τ')) hh

/-- Nonendomorphism outer source comparison, retaining both endpoint casts. -/
theorem contentInductionComp_outer_arrow (β : Multiset I) (σ τ τ' : List I)
    (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (ht : (β + (σ : Multiset I)) + (τ' : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (ht' : β + ((σ ++ τ' : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D τ')}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h ht ha)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ _ rfl) M) z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' ht'
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ' γ ht ht').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_outer_arrow_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ' γ ht)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppendTo D Sc cutoff N β (σ ++ τ') γ ht')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ' γ ht ht')
    (contentAppendTo_supernatural D Sc cutoff N h ht ha)
    (contentAppendTo_supernatural D Sc cutoff N h' ht'
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha))
    (fun v => appendComponent_leftContext_arrow_heq D Sc cutoff N v.obj.word σ τ τ' a) M z

theorem appendComponent_rightContext_arrow_heq (v σ σ' τ : List I)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')) :
    HEq (truncatedRightContext D Sc cutoff N τ (v ++ σ) (v ++ σ')
      (truncatedAppendComponent D Sc cutoff N a ⟨v⟩))
      (truncatedAppendComponent D Sc cutoff N
        (a ▷ (pres D Sc).obj (ob D τ)) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) a (𝟙 ((pres D Sc).obj (ob D τ)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq (((pres D Sc).obj (ob D v) ◁ a) ▷ (pres D Sc).obj (ob D τ))
      ((pres D Sc).obj (ob D v) ◁ (a ▷ (pres D Sc).obj (ob D τ))) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ' τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact arrowRecast_map_heq
    (i := ((v ++ σ) ++ τ, (v ++ σ') ++ τ)) (j := (v ++ (σ ++ τ), v ++ (σ' ++ τ)))
    (A := fun w : List I × List I => (pres D Sc).obj (ob D w.1) ⟶ (pres D Sc).obj (ob D w.2))
    (B := fun w : List I × List I => TruncatedOld D Sc cutoff N w.1 w.2)
    (fun w f => (truncatedIdeal D Sc cutoff N w.1 w.2).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (Prod.ext (List.append_assoc v σ τ) (List.append_assoc v σ' τ)) hh

/-- Inner nonendomorphism whiskering at an explicit common intermediate content. -/
theorem contentInductionCompTo_inner_arrow (β : Multiset I) (σ σ' : List I)
    (δ : Multiset I) (hδ : β + (σ : Multiset I) = δ) (hδ' : β + (σ' : Multiset I) = δ)
    (τ : List I) (γ : Multiset I) (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (h' : β + ((σ' ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h).app M) z).toLinearMap ∘ₗ
      BalancedInduction.mapComponent (contentAppendTo D Sc cutoff N δ τ γ hγ)
        (BalancedInduction.transformComponent
          (contentAppendTo_supernatural D Sc cutoff N hδ hδ' ha) M) p z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h h'
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h').app M) z).toLinearMap := by
  rw [contentInductionCompTo_eq, contentInductionCompTo_eq]
  exact BalancedInduction.compForward_inner_arrow_recast
    (contentAppendTo D Sc cutoff N β σ δ hδ)
    (contentAppendTo D Sc cutoff N δ τ γ hγ)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h)
    (contentAppendTo D Sc cutoff N β (σ' ++ τ) γ h')
    (contentAppendTo D Sc cutoff N β σ' δ hδ')
    (contentAppend_compTo_eq D Sc cutoff N β σ δ hδ τ γ hγ h)
    (contentAppend_compTo_eq D Sc cutoff N β σ' δ hδ' τ γ hγ h')
    (contentAppendTo_supernatural D Sc cutoff N hδ hδ' ha)
    (contentAppendTo_supernatural D Sc cutoff N h h'
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha))
    (fun v => appendComponent_rightContext_arrow_heq D Sc cutoff N v.obj.word σ σ' τ a) M z

private def compIsoApp {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E) (e : J ⋙ K ≅ L) (M : C) :
    K.obj (J.obj M) ≅ L.obj M := e.app M

private theorem compIsoApp_hom_mem
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E) (e : J ⋙ K ≅ L) (M : C)
    {p : ZMod 2} (he : e.hom.app M ∈ parity (R := k) _ _ p) :
    (compIsoApp J K L e M).hom ∈ parity (R := k) _ _ p := he

private theorem total_of_mem
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

private theorem map_transform_total
    {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {F G : Superfunctor k C (SVec k)} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : B) :
    ((BalancedInduction.induction J).map f).total z = BalancedInduction.mapComponent J f p z :=
  total_of_mem (Supercategory.map_mem (BalancedInduction.induction J) hf) z

theorem contentTripleLeft_whisker (i j l : I) :
    contentTripleLeft D Sc i j l = crossTwo D Sc i j ▷ (pres D Sc).obj (ob D [l]) := by
  rw [crossTwo, cl_whiskerRight D Sc _ _ [l]
    (by intro g hg; simp only [List.mem_singleton] at hg; subst g; simp [PG.pos, PG.width])]
  rfl

/-- The normalized prefix source on the canonical three-letter objects. -/
def contentTriplePrefixAffine (i j l : I) :
    (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [j,i,l]) := by
  classical
  exact if i = j then -contentTripleLeft D Sc i j l else contentTripleLeft D Sc i j l

theorem contentTriplePrefixAffine_mem (i j l : I) :
    contentTriplePrefixAffine D Sc i j l ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  classical
  unfold contentTriplePrefixAffine
  split_ifs
  · exact Submodule.neg_mem _ (contentTripleLeft_parity D Sc i j l)
  · exact contentTripleLeft_parity D Sc i j l

theorem contentTriplePrefixAffine_eq_whisker (i j l : I) :
    contentTriplePrefixAffine D Sc i j l =
      contentCrossAffine D Sc i j ▷ (pres D Sc).obj (ob D [l]) := by
  classical
  by_cases hij : i = j
  · simp only [contentTriplePrefixAffine, contentCrossAffine, ite_eq_left hij,
      MonoidalSupercategory.neg_whiskerRight (R := k), contentTripleLeft_whisker]
  · simp only [contentTriplePrefixAffine, contentCrossAffine, ite_eq_right hij,
      contentTripleLeft_whisker]

private theorem homogeneous_total_ext
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f g : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p)
    (h : ∀ z, f.total z = g.total z) : f = g := by
  apply SuperNatTrans.ext
  funext q z
  by_cases hq : q = p
  · subst q
    rw [← total_of_mem hf, ← total_of_mem hg]
    exact h z
  · rw [Superfunctor.app_eq_zero_of_mem hf hq,
      Superfunctor.app_eq_zero_of_mem hg hq]

private theorem contentInductionTransform_app
    {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) (M : ContentModules D Sc cutoff N β) :
    (contentInductionTransform D Sc cutoff N hσ hτ ha).app p M =
      BalancedInduction.transformComponent (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M :=
  congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha))) M

/-- Inner-arrow comparison before evaluating the target module. -/
theorem contentInductionCompTo_inner_map (β : Multiset I) (σ σ' : List I)
    (δ : Multiset I) (hδ : β + (σ : Multiset I) = δ) (hδ' : β + (σ' : Multiset I) = δ)
    (τ : List I) (γ : Multiset I) (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (h' : β + ((σ' ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')}
    (ha : a ∈ parity (R := k) _ _ p) (M : ContentModules D Sc cutoff N β) :
    (contentInductionTo D Sc cutoff N δ τ γ hγ).map
        ((contentInductionTransform D Sc cutoff N hδ hδ' ha).app p M) ≫
      (compIsoApp
      (contentInductionTo D Sc cutoff N β σ δ hδ)
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h)
      (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M).hom =
    (compIsoApp
      (contentInductionTo D Sc cutoff N β σ' δ hδ')
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ' ++ τ) γ h')
      (contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h') M).hom ≫
      (contentInductionTransform D Sc cutoff N h h'
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)).app p M := by
  have hm := (contentInductionTransform D Sc cutoff N hδ hδ' ha).app_mem p M
  have hc := (contentInductionTransform D Sc cutoff N h h'
    (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)).app_mem p M
  have hf := compIsoApp_hom_mem
    (contentInductionTo D Sc cutoff N β σ δ hδ)
    (contentInductionTo D Sc cutoff N δ τ γ hγ)
    (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h)
    (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M
    (contentInductionCompTo_mem D Sc cutoff N β σ δ hδ τ γ hγ h M).1
  have hf' := compIsoApp_hom_mem
    (contentInductionTo D Sc cutoff N β σ' δ hδ')
    (contentInductionTo D Sc cutoff N δ τ γ hγ)
    (contentInductionTo D Sc cutoff N β (σ' ++ τ) γ h')
    (contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h') M
    (contentInductionCompTo_mem D Sc cutoff N β σ' δ hδ' τ γ hγ h' M).1
  apply homogeneous_total_ext (p := p)
    (by simpa only [add_zero] using
      comp_mem (Supercategory.map_mem (contentInductionTo D Sc cutoff N δ τ γ hγ) hm) hf)
    (by simpa only [zero_add] using comp_mem hf' hc)
  intro z
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  change (moduleIsoLinearEquiv
      ((contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h).app M) z).toLinearMap ∘ₗ
      ((contentInductionTo D Sc cutoff N δ τ γ hγ).map
        ((contentInductionTransform D Sc cutoff N hδ hδ' ha).app p M)).total z =
    ((contentInductionTransform D Sc cutoff N h h'
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)).app p M).total z ∘ₗ
      (moduleIsoLinearEquiv
        ((contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h').app M) z).toLinearMap
  rw [contentInductionTransform_total,
    map_transform_total _ hm, contentInductionTransform_app]
  exact contentInductionCompTo_inner_arrow D Sc cutoff N β σ σ' δ hδ hδ' τ γ hγ h h' ha M z

/-- Intermediate source-arrow form of the module comparison. The equality
identifies the supplied arrow with the same right-whiskered source; the prefix
comparison discharges it with `contentTriplePrefixAffine_eq_whisker`. -/
theorem contentInductionCompTo_inner_map_of_eq (β : Multiset I) (σ σ' : List I)
    (δ : Multiset I) (hδ : β + (σ : Multiset I) = δ) (hδ' : β + (σ' : Multiset I) = δ)
    (τ : List I) (γ : Multiset I) (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (h' : β + ((σ' ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')}
    (ha : a ∈ parity (R := k) _ _ p)
    {b : (pres D Sc).obj (ob D (σ ++ τ)) ⟶ (pres D Sc).obj (ob D (σ' ++ τ))}
    (hb : b ∈ parity (R := k) _ _ p)
    (hab : b = a ▷ (pres D Sc).obj (ob D τ))
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionTo D Sc cutoff N δ τ γ hγ).map
        ((contentInductionTransform D Sc cutoff N hδ hδ' ha).app p M) ≫
      (compIsoApp
      (contentInductionTo D Sc cutoff N β σ δ hδ)
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h)
      (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M).hom =
    (compIsoApp
      (contentInductionTo D Sc cutoff N β σ' δ hδ')
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ' ++ τ) γ h')
      (contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h') M).hom ≫
      (contentInductionTransform D Sc cutoff N h h' hb).app p M := by
  cases hab
  exact contentInductionCompTo_inner_map D Sc cutoff N β σ σ' δ hδ hδ' τ γ hγ h h' ha M

section PrefixComparisonPremises
variable
  (β : Multiset I) (i j l : I) (δ γ : Multiset I)
  (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
  (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
  (h : β + ([i,j,l] : Multiset I) = γ)
  (ht : β + ([j,i,l] : Multiset I) = γ)
  (hγ : δ + ([l] : Multiset I) = γ)
  (M : ContentModules D Sc cutoff N β)

end PrefixComparisonPremises

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Normalization of independently whiskered triple crossings -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentTripleRight_whisker (i j l : I) :
    contentTripleRight D Sc i j l = (pres D Sc).obj (ob D [i]) ◁ crossTwo D Sc j l := by
  rw [crossTwo, cl_whiskerLeft]
  rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The suffix pair crossing as a natural family

This supplies the other independently induced crossing family required by the
three-factor braid fields of Brundan–Ellis Definition 1.5.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Total components detect a supernatural transformation, without a
homogeneity assumption. Used twice for module-valued natural families. -/
theorem BalancedInduction.supernatural_ext_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {f g : SuperNatTrans k F G}
    (h : ∀ M, f.total M = g.total M) : f = g := by
  apply SuperNatTrans.ext
  funext p M
  have hp (t : SuperNatTrans k F G) : proj k p (t.total M) = t.app p M := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (t.app_mem 0 M) (t.app_mem 1 M)
    · exact proj_eq_of_add (add_comm _ _) (t.app_mem 1 M)
        (by simpa using t.app_mem 0 M)
  rw [← hp f, ← hp g, h M]

section Suffix
variable (β : Multiset I) (i j l : I) (γ : Multiset I)
  (h : β + ([i,j,l] : Multiset I) = γ)
  (ht : β + ([i,l,j] : Multiset I) = γ)

private theorem family_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) :
    hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

end Suffix
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Outer-arrow comparison of content induction composition

Brundan--Ellis (1.9), DeformedActionAssembly §6. The existing outer-arrow
coend identity is retained as an equality of whole module maps, with the
true first intermediate content explicit. This is the suffix braid
comparison used by the selected weight charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Composition intertwines an arrow on the second inducing word,
with both endpoint casts and the true first content retained. -/
theorem contentInductionCompTo_outer_map (β : Multiset I) (σ τ τ' : List I)
    (δ γ : Multiset I) (hδ : β + (σ : Multiset I) = δ)
    (hγ : δ + (τ : Multiset I) = γ) (htγ : δ + (τ' : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (ht : β + ((σ ++ τ' : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D τ')}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionTransform D Sc cutoff N hγ htγ ha).app p
        ((contentInductionTo D Sc cutoff N β σ δ hδ).obj M) ≫
      (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h).hom.app M =
    (contentInductionCompTo D Sc cutoff N β σ δ hδ τ' γ htγ ht).hom.app M ≫
      (contentInductionTransform D Sc cutoff N h ht
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)).app p M := by
  cases hδ
  apply BalancedInduction.supernatural_ext_total
  intro z
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  change (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ hγ h).app M) z).toLinearMap ∘ₗ
      ((contentInductionTransform D Sc cutoff N hγ htγ ha).app p
        ((contentInductionTo D Sc cutoff N β σ _ rfl).obj M)).total z =
    ((contentInductionTransform D Sc cutoff N h ht
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)).app p M).total z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ' γ htγ ht).app M) z).toLinearMap
  rw [contentInductionTransform_total, contentInductionTransform_total]
  exact contentInductionComp_outer_arrow D Sc cutoff N β σ τ τ' γ hγ htγ h ht ha M z

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The uncorrected full-coefficient content braid

Brundan–Ellis Definition 1.5, the braid outside the repeated-outer correction
case. Both paths use the independent pair crossings and their induction
whiskerings. No local inverse or factor action is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private def crossingSign (i j : I) : k := by
  classical
  exact if i = j then -1 else 1

private theorem normalized_crossing (i j : I) :
    contentCrossAffine D Sc i j = crossingSign (k := k) i j • crossTwo D Sc i j := by
  classical
  by_cases h : i = j <;> simp [contentCrossAffine, crossingSign, h]

def contentNormalizedLeft (i j l : I) :=
  contentTriplePrefixAffine D Sc i j l
def contentNormalizedRight (i j l : I) :=
  (pres D Sc).obj (ob D [i]) ◁ contentCrossAffine D Sc j l

theorem contentNormalizedLeft_mem (i j l : I) :
    contentNormalizedLeft D Sc i j l ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
  contentTriplePrefixAffine_mem D Sc i j l
theorem contentNormalizedRight_mem (i j l : I) :
    contentNormalizedRight D Sc i j l ∈ parity (R := k) _ _ (D.parity j * D.parity l) :=
  MonoidalSupercategory.whiskerLeft_mem (R := k) _ (contentCrossAffine_mem D Sc j l)

/-- Both normalized source paths carry the same product of pair signs. -/
theorem contentNormalized_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j)) :
    contentNormalizedLeft D Sc i j l ≫ contentNormalizedRight D Sc j i l ≫
        contentNormalizedLeft D Sc j l i =
      contentNormalizedRight D Sc i j l ≫ contentNormalizedLeft D Sc i l j ≫
        contentNormalizedRight D Sc l i j := by
  simp only [contentNormalizedLeft, contentTriplePrefixAffine_eq_whisker,
    contentNormalizedRight, normalized_crossing,
    MonoidalSupercategory.smul_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_smul (R := k),
    ← contentTripleLeft_whisker, ← contentTripleRight_whisker,
    Linear.smul_comp, Linear.comp_smul, smul_smul]
  have h := tripleCross_braid D Sc i j l hb ⟨[], rfl⟩
  change contentTripleLeft D Sc i j l ≫ contentTripleRight D Sc j i l ≫
      contentTripleLeft D Sc j l i =
    contentTripleRight D Sc i j l ≫ contentTripleLeft D Sc i l j ≫
      contentTripleRight D Sc l i j at h
  rw [h]
  congr 1
  ring

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The same-colour braid on direct word induction

Brundan--Ellis (1.9). Retain the normalized affine prefix and suffix as
whole module endomorphisms of direct three-letter induction. This form
is needed by the selected weight triple chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem moduleBraid_of_total
    {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (L R : End M)
    (a b : ∀ w, M.obj w →ₗ[k] M.obj w)
    (hL : ∀ w, L.total w = a w) (hR : ∀ w, R.total w = b w)
    (hb : ∀ w, (b w).comp ((a w).comp (b w)) = (a w).comp ((b w).comp (a w))) :
    R ≫ L ≫ R = L ≫ R ≫ L := by
  apply BalancedInduction.supernatural_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total]
  change (R.total w).comp ((L.total w).comp (R.total w)) =
    (L.total w).comp ((R.total w).comp (L.total w))
  rw [hL, hR, hb]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Pure coend form of the normalized same-colour braid, with all word endpoints pinned. -/
theorem contentInduction_sameColour_linear_braid
    (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i,i,i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z)) =
      (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v g b
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,i,i]) (τ := [i,i,i]) (υ := [i,i,i]) (ω := [i,i,i]) h h h h
    (contentNormalizedRight_mem D Sc i i i) (contentNormalizedLeft_mem D Sc i i i)
    (contentNormalizedRight_mem D Sc i i i) M z v g b]
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,i,i]) (τ := [i,i,i]) (υ := [i,i,i]) (ω := [i,i,i]) h h h h
    (contentNormalizedLeft_mem D Sc i i i) (contentNormalizedRight_mem D Sc i i i)
    (contentNormalizedLeft_mem D Sc i i i) M z v g b]
  rw [contentNormalized_braid D Sc i i i (by simp)]

/-- The two independently induced normalized operators satisfy the
same-colour braid on every module, before weight transport. -/
theorem contentInduction_sameColour_braid (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i,i,i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    (contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
        (D.parity i * D.parity i) M =
    (contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
        (D.parity i * D.parity i) M := by
  apply moduleBraid_of_total
    ((contentInductionTo D Sc cutoff N β [i,i,i] γ h).obj M)
    ((contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
      (D.parity i * D.parity i) M)
    ((contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
      (D.parity i * D.parity i) M)
    (fun z => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z)
    (fun z => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z)
  · intro z
    exact contentInductionTransform_total D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i) M z
  · intro z
    exact contentInductionTransform_total D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i) M z
  · intro z
    exact contentInduction_sameColour_linear_braid D Sc cutoff N β i γ h M z

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Distinct-colour slides on content induction

Brundan–Ellis Definition 1.5, (1.8). The pair crossing and both single-letter
dots are independently constructed. Common target content is retained at
both words; full coefficient parity is carried by balanced induction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem contentTwoTransform_tensor {β γ : Multiset I} {σ τ υ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (hυ : β + (υ : Multiset I) = γ) {p q : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    {b : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D υ)}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β υ γ hυ).obj v ⟶ z) (m : M.obj v) :
    ((BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M z).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hτ hυ hb) M z))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β υ γ hυ) M.toFunctor v h m) =
    sign k (p*q) •
      BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ) M.toFunctor v
        (contentAppendToComponent D Sc cutoff N hσ hυ (a ≫ b) v ≫
          twist k (p+q) h) m := by
  rw [BalancedInduction.transformLinear_comp, LinearMap.smul_apply,
    BalancedInduction.transformLinear_tensor]
  congr 2
  rw [contentAppendToComponent_comp D Sc cutoff N hσ hτ hυ a hb]

private theorem firstDot_slide_source {i j : I} (hij : i ≠ j) :
    dotE D Sc [i,j] 0 ≫ contentCrossAffine D Sc i j =
      SKM.zsign k (D.parity i * D.parity j) •
        (contentCrossAffine D Sc i j ≫ dotE D Sc [j,i] 1) := by
  rw [contentCrossAffine_distinct D Sc i j hij]
  simp only [dotE_eq, crossTwo, cl_comp]
  exact slide_left_ne D Sc [] [] i j hij _ _

private theorem lastDot_slide_source {i j : I} (hij : i ≠ j) :
    contentCrossAffine D Sc i j ≫ dotE D Sc [j,i] 0 =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc [i,j] 1 ≫ contentCrossAffine D Sc i j) := by
  rw [contentCrossAffine_distinct D Sc i j hij]
  simp only [dotE_eq, crossTwo, cl_comp]
  exact slide_right_ne D Sc [] [] i j hij _ _

theorem contentInduction_distinct_slide_left_linear (β : Multiset I) {i j : I} (hij : i ≠ j) (γ : Multiset I)
    (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hij'
      (firstDot_parity D Sc i [j])) M z).comp
      (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
        (contentCrossAffine_mem D Sc i j)) M z) =
    sign k (D.parity i * D.parity j) •
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
        (contentCrossAffine_mem D Sc i j)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hji hji
          (contentPairDot_one_parity D Sc j i)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTwoTransform_tensor, LinearMap.smul_apply, contentTwoTransform_tensor,
    firstDot_slide_source D Sc hij, contentAppendToComponent_smul, Linear.smul_comp]
  simp only [add_comm (D.parity i) (D.parity i * D.parity j),
    mul_comm (D.parity i) (D.parity i * D.parity j)]
  simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul, smul_smul,
    sign_eq_zsign]
  congr 1
  ring
  all_goals first
    | exact contentCrossAffine_mem D Sc i j
    | exact firstDot_parity D Sc i [j]
    | exact firstDot_parity D Sc j [i]
    | exact contentPairDot_one_parity D Sc i j
    | exact contentPairDot_one_parity D Sc j i

theorem contentInduction_distinct_slide_right_linear (β : Multiset I) {i j : I} (hij : i ≠ j) (γ : Multiset I)
    (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
      (contentCrossAffine_mem D Sc i j)) M z).comp
      (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hji hji
        (firstDot_parity D Sc j [i])) M z) =
    sign k (D.parity i * D.parity j) •
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hij'
        (contentPairDot_one_parity D Sc i j)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
          (contentCrossAffine_mem D Sc i j)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTwoTransform_tensor, LinearMap.smul_apply, contentTwoTransform_tensor,
    lastDot_slide_source D Sc hij, contentAppendToComponent_smul, Linear.smul_comp]
  simp only [add_comm (D.parity i * D.parity j) (D.parity j),
    mul_comm (D.parity i * D.parity j) (D.parity j)]
  simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul, smul_smul,
    sign_eq_zsign]
  congr 1
  ring
  all_goals first
    | exact contentCrossAffine_mem D Sc i j
    | exact firstDot_parity D Sc j [i]
    | exact contentPairDot_one_parity D Sc i j

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The multicolour braid on direct word induction

Brundan--Ellis (1.9), outside the repeated-outer correction case. The
normalized direct affine prefix and suffix satisfy the whole module-map
braid between the six word inductions. This form is consumed by the
independently selected weight triple charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem moduleThree_eq_of_totals
    {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M₀ M₁ M₂ M₃ M₄ M₅ : Superfunctor k C (SVec k))
    (a₀ : M₀ ⟶ M₁) (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃)
    (b₀ : M₀ ⟶ M₄) (b₁ : M₄ ⟶ M₅) (b₂ : M₅ ⟶ M₃)
    (f₀ : ∀ w, M₀.obj w →ₗ[k] M₁.obj w) (f₁ : ∀ w, M₁.obj w →ₗ[k] M₂.obj w)
    (f₂ : ∀ w, M₂.obj w →ₗ[k] M₃.obj w) (g₀ : ∀ w, M₀.obj w →ₗ[k] M₄.obj w)
    (g₁ : ∀ w, M₄.obj w →ₗ[k] M₅.obj w) (g₂ : ∀ w, M₅.obj w →ₗ[k] M₃.obj w)
    (ha₀ : ∀ w, a₀.total w = f₀ w) (ha₁ : ∀ w, a₁.total w = f₁ w) (ha₂ : ∀ w, a₂.total w = f₂ w)
    (hb₀ : ∀ w, b₀.total w = g₀ w) (hb₁ : ∀ w, b₁.total w = g₁ w) (hb₂ : ∀ w, b₂.total w = g₂ w)
    (hh : ∀ w, (f₂ w).comp ((f₁ w).comp (f₀ w)) = (g₂ w).comp ((g₁ w).comp (g₀ w))) :
    a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂ := by
  apply BalancedInduction.supernatural_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total]
  change (a₂.total w).comp ((a₁.total w).comp (a₀.total w)) =
    (b₂.total w).comp ((b₁.total w).comp (b₀.total w))
  rw [ha₀, ha₁, ha₂, hb₀, hb₁, hb₂, hh]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
private theorem inductionLinear_braid (β : Multiset I) (i j l : I)
    (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h1 (contentNormalizedLeft_mem D Sc i j l)) M z).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h1 h2 (contentNormalizedRight_mem D Sc j i l)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h2 h3 (contentNormalizedLeft_mem D Sc j l i)) M z)) =
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h4 (contentNormalizedRight_mem D Sc i j l)) M z).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h4 h5 (contentNormalizedLeft_mem D Sc i l j)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h5 h3 (contentNormalizedRight_mem D Sc l i j)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,j,l]) (τ := [j,i,l]) (υ := [j,l,i]) (ω := [l,j,i])
    h0 h1 h2 h3
    (contentNormalizedLeft_mem D Sc i j l) (contentNormalizedRight_mem D Sc j i l) (contentNormalizedLeft_mem D Sc j l i) M z v h m]
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,j,l]) (τ := [i,l,j]) (υ := [l,i,j]) (ω := [l,j,i])
    h0 h4 h5 h3
    (contentNormalizedRight_mem D Sc i j l) (contentNormalizedLeft_mem D Sc i l j) (contentNormalizedRight_mem D Sc l i j) M z v h m]
  have hs : (D.parity i * D.parity l) * (D.parity j * D.parity l) +
      (D.parity i * D.parity j) *
        (D.parity i * D.parity l + D.parity j * D.parity l) =
      (D.parity i * D.parity l) * (D.parity i * D.parity j) +
      (D.parity j * D.parity l) *
        (D.parity i * D.parity l + D.parity i * D.parity j) := by ring
  have hp : D.parity i * D.parity j +
      (D.parity i * D.parity l + D.parity j * D.parity l) =
      D.parity j * D.parity l +
        (D.parity i * D.parity l + D.parity i * D.parity j) := by ring
  rw [hs, hp, contentNormalized_braid D Sc i j l hb]

section Braid
variable (β : Multiset I) (i j l : I) (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
  (h₀ : β + ([i,j,l] : Multiset I) = γ) (h₁ : β + ([j,i,l] : Multiset I) = γ)
  (h₂ : β + ([j,l,i] : Multiset I) = γ) (h₃ : β + ([l,j,i] : Multiset I) = γ)
  (h₄ : β + ([i,l,j] : Multiset I) = γ) (h₅ : β + ([l,i,j] : Multiset I) = γ)

include hb in
/-- The direct normalized operators satisfy the multicolour braid on every
module, with all six endpoint contents explicit and no comparison premise. -/
theorem contentInduction_uncorrected_braid (M : ContentModules D Sc cutoff N β) :
    ((contentInductionTransform D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j)).app (D.parity i * D.parity j) M) ≫
      ((contentInductionTransform D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j)).app (D.parity i * D.parity l) M) ≫
      ((contentInductionTransform D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l)).app (D.parity j * D.parity l) M) =
    ((contentInductionTransform D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i)).app (D.parity j * D.parity l) M) ≫
      ((contentInductionTransform D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l)).app (D.parity i * D.parity l) M) ≫
      ((contentInductionTransform D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l)).app (D.parity i * D.parity j) M) := by
  apply moduleThree_eq_of_totals
    ((contentInductionTo D Sc cutoff N β [l,j,i] γ h₃).obj M)
    ((contentInductionTo D Sc cutoff N β [l,i,j] γ h₅).obj M)
    ((contentInductionTo D Sc cutoff N β [i,l,j] γ h₄).obj M)
    ((contentInductionTo D Sc cutoff N β [i,j,l] γ h₀).obj M)
    ((contentInductionTo D Sc cutoff N β [j,l,i] γ h₂).obj M)
    ((contentInductionTo D Sc cutoff N β [j,i,l] γ h₁).obj M)
    ((contentInductionTransform D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j)).app (D.parity i * D.parity j) M)
    ((contentInductionTransform D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j)).app (D.parity i * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l)).app (D.parity j * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i)).app (D.parity j * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l)).app (D.parity i * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l)).app (D.parity i * D.parity j) M)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l)) M w)
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l) M w
  · intro w
    exact (inductionLinear_braid D Sc cutoff N β i j l hb γ h₀ h₁ h₂ h₃ h₄ h₅ M w).symm
end Braid
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Affine contexts of the three positioned dots

Brundan--Ellis (1.9), the repeated-outer polynomial. Normalize the literal
contexts obtained from the selected triple-dot comparison to the three
source positions, before any module or coefficient evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The first dot retains both right contexts as the first position of the whole word. -/
theorem tripleFirstDot_affineContexts (l j i : I) :
    (dotE D Sc [l] 0 ▷ (pres D Sc).obj (ob D [j])) ▷ (pres D Sc).obj (ob D [i]) =
      dotE D Sc [l,j,i] 0 := by
  erw [dotE_whiskerRight D Sc [l] [j] 0 (by simp),
    dotE_whiskerRight D Sc [l,j] [i] 0 (by simp)]
  rfl

/-- The middle dot has the first-letter left context and final-letter right context. -/
theorem tripleMiddleDot_affineContexts (l j i : I) :
    ((pres D Sc).obj (ob D [l]) ◁ dotE D Sc [j] 0) ▷ (pres D Sc).obj (ob D [i]) =
      (pres D Sc).obj (ob D [l]) ◁ dotE D Sc [j,i] 0 := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [l]))) (dotE D Sc [j] 0)
    (𝟙 ((pres D Sc).obj (ob D [i])))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k), MonoidalSupercategory.whiskerLeft_id (R := k),
    Category.id_comp, Category.comp_id, Presentation.associator_eq, eqToIso.hom, eqToHom_refl] at h
  rw [dotE_whiskerRight D Sc [j] [i] 0 (by simp)] at h
  exact h

/-- The last dot sees the two-letter left context as the nested first and middle contexts. -/
theorem tripleLastDot_affineContexts (l j i : I) :
    (pres D Sc).obj (ob D [l,j]) ◁ dotE D Sc [i] 0 =
      (pres D Sc).obj (ob D [l]) ◁ (pres D Sc).obj (ob D [j]) ◁ dotE D Sc [i] 0 := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [l]))) (𝟙 ((pres D Sc).obj (ob D [j]))) (dotE D Sc [i] 0)
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k), MonoidalSupercategory.whiskerLeft_id (R := k),
    Category.id_comp, Category.comp_id, Presentation.associator_eq, eqToIso.hom, eqToHom_refl] at h
  exact h

/-- The middle literal context is exactly the indexed polynomial generator. -/
theorem tripleMiddleDot_affineIndex (l j i : I) :
    ((pres D Sc).obj (ob D [l]) ◁ dotE D Sc [j] 0) ▷ (pres D Sc).obj (ob D [i]) =
      dotE D Sc [l,j,i] 1 := by
  erw [tripleMiddleDot_affineContexts D Sc l j i, whiskerLeft_letter_dotE]

/-- The last literal context is exactly the indexed polynomial generator. -/
theorem tripleLastDot_affineIndex (l j i : I) :
    (pres D Sc).obj (ob D [l,j]) ◁ dotE D Sc [i] 0 = dotE D Sc [l,j,i] 2 := by
  erw [tripleLastDot_affineContexts D Sc l j i, whiskerLeft_letter_dotE, whiskerLeft_letter_dotE]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The original-parameter source correction at an explicit output content

Brundan--Ellis (1.9), repeated outer colour. Retain the common output γ
and all word-content equalities while applying the checked source
polynomial identity. This avoids replacing a native output module by a
separately normalized canonical-content model.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
local notation "Sc'" => parameterTwist D Sc

/-- The normalized source mixed braid equals the ORIGINAL Sc ordered
polynomial at a specified output content, with all three word endpoints explicit. -/
theorem contentMixedBraid_at_polynomial
    (β : Multiset I) (i j : I) (hij : i ≠ j) (γ : Multiset I)
    (h₀ : β + ([i,j,i] : Multiset I) = γ)
    (h₁ : β + ([i,i,j] : Multiset I) = γ)
    (h₂ : β + ([j,i,i] : Multiset I) = γ)
    (M : ContentModules D Sc' cutoff bound β) (w : ContentCategory D Sc' cutoff bound γ) :
    let T0 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₁ (contentTripleRight_parity D Sc' i j i)) M w
    let T1 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₁ (contentTripleLeft_parity D Sc' i i j)) M w
    let T2 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₀ (contentTripleRight_parity D Sc' i i j)) M w
    let T3 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₂ (contentTripleLeft_parity D Sc' i j i)) M w
    let T4 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₂ (contentTripleRight_parity D Sc' j i i)) M w
    let T5 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₀ (contentTripleLeft_parity D Sc' j i i)) M w
    T0.comp ((-T1).comp T2) - T3.comp ((-T4).comp T5) =
      tripleDotCorrectionPolynomial D Sc i j
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (firstDot_parity D Sc' i [j,i])) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_one_parity D Sc' i j)) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_two_parity D Sc' i j)) M w) := by
  cases h₀
  have hs := contentMixedBraid_polynomial_linear D Sc cutoff bound β hij M w
  have hp := contentMixedBraidPolynomial_eq_ordered D Sc cutoff bound β i j M w
  exact hs.trans hp

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Normalized mixed braid correction on direct word induction

Brundan--Ellis (1.9). Keep the independently prescribed equal-colour
minus signs and all intermediate word contents in the corrected relation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem transform_congr {β γ : Multiset I} {σ τ : List I} {p : ZMod 2}
    (h : β + (σ : Multiset I) = γ) (ht : β + (τ : Multiset I) = γ)
    {f g : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p) (hfg : f = g)
    (M : ContentModules D Sc cutoff bound β) (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff bound h ht hf) M w =
      BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff bound h ht hg) M w := by
  cases hfg
  rfl

private theorem transform_neg {β γ : Multiset I} {σ τ : List I} {p : ZMod 2}
    (h : β + (σ : Multiset I) = γ) (ht : β + (τ : Multiset I) = γ)
    {f : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff bound β) (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound h ht (Submodule.neg_mem _ hf)) M w =
      -BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff bound h ht hf) M w := by
  apply BalancedInduction.hom_ext
  intro v a m
  simp only [BalancedInduction.transformLinear_tensor, contentAppendToComponent_neg,
    Preadditive.neg_comp, LinearMap.neg_apply]
  simp only [BalancedInduction.tensor, TensorProduct.neg_tmul, map_neg]

private theorem normalized_left_distinct (i j l : I) (hij : i ≠ j) :
    contentNormalizedLeft D Sc i j l = contentTripleLeft D Sc i j l := by
  classical
  simp only [contentNormalizedLeft, contentTriplePrefixAffine, ite_eq_right hij]
private theorem normalized_left_equal (i l : I) :
    contentNormalizedLeft D Sc i i l = -contentTripleLeft D Sc i i l := by
  classical
  simp only [contentNormalizedLeft, contentTriplePrefixAffine, ite_true]
private theorem normalized_right_distinct (i j l : I) (hjl : j ≠ l) :
    contentNormalizedRight D Sc i j l = contentTripleRight D Sc i j l := by
  rw [contentNormalizedRight, contentCrossAffine_distinct D Sc j l hjl,
    contentTripleRight_whisker]
private theorem normalized_right_equal (j i : I) :
    contentNormalizedRight D Sc j i i = -contentTripleRight D Sc j i i := by
  rw [contentNormalizedRight, contentCrossAffine_equal,
    MonoidalSupercategory.whiskerLeft_neg (R := k), contentTripleRight_whisker]

local notation "Sc'" => parameterTwist D Sc

/-- Direct normalized crossing paths with a repeated outer colour differ
by the ordered correction in the original parameter family Sc. -/
theorem contentNormalizedMixedBraid_at_polynomial
    (β : Multiset I) (i j : I) (hij : i ≠ j) (γ : Multiset I)
    (h₀ : β + ([i,j,i] : Multiset I) = γ)
    (h₁ : β + ([i,i,j] : Multiset I) = γ)
    (h₂ : β + ([j,i,i] : Multiset I) = γ)
    (M : ContentModules D Sc' cutoff bound β) (w : ContentCategory D Sc' cutoff bound γ) :
    let T0 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₁ (contentNormalizedRight_mem D Sc' i j i)) M w
    let T1 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₁ (contentNormalizedLeft_mem D Sc' i i j)) M w
    let T2 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₀ (contentNormalizedRight_mem D Sc' i i j)) M w
    let T3 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₂ (contentNormalizedLeft_mem D Sc' i j i)) M w
    let T4 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₂ (contentNormalizedRight_mem D Sc' j i i)) M w
    let T5 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₀ (contentNormalizedLeft_mem D Sc' j i i)) M w
    T0.comp (T1.comp T2) - T3.comp (T4.comp T5) =
      tripleDotCorrectionPolynomial D Sc i j
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (firstDot_parity D Sc' i [j,i])) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_one_parity D Sc' i j)) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_two_parity D Sc' i j)) M w) := by
  dsimp only
  have h0 := transform_congr D Sc' cutoff bound h₀ h₁
    (contentNormalizedRight_mem D Sc' i j i) (contentTripleRight_parity D Sc' i j i)
    (normalized_right_distinct D Sc' i j i hij.symm) M w
  have h1 := transform_congr D Sc' cutoff bound h₁ h₁
    (contentNormalizedLeft_mem D Sc' i i j) (Submodule.neg_mem _ (contentTripleLeft_parity D Sc' i i j))
    (normalized_left_equal D Sc' i j) M w
  have hn1 := transform_neg D Sc' cutoff bound h₁ h₁ (contentTripleLeft_parity D Sc' i i j) M w
  have he1 := h1.trans hn1
  have h2 := transform_congr D Sc' cutoff bound h₁ h₀
    (contentNormalizedRight_mem D Sc' i i j) (contentTripleRight_parity D Sc' i i j)
    (normalized_right_distinct D Sc' i i j hij) M w
  have h3 := transform_congr D Sc' cutoff bound h₀ h₂
    (contentNormalizedLeft_mem D Sc' i j i) (contentTripleLeft_parity D Sc' i j i)
    (normalized_left_distinct D Sc' i j i hij) M w
  have h4 := transform_congr D Sc' cutoff bound h₂ h₂
    (contentNormalizedRight_mem D Sc' j i i) (Submodule.neg_mem _ (contentTripleRight_parity D Sc' j i i))
    (normalized_right_equal D Sc' j i) M w
  have hn4 := transform_neg D Sc' cutoff bound h₂ h₂ (contentTripleRight_parity D Sc' j i i) M w
  have he4 := h4.trans hn4
  have h5 := transform_congr D Sc' cutoff bound h₂ h₀
    (contentNormalizedLeft_mem D Sc' j i i) (contentTripleLeft_parity D Sc' j i i)
    (normalized_left_distinct D Sc' j i i hij.symm) M w
  rw [h0, he1, h2, h3, he4, h5]
  exact contentMixedBraid_at_polynomial D Sc cutoff bound β i j hij γ h₀ h₁ h₂ M w

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Zero objects in the fixed-output content Hom category

The zero padding in `SwappedHomInversion.md` §2 uses the actual zero
module at a fixed output content. Its constant superfunctor is a zero
object while retaining the entire probe input category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction
universe u
local instance contentZeroHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The constant actual zero module, regarded as a whole-input superfunctor. -/
def contentHomZero (β : Multiset I) (A : PiSCat.{u,u,u+1} k) :
    A ⟶ contentModuleTarget D Sc cutoff bound β :=
  ⟨elvZeroFunctor D Sc cutoff bound (C := A) β⟩

/-- Its identity vanishes as a supernatural transformation, before input evaluation. -/
theorem contentHomZero_isZero (β : Multiset I) (A : PiSCat.{u,u,u+1} k) :
    Limits.IsZero (contentHomZero D Sc cutoff bound β A) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p M
  exact (elvZeroModule_isZero D Sc cutoff bound β).eq_of_src _ _

/-- The padded fixed-output Hom category has its zero object from the source modules. -/
instance contentHom_hasZeroObject (β : Multiset I) (A : PiSCat.{u,u,u+1} k) :
    Limits.HasZeroObject (A ⟶ contentModuleTarget D Sc cutoff bound β) :=
  ⟨⟨contentHomZero D Sc cutoff bound β A, contentHomZero_isZero D Sc cutoff bound β A⟩⟩

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Graded coordinates of morphisms between content representables

Covariant representables reverse the representing arrow. Each parity component
precomposes with that arrow and twists the argument by its total parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ContentYoneda
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)
variable {v w : ContentCategory D Sc cutoff N β}

def component (f : w ⟶ v) (p : ZMod 2) (z : ContentCategory D Sc cutoff N β) :
    (v ⟶ z) →ₗ[k] (w ⟶ z) := by
  let fp : w ⟶ v := proj k p f
  exact {
    toFun := fun h => fp ≫ twist k p h
    map_add' := fun h h' => by rw [map_add, Preadditive.comp_add]
    map_smul' := fun r h => by rw [map_smul, Linear.comp_smul]; rfl }

def fromArrow (f : w ⟶ v) : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w :=
  Superfunctor.homMk {
    app := component D Sc cutoff N β f
    app_mem := by
      intro p z
      apply SVec.mem_parityHom_of_apply_mem
      intro q h hh
      change h ∈ (contentHomSpace D Sc cutoff N β v z).part q at hh
      change proj k p f ≫ twist k p h ∈ (contentHomSpace D Sc cutoff N β w z).part (q + p)
      rw [contentHomSpace_part] at hh ⊢
      change proj k p f ≫ twist k p h ∈ parity (R := k) w z (q + p)
      rw [add_comm q p]
      exact comp_mem (proj_mem p f) (twist_mem p hh)
    naturality := by
      intro p z t q a ha
      apply LinearMap.ext
      intro h
      change v ⟶ z at h
      change proj k p f ≫ twist k p (h ≫ a) =
        koszulSign p q • ((proj k p f ≫ twist k p h) ≫ a)
      rw [twist_comp, twist_of_mem p ha, Linear.comp_smul,
        Linear.comp_smul, koszulSign_smul (R := k), Category.assoc] }

/-- A component with its content-Hom endpoints exposed. -/
def componentMap (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2)
    (z : ContentCategory D Sc cutoff N β) : (v ⟶ z) →ₗ[k] (w ⟶ z) := t.app p z

def evaluate (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) : w ⟶ v :=
  componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v)

theorem evaluate_part (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2) :
    componentMap D Sc cutoff N β t p v (𝟙 v) ∈ parity (R := k) w v p := by
  have hi : (𝟙 v : v ⟶ v) ∈ (contentHomSpace D Sc cutoff N β v v).part 0 := by
    rw [contentHomSpace_part]; exact id_mem v
  have h := SVec.apply_mem_part (t.app_mem p v) hi
  change componentMap D Sc cutoff N β t p v (𝟙 v) ∈ (contentHomSpace D Sc cutoff N β w v).part (0 + p) at h
  rw [zero_add, contentHomSpace_part] at h
  exact h

@[simp] theorem evaluate_fromArrow (f : w ⟶ v) :
    evaluate D Sc cutoff N β (fromArrow D Sc cutoff N β f) = f := by
  change (proj k 0 f ≫ twist k 0 (𝟙 v)) + (proj k 1 f ≫ twist k 1 (𝟙 v)) = f
  simp only [twist_id, Category.comp_id, proj_add_proj]

theorem app_formula (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2)
    (z : ContentCategory D Sc cutoff N β) (h : v ⟶ z) :
    componentMap D Sc cutoff N β t p z h = componentMap D Sc cutoff N β t p v (𝟙 v) ≫ twist k p h := by
  refine induction_on (R := k) h ?_ ?_ ?_
  · simp
  · intro q h hh
    have hn := congrArg (fun a => a (𝟙 v)) (t.naturality p h hh)
    change componentMap D Sc cutoff N β t p z (𝟙 v ≫ h) = koszulSign p q • (componentMap D Sc cutoff N β t p v (𝟙 v) ≫ h) at hn
    rw [Category.id_comp, koszulSign_smul (R := k)] at hn
    rw [twist_of_mem p hh, Linear.comp_smul]
    exact hn
  · intro a b ha hb
    rw [map_add, map_add, Preadditive.comp_add, ha, hb]

theorem fromArrow_evaluate (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) :
    fromArrow D Sc cutoff N β (evaluate D Sc cutoff N β t) = t := by
  apply Superfunctor.hom_ext
  intro p z
  apply LinearMap.ext
  intro h
  change v ⟶ z at h
  change proj k p (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v)) ≫ twist k p h = componentMap D Sc cutoff N β t p z h
  rw [app_formula D Sc cutoff N β t p z h, map_add]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_of_mem (evaluate_part D Sc cutoff N β t 0),
      proj_of_mem_ne (evaluate_part D Sc cutoff N β t 1) (by decide), add_zero]
  · rw [proj_of_mem_ne (evaluate_part D Sc cutoff N β t 0) (by decide),
      proj_of_mem (evaluate_part D Sc cutoff N β t 1), zero_add]
/-- Evaluation at the identity, with the explicitly constructed inverse. -/
def homEquiv : (contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) ≃ₗ[k] (w ⟶ v) where
  toFun := evaluate D Sc cutoff N β
  invFun := fromArrow D Sc cutoff N β
  left_inv := fromArrow_evaluate D Sc cutoff N β
  right_inv := evaluate_fromArrow D Sc cutoff N β
  map_add' t s := by
    change (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β s 0 v (𝟙 v)) +
      (componentMap D Sc cutoff N β t 1 v (𝟙 v) + componentMap D Sc cutoff N β s 1 v (𝟙 v)) = _
    change _ = (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v)) +
      (componentMap D Sc cutoff N β s 0 v (𝟙 v) + componentMap D Sc cutoff N β s 1 v (𝟙 v))
    abel
  map_smul' r t := by
    change r • componentMap D Sc cutoff N β t 0 v (𝟙 v) +
      r • componentMap D Sc cutoff N β t 1 v (𝟙 v) =
      r • (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v))
    exact (smul_add _ _ _).symm

/-- Evaluation retains both homogeneous parts of the full coefficient grading. -/
theorem evaluate_proj (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2) :
    evaluate D Sc cutoff N β (proj k p t) = proj k p (evaluate D Sc cutoff N β t) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change (proj k 0 t).app 0 v (𝟙 v) + (proj k 0 t).app 1 v (𝟙 v) = _
    simp only [Superfunctor.proj_app, ite_true, one_ne_zero, ite_false]
    change componentMap D Sc cutoff N β t 0 v (𝟙 v) + 0 =
      proj k 0 (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v))
    rw [map_add, proj_of_mem (evaluate_part D Sc cutoff N β t 0),
      proj_of_mem_ne (evaluate_part D Sc cutoff N β t 1) (by decide)]
  · change (proj k 1 t).app 0 v (𝟙 v) + (proj k 1 t).app 1 v (𝟙 v) = _
    simp only [Superfunctor.proj_app, zero_ne_one, ite_false, ite_true]
    change 0 + componentMap D Sc cutoff N β t 1 v (𝟙 v) =
      proj k 1 (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v))
    rw [map_add, proj_of_mem_ne (evaluate_part D Sc cutoff N β t 0) (by decide),
      proj_of_mem (evaluate_part D Sc cutoff N β t 1)]

end OddMath.QuiverHecke.ELVOld.ContentYoneda

namespace OddMath.QuiverHecke.ELVOld.VacuumRepresentable
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

end OddMath.QuiverHecke.ELVOld.VacuumRepresentable
end

end

section

/-! # Principal inverse coordinates on supported content blocks

BE (1.13)–(1.14): the prescribed finite forward fields determine the principal inverse.
This compares every constructed content local record with the existing
weighted matrix inverse through the selected source and target charts,
without assuming a comparison of inverses or unfolding a choice.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
section Uniqueness
variable {k : Type u} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
private theorem principalFrom_coordinates {A' B' Z' : C}
    {f : B ⟶ A} {g : ℕ → (Z ⟶ A)} {F : B' ⟶ A'} {G : ℕ → (Z' ⟶ A')}
    (L : SKM.SuperSumInvFrom (k := k) f g p q n)
    (R : SKM.SuperSumInvFrom (k := k) F G p q n)
    (a : A ≅ A') (b : B ≅ B') (c : Z ≅ Z')
    (hf : b.hom ≫ F ≫ a.inv = f) (hg : ∀ m, c.hom ≫ G m ≫ a.inv = g m) :
    L.f' = a.hom ≫ R.f' ≫ b.inv := by
  symm
  apply L.hom_ext
  · calc
      f ≫ (a.hom ≫ R.f' ≫ b.inv) = b.hom ≫ (F ≫ R.f') ≫ b.inv := by
        rw [← hf]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = f ≫ L.f' := by rw [R.ff, Category.id_comp, b.hom_inv_id, L.ff]
  · intro m hm
    calc
      g m ≫ (a.hom ≫ R.f' ≫ b.inv) = c.hom ≫ (G m ≫ R.f') ≫ b.inv := by
        rw [← hg m]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = g m ≫ L.f' := by rw [R.gf m hm, Limits.zero_comp, Limits.comp_zero, L.gf m hm]
private theorem principalTo_coordinates {A' B' Z' : C}
    {f : A ⟶ B} {g : ℕ → (A ⟶ Z)} {F : A' ⟶ B'} {G : ℕ → (A' ⟶ Z')}
    (L : SKM.SuperSumInvTo (k := k) f g p q n)
    (R : SKM.SuperSumInvTo (k := k) F G p q n)
    (a : A ≅ A') (b : B ≅ B') (c : Z ≅ Z')
    (hf : a.hom ≫ F ≫ b.inv = f) (hg : ∀ m, a.hom ≫ G m ≫ c.inv = g m) :
    L.f' = b.hom ≫ R.f' ≫ a.inv := by
  symm
  apply L.hom_ext
  · calc
      (b.hom ≫ R.f' ≫ a.inv) ≫ f = b.hom ≫ (R.f' ≫ F) ≫ b.inv := by
        rw [← hf]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = L.f' ≫ f := by rw [R.ff, Category.id_comp, b.hom_inv_id, L.ff]
  · intro m hm
    calc
      (b.hom ≫ R.f' ≫ a.inv) ≫ g m = b.hom ≫ (R.f' ≫ G m) ≫ c.inv := by
        rw [← hg m]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = L.f' ≫ g m := by rw [R.fg m hm, Limits.zero_comp, Limits.comp_zero, L.fg m hm]
end Uniqueness

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The selected lower-loop chart, for the stored successor content. -/
def contentPrincipalSourceIso (β γ : Multiset I) (i : I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N γ) :=
  let J := contentAppendTo D Sc cutoff N β [i] γ hγ
  let Q₀ := contentInclusion D Sc cutoff N β
  let Q₁ := contentInclusion D Sc cutoff N γ
  let T := truncatedAppend D Sc cutoff N [i]
  let P := induced Q₁ M
  fullSquareSourceIso J Q₁ Q₀ T (contentAppendTo_inclusion D Sc cutoff N β [i] γ hγ)
    (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hγ M)

/-- The selected upper-loop chart, for the stored successor content. -/
def contentPrincipalTargetIso (γ δ : Multiset I) (i : I)
    (hδ : γ + ([i] : Multiset I) = δ) (M : ContentModules D Sc cutoff N γ) :=
  let K := contentAppendTo D Sc cutoff N γ [i] δ hδ
  let Q₁ := contentInclusion D Sc cutoff N γ
  let Q₂ := contentInclusion D Sc cutoff N δ
  let T := truncatedAppend D Sc cutoff N [i]
  let P := induced Q₁ M
  let FE := Functor.obj (restriction T) (induced T P)
  fullSquareTargetRetargetIso K Q₂ Q₁ T (contentAppendTo_inclusion D Sc cutoff N γ [i] δ hδ)
    M FE FE (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hδ (induced T P)) (Iso.refl FE)

section Canonical
variable (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "hCross" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hDotJ" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hDotK" => contentBlockMatrixDot_supernatural D Sc cutoff N γ i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "Source" => contentPrincipalSourceIso D Sc cutoff N β γ i hJ M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N γ δ i hK M
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- Every unit-orientation local record with the prescribed forward
fields has the principal of the given weighted inverse in these charts. -/
theorem contentSupportedLocalInverseFrom_principal
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hCross M)
      (unitDotColumn K hDotK M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ) :
    L.f' = (Target).hom ≫ (weightedContentLocalInverseFrom D Sc cutoff N i P γ hh).f' ≫ (Source).inv := by
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P γ hh
  let a := Target
  let b := Source
  let c := Value
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDotK M n := by
    have hs := contentUnitDotColumn_square D Sc cutoff N γ i M n
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact principalFrom_coordinates L B a b c hf hg

/-- Every cap-orientation record has the same prescribed weighted
principal, independently of how the record was chosen. -/
theorem contentSupportedLocalInverseTo_principal
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hCross M)
      (capDotRow J hDotJ M) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ))
    (hh : contentCrossingHeight D cutoff i γ ≤ 0) :
    L.f' = (Target).hom ≫ (weightedContentLocalInverseTo D Sc cutoff N i P γ hh).f' ≫ (Source).inv := by
  let B := weightedContentLocalInverseTo D Sc cutoff N i P γ hh
  let a := Source
  let b := Target
  let c := Value
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ b.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ b.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ c.inv =
      capDotRow J hDotJ M n := by
    have hs := contentMatrixCapDotRow_square D Sc cutoff N β i M n
    have he := congrArg (fun f => f ≫ c.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact principalTo_coordinates L B a b c hf hg
end Canonical

private theorem principalSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section Targets
variable (β : Multiset I) (i : I) (γ δ : Multiset I)
  (hγ : β + ([i] : Multiset I) = γ) (hδ : γ + ([i] : Multiset I) = δ)
  (M : ContentModules D Sc cutoff N γ)
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hγ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hδ
local notation "hCross" => contentTargetsGridCross_supernatural D Sc cutoff N β γ δ i hγ hδ
local notation "hDotJ" => contentAppendTo_supernatural D Sc cutoff N hγ hγ
  (principalSingletonDot_mem D Sc i)
local notation "hDotK" => contentAppendTo_supernatural D Sc cutoff N hδ hδ
  (principalSingletonDot_mem D Sc i)
local notation "P" => induced (contentInclusion D Sc cutoff N γ) M
local notation "Source" => contentPrincipalSourceIso D Sc cutoff N β γ i hγ M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N γ δ i hδ M

end Targets

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Window inverse coordinates on supported content blocks

BE (1.13)–(1.14), and the boundary contractions of SwappedHomInversion §4:
all finite local `g'` fields are forced by the prescribed forward fields,
and agree with the weighted content inverse in the named charts. This
attachment does not yet compare weighted windows with raw OLD kernels.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
section Uniqueness
variable {k : Type u} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
private theorem windowFrom_coordinates {A' B' Z' : C}
    {f : B ⟶ A} {g : ℕ → (Z ⟶ A)} {F : B' ⟶ A'} {G : ℕ → (Z' ⟶ A')}
    (L : SKM.SuperSumInvFrom (k := k) f g p q n)
    (R : SKM.SuperSumInvFrom (k := k) F G p q n)
    (a : A ≅ A') (b : B ≅ B') (c : Z ≅ Z')
    (hf : b.hom ≫ F ≫ a.inv = f) (hg : ∀ m, c.hom ≫ G m ≫ a.inv = g m)
    (m : ℕ) (hm : m < n) :
    L.g' m = a.hom ≫ R.g' m ≫ c.inv := by
  classical
  symm
  apply L.hom_ext
  · calc
      f ≫ (a.hom ≫ R.g' m ≫ c.inv) = b.hom ≫ (F ≫ R.g' m) ≫ c.inv := by
        rw [← hf]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = f ≫ L.g' m := by rw [R.fg m hm, Limits.zero_comp, Limits.comp_zero, L.fg m hm]
  · intro l hl
    calc
      g l ≫ (a.hom ≫ R.g' m ≫ c.inv) = c.hom ≫ (G l ≫ R.g' m) ≫ c.inv := by
        rw [← hg l]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = g l ≫ L.g' m := by
        rw [R.gg l m hl hm, L.gg l m hl hm]
        split_ifs <;> simp
private theorem windowTo_coordinates {A' B' Z' : C}
    {f : A ⟶ B} {g : ℕ → (A ⟶ Z)} {F : A' ⟶ B'} {G : ℕ → (A' ⟶ Z')}
    (L : SKM.SuperSumInvTo (k := k) f g p q n)
    (R : SKM.SuperSumInvTo (k := k) F G p q n)
    (a : A ≅ A') (b : B ≅ B') (c : Z ≅ Z')
    (hf : a.hom ≫ F ≫ b.inv = f) (hg : ∀ m, a.hom ≫ G m ≫ c.inv = g m)
    (m : ℕ) (hm : m < n) :
    L.g' m = c.hom ≫ R.g' m ≫ a.inv := by
  classical
  symm
  apply L.hom_ext
  · calc
      (c.hom ≫ R.g' m ≫ a.inv) ≫ f = c.hom ≫ (R.g' m ≫ F) ≫ b.inv := by
        rw [← hf]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = L.g' m ≫ f := by rw [R.gf m hm, Limits.zero_comp, Limits.comp_zero, L.gf m hm]
  · intro l hl
    calc
      (c.hom ≫ R.g' m ≫ a.inv) ≫ g l = c.hom ≫ (R.g' m ≫ G l) ≫ c.inv := by
        rw [← hg l]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = L.g' m ≫ g l := by
        rw [R.gg m l hm hl, L.gg m l hm hl]
        split_ifs <;> simp
end Uniqueness

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

section Canonical
variable (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "hCross" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hDotJ" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hDotK" => contentBlockMatrixDot_supernatural D Sc cutoff N γ i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "Source" => contentPrincipalSourceIso D Sc cutoff N β γ i hJ M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N γ δ i hK M
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- Every unit-orientation local record with the prescribed forward
fields has the window of the given weighted inverse in these charts. -/
theorem contentSupportedLocalInverseFrom_window
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hCross M)
      (unitDotColumn K hDotK M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ)
    (m : ℕ) (hm : m < contentUnitCount D cutoff i γ) :
    L.g' m = (Target).hom ≫ (weightedContentLocalInverseFrom D Sc cutoff N i P γ hh).g' m ≫ (Value).inv := by
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P γ hh
  let a := Target
  let b := Source
  let c := Value
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDotK M n := by
    have hs := contentUnitDotColumn_square D Sc cutoff N γ i M n
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact windowFrom_coordinates L B a b c hf hg m hm

/-- Every cap-orientation record has the same prescribed weighted
window, independently of how the record was chosen. -/
theorem contentSupportedLocalInverseTo_window
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hCross M)
      (capDotRow J hDotJ M) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ))
    (hh : contentCrossingHeight D cutoff i γ ≤ 0)
    (m : ℕ) (hm : m < contentCapCount D cutoff i γ) :
    L.g' m = (Value).hom ≫ (weightedContentLocalInverseTo D Sc cutoff N i P γ hh).g' m ≫ (Source).inv := by
  let B := weightedContentLocalInverseTo D Sc cutoff N i P γ hh
  let a := Source
  let b := Target
  let c := Value
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ b.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ b.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ c.inv =
      capDotRow J hDotJ M n := by
    have hs := contentMatrixCapDotRow_square D Sc cutoff N β i M n
    have he := congrArg (fun f => f ≫ c.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact windowTo_coordinates L B a b c hf hg m hm
end Canonical

private theorem principalSingletonDot_mem_2 (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section Targets
variable (β : Multiset I) (i : I) (γ δ : Multiset I)
  (hγ : β + ([i] : Multiset I) = γ) (hδ : γ + ([i] : Multiset I) = δ)
  (M : ContentModules D Sc cutoff N γ)
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hγ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hδ
local notation "hCross" => contentTargetsGridCross_supernatural D Sc cutoff N β γ δ i hγ hδ
local notation "hDotJ" => contentAppendTo_supernatural D Sc cutoff N hγ hγ
  (principalSingletonDot_mem_2 D Sc i)
local notation "hDotK" => contentAppendTo_supernatural D Sc cutoff N hδ hδ
  (principalSingletonDot_mem_2 D Sc i)
local notation "P" => induced (contentInclusion D Sc cutoff N γ) M
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M
local notation "Source" => contentPrincipalSourceIso D Sc cutoff N β γ i hγ M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N γ δ i hδ M

/-- Stored successor contents preserve the forced weighted unit window. -/
theorem contentTargetsLocalInverseFrom_window
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hCross M)
      (unitDotColumn K hDotK M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ)
    (m : ℕ) (hm : m < contentUnitCount D cutoff i γ) :
    L.g' m = (Target).hom ≫ (weightedContentLocalInverseFrom D Sc cutoff N i P γ hh).g' m ≫
      (Value).inv := by
  subst δ
  subst γ
  exact contentSupportedLocalInverseFrom_window D Sc cutoff N β i M L hh m hm

/-- Stored successor contents preserve the forced weighted cap window. -/
theorem contentTargetsLocalInverseTo_window
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hCross M)
      (capDotRow J hDotJ M) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ))
    (hh : contentCrossingHeight D cutoff i γ ≤ 0)
    (m : ℕ) (hm : m < contentCapCount D cutoff i γ) :
    L.g' m = (Value).hom ≫ (weightedContentLocalInverseTo D Sc cutoff N i P γ hh).g' m ≫
      (Source).inv := by
  subst δ
  subst γ
  exact contentSupportedLocalInverseTo_window D Sc cutoff N β i M L hh m hm
end Targets

end OddMath.QuiverHecke.ELVOld
end

end
