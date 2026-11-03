/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockNilHecke

/-! # The chosen signed nilHecke slides on every OLD probe weight

Brundan–Ellis (1.8): transport the literal OLD probe block slides through
one selected double-induction coordinate. Both independent global dots and
the selected negative crossing are retained, including absent sectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
private theorem conjugate_relation {C : Type*} [Category C] [Preadditive C]
    {A B : C} (e : A = B) (a b c d : End B) (q : ℤ)
    (h : a ≫ b - q • (c ≫ d) = 𝟙 B) :
    (eqToHom e ≫ a ≫ eqToHom e.symm) ≫ (eqToHom e ≫ b ≫ eqToHom e.symm) -
      q • ((eqToHom e ≫ c ≫ eqToHom e.symm) ≫ (eqToHom e ≫ d ≫ eqToHom e.symm)) = 𝟙 A := by
  cases e
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The independently chosen global generators satisfy the left signed slide. -/
theorem probeOldActionEqualCross_slideLeft :
    (probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂) ≫ probeOldActionEqualCross D Sc m i Λ h₁ h₂ -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldActionEqualCross D Sc m i Λ h₁ h₂ ≫
          (probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂)) = 𝟙 _ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let F := (probeOldE D Sc m i Λ h₁).comp (probeOldE D Sc m i Λ h₂)
  let c : End F := probeOldActionEqualCross D Sc m i Λ h₁ h₂
  let o : End F := probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂
  let a : End F := probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂
  let e := supernaturalEndEvaluation F M
  change e (c * o - (koszulSign (D.parity i) (D.parity i) : ℤ) • (a * c)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  funext ε
  change ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε) ≫
      (probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      ((probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε ≫
        (probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε) = 𝟙 _
  simp only [probeOldActionEqualCross]
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    change _ ≫ (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M _ - _ = _
    rw [probeOldOuterDot_total, probeOldInnerDot_total,
      probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
      probeOldWeightEqualCrossVia_total]
    let eb := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) (M β)
    have hb := congrArg eb (probeOldBlockEqualCross_slideLeft D Sc m i Λ h₁ h₂ β)
    change eb (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β)) = eb 1 at hb
    rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hb
    change (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) ≫
          (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β)) = 𝟙 _ at hb
    have ht := conjugate_relation (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M)
      ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β))
      (koszulSign (D.parity i) (D.parity i)) hb
    convert! ht using 1
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i i Λ h₁ h₂ ε hε M).eq_of_src _ _

/-- The same chosen generators satisfy the right signed slide on all probe weights. -/
theorem probeOldActionEqualCross_slideRight :
    probeOldActionEqualCross D Sc m i Λ h₁ h₂ ≫ (probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂) -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂) ≫
          probeOldActionEqualCross D Sc m i Λ h₁ h₂) = 𝟙 _ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let F := (probeOldE D Sc m i Λ h₁).comp (probeOldE D Sc m i Λ h₂)
  let c : End F := probeOldActionEqualCross D Sc m i Λ h₁ h₂
  let o : End F := probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂
  let a : End F := probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂
  let e := supernaturalEndEvaluation F M
  change e (o * c - (koszulSign (D.parity i) (D.parity i) : ℤ) • (c * a)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  funext ε
  change (probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε ≫
      ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε) -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε ≫
        (probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε) = 𝟙 _
  simp only [probeOldActionEqualCross]
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    change (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M _ ≫ _ - _ = _
    rw [probeOldOuterDot_total, probeOldInnerDot_total,
      probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
      probeOldWeightEqualCrossVia_total]
    let eb := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) (M β)
    have hb := congrArg eb (probeOldBlockEqualCross_slideRight D Sc m i Λ h₁ h₂ β)
    change eb (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β)) = eb 1 at hb
    rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hb
    change (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) ≫
        (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β) -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
          (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β)) = 𝟙 _ at hb
    have ht := conjugate_relation (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M)
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      (koszulSign (D.parity i) (D.parity i)) hb
    convert! ht using 1
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i i Λ h₁ h₂ ε hε M).eq_of_src _ _

end OddMath.QuiverHecke
