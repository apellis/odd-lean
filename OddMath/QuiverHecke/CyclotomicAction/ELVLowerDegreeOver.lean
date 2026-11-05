/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGradingOver

/-!
# Lower degrees of coefficient Homs over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜` in nonnegative degrees. For each pair of
boundary words, the Hom modules of the ELV coefficient category over `R`, with the grading
`QuiverHecke.elvHomGradingOver`, vanish in all degrees below a bound that does not depend on
the coefficient cutoff (`QuiverHecke.exists_elvHomDegreeOver_lower_bound`).

The bound on the quiver Hecke factor comes from the normal forms `x^l ψ_w`, which span each
Hom module over `R` and have degrees bounded below (`QuiverHecke.exists_le_deg`); homogeneous
scalars of `R` only raise degrees (`BasisGrading.eq_bot_of_span_lower_bound`). The coefficient
factor has no negative degrees. For `K = R` with the trivial grading this is
`QuiverHecke.exists_elvHomDegree_lower_bound`.
-/

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams

namespace OddMath.QuiverHecke

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R)

/-- Negative coefficient degrees over a base graded in nonnegative degrees vanish. -/
theorem coefficientDegreePartOver_eq_bot_of_neg (h𝒜 : ∀ m, m < 0 → 𝒜 m = ⊥) (n : ℤ)
    (hn : n < 0) : SKM.SYM.coefficientDegreePartOver D sy 𝒜 n = ⊥ :=
  BasisGrading.basisPart_eq_bot_of_lower_bound (c := 0) h𝒜
    (SKM.SYM.coefficientDegree_nonneg D sy) (by omega)

/-- The ELV coefficient algebra over `R` has no negative degrees. -/
theorem elvCoefficientDegreeOver_eq_bot_of_neg (h𝒜 : ∀ m, m < 0 → 𝒜 m = ⊥)
    (cutoff : I → ℕ) (n : ℤ) (hn : n < 0) :
    SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff n = ⊥ := by
  unfold SKM.SYM.elvCoefficientDegreeOver
  rw [coefficientDegreePartOver_eq_bot_of_neg D sy 𝒜 h𝒜 n hn, Submodule.map_bot]

variable [GradedAlgebra 𝒜] (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc))

include hP in
/-- **Affine lower bound over a graded base.** The quiver Hecke Hom modules over `R` vanish in
all degrees below the least degree of a normal form. -/
theorem exists_presentedSubmodule_lower_bound (h𝒜 : ∀ m, m < 0 → 𝒜 m = ⊥) (v w : List I) :
    ∃ L : ℤ, ∀ n, n < L →
      CoefficientGrading.presentedSubmodule (𝒜 := 𝒜) (deg := gdeg D sy) (pres D Sc)
        (ob D v) (ob D w) n = ⊥ := by
  let _ := Linear.restrictScalars K R (H D Sc)
  obtain ⟨L, hL⟩ := exists_le_deg D sy v w
  refine ⟨L, fun n hn => ?_⟩
  refine BasisGrading.eq_bot_of_span_lower_bound (𝒜 := 𝒜)
    (DirectSum.IsInternal.submodule_independent
      (CoefficientGrading.isInternal_presentedSubmodule hP (ob D v) (ob D w)))
    h𝒜 (fun hr hy => CoefficientGrading.smul_mem_presentedPart_add hr hy)
    (v := fun i : NFIdx v w => i.nf (D := D) (Sc := Sc)) (δ' := fun i => i.deg D sy)
    (fun i => by
      change (pres D Sc).lin (LinDiagram.of (mkD D (pl v i.gens) i.2.2.2)) ∈
        CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D v) (ob D w) (i.deg D sy)
      exact CoefficientGrading.lin_mem_presentedPart
        (CoefficientGrading.of_mem_part' _ (degree_gdeg_mkD D sy _ _)))
    (span_nf D Sc v w) hL hn

include hP in
/-- **Cutoff-independent lower degrees over a graded base.** One bound works for every
coefficient cutoff. -/
theorem exists_elvHomDegreeOver_lower_bound (h𝒜 : ∀ m, m < 0 → 𝒜 m = ⊥) (v w : List I) :
    ∃ L : ℤ, ∀ cutoff : I → ℕ, ∀ n, n < L →
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      GradedSupercategory.degree (R := K) (ELVOld.obj D Sc cutoff v)
        (ELVOld.obj D Sc cutoff w) n = ⊥ := by
  obtain ⟨L, hL⟩ := exists_presentedSubmodule_lower_bound D sy 𝒜 Sc hP h𝒜 v w
  refine ⟨L, fun cutoff n hn => ?_⟩
  let _ := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  let _ := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  haveI : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  let _ := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  let _ := Linear.restrictScalars K R (H D Sc)
  let _ := Supercategory.restrictScalars K R (H D Sc)
  let _ := quiverHeckeGradingOver D sy 𝒜 Sc hP
  refine BoxProdCoefficient.homDegree_eq_bot_of_lower_bound (a := 0) (b := L)
    (fun p hp => eq_bot_iff.2 fun f hf => ?_) (fun q hq => hL q hq) (by omega)
  have hf' : SuperalgebraCat.toElem f ∈ SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff p := hf
  rw [elvCoefficientDegreeOver_eq_bot_of_neg D sy 𝒜 h𝒜 cutoff p hp] at hf'
  exact (Submodule.mem_bot K).2 ((Submodule.mem_bot K).1 hf')

end OddMath.QuiverHecke
