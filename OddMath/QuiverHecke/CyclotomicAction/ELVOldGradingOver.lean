/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleELVPolynomialGradingOver
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGradingOver

/-!
# The old cyclotomic ideal over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜`, and let the quiver Hecke presentation over
`R` be coefficient-graded homogeneous. For the grading `QuiverHecke.elvHomGradingOver` of the ELV
coefficient category over `R`, the first-position cyclotomic relation is homogeneous of degree
`2 d_j cutoff_j` (`ELVOld.relation_mem_degreeOver`), and every homogeneous component of an
element of the old two-sided cyclotomic ideal lies in the ideal
(`ELVOld.ideal_dproj_mem_over`).

The ideal is an `R`-span, while the degree projections are only `K`-linear: the step from the
generators to the span decomposes the scalars into homogeneous parts
(`BasisGrading.decompose_mem_span`). For `K = R` with the trivial grading these are
`ELVOld.relation_mem_degree` and `ELVOld.ideal_dproj_mem`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory

namespace OddMath.QuiverHecke

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- A positional normal-form diagram has the degree of its layers, over a graded base. -/
theorem cl_mem_presentedPart {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    cl D Sc t t' gs h ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D t)
      (ob D t') ((pl t gs).map fun x => gdeg D sy x.2.1).sum :=
  CoefficientGrading.lin_mem_presentedPart
    (CoefficientGrading.of_mem_part' _ (degree_gdeg_mkD D sy _ _))

/-- Dot powers on a nonempty word have their symmetrizer degree, over a graded base. -/
theorem firstDotPower_mem_presentedPart (j : I) (v : List I) (n : ℕ) :
    firstDotPower D Sc (j :: v) n ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D (j :: v)) (ob D (j :: v)) (2 * sy.d j * n) := by
  have hd : ((pl (j :: v) ((List.replicate n 0).map PG.dot)).map
      fun x => gdeg D sy x.2.1).sum = 2 * sy.d j * n := by
    simp only [List.map_replicate]
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.replicate_succ, pl_cons, PG.ld, PG.act, List.drop_zero,
        List.take_zero, List.singleton_append, List.map_cons, List.sum_cons]
      rw [ih]
      simp only [gdeg, Nat.cast_add, Nat.cast_one]
      ring
  have h := cl_mem_presentedPart D sy 𝒜 Sc (t := j :: v) (t' := j :: v)
    ((List.replicate n 0).map PG.dot)
    (by simpa only [tgt_map_dot] using sChain_pl (j :: v) ((List.replicate n 0).map PG.dot))
  rw [hd] at h
  exact h

/-- The degree-`n` part of a Hom module of the ELV coefficient category over `R`. -/
abbrev elvHomDegreeOver (v w : List I) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    Submodule K (ELVOld.hom D Sc cutoff v w) :=
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  GradedSupercategory.degree (R := K) (ELVOld.obj D Sc cutoff v) (ELVOld.obj D Sc cutoff w) n

/-- Homogeneous scalars of `R` raise degrees in the ELV coefficient category over `R`. -/
theorem smul_mem_elvHomDegreeOver {v w : List I} {e n : ℤ} {r : R}
    {y : ELVOld.hom D Sc cutoff v w} (hr : r ∈ 𝒜 e)
    (hy : y ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    r • y ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w (e + n) := by
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  have : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  exact BoxProdCoefficient.smul_mem_homDegree (𝒜 := 𝒜)
    (fun {_ _ _ _ _ _} hr hf => by
      change SuperalgebraCat.toElem (_ • _) ∈ SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff _
      rw [SuperalgebraCat.toElem_smul]
      exact SKM.SYM.smul_mem_elvCoefficientDegreeOver cutoff hr hf) hr hy

/-- A coefficient and an affine diagram contribute additively to the degree over `R`. -/
theorem elvQuotientMap_source_mem_degreeOver {v w : List I} {a : SKM.SYM D R}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)} {r s : ℤ}
    (ha : a ∈ SKM.SYM.coefficientDegreePartOver D sy 𝒜 r)
    (hf : f ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D v) (ob D w) s) :
    elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc a f) ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w (r + s) := by
  rw [elvQuotientMap_source]
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  have : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  have ha' : SKM.SYM.elvCoefficientQuotient D cutoff a ∈
      SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff r :=
    Submodule.mem_map_of_mem (f := ((SKM.SYM.elvCoefficientQuotient D cutoff).restrictScalars
      K).toLinearMap) ha
  exact BoxProdCoefficient.tmulHom_mem_homDegree (X := ELVOld.obj D Sc cutoff v)
    (Y := ELVOld.obj D Sc cutoff w) ha' hf

/-- A coefficient polynomial with complementary coefficient degrees is homogeneous over `R`. -/
theorem deformedCyclotomic_mem_degreeOver (j : I) (v : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D R)
    (hcoeff : ∀ a, c a ∈ SKM.SYM.coefficientDegreePartOver D sy 𝒜
      (2 * sy.d j * ((N : ℤ) - a.val))) :
    (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (j :: v) N c) ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (j :: v) (j :: v) (2 * sy.d j * N) := by
  change elvQuotientMap D Sc cutoff _ _ _ ∈ _
  unfold deformedCyclotomic
  rw [map_sum]
  apply Submodule.sum_mem
  intro a _
  have h := elvQuotientMap_source_mem_degreeOver D sy 𝒜 Sc hP cutoff (hcoeff a)
    (firstDotPower_mem_presentedPart D sy 𝒜 Sc j v a.val)
  have he : 2 * sy.d j * ((N : ℤ) - a.val) + 2 * sy.d j * a.val = 2 * sy.d j * N := by ring
  rw [he] at h
  exact h

/-- **The first-position cyclotomic relation over a graded base** has degree
`2 d_j cutoff_j`. -/
theorem ELVOld.relation_mem_degreeOver (j : I) (v : List I) :
    ELVOld.relation D Sc cutoff j v ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (j :: v) (j :: v) (2 * sy.d j * cutoff j) := by
  unfold ELVOld.relation
  split_ifs with hj
  · exact deformedCyclotomic_mem_degreeOver D sy 𝒜 Sc hP cutoff j v (cutoff j) _
      (SKM.SYM.elvMonicCoefficient_mem_coefficientDegreePartOver D sy 𝒜 ⟨j, hj⟩ (cutoff j))
  · have he : D.parity j = 0 :=
      (Supercategory.parity_eq_zero_or_one (D.parity j)).resolve_right hj
    exact deformedCyclotomic_mem_degreeOver D sy 𝒜 Sc hP cutoff j v (cutoff j) _
      (SKM.SYM.evenMonicCoefficient_mem_coefficientDegreePartOver D sy 𝒜 j he (cutoff j))

/-- **Homogeneity of the old cyclotomic ideal over a graded base.** Every homogeneous
component of an element of the two-sided old cyclotomic ideal lies in the ideal. -/
theorem ELVOld.ideal_dproj_mem_over {v w : List I} {f : ELVOld.hom D Sc cutoff v w}
    (hf : f ∈ ELVOld.ideal D Sc cutoff v w) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    dproj K n f ∈ ELVOld.ideal D Sc cutoff v w := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  let S : ∀ v w : List I, Set (ELVOld.hom D Sc cutoff v w) := fun v w => {f | ∃ j t,
    ∃ a : ELVOld.hom D Sc cutoff v (j :: t), ∃ b : ELVOld.hom D Sc cutoff (j :: t) w,
      a ≫ ELVOld.relation D Sc cutoff j t ≫ b = f}
  letI := degreeDecomposition K (ELVOld.obj D Sc cutoff v) (ELVOld.obj D Sc cutoff w)
  rw [dproj_apply]
  refine BasisGrading.decompose_mem_span 𝒜
    (GradedSupercategory.degree (R := K) (ELVOld.obj D Sc cutoff v) (ELVOld.obj D Sc cutoff w))
    (fun hr hy => smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr hy) (S := S v w)
    ?_ hf n
  rintro g ⟨j, t, a, b, rfl⟩ m
  rw [← dproj_apply]
  refine induction_on_degree (R := K) a (by simp) (fun r a ha => ?_)
    (fun a a' ha ha' => ?_)
  · refine induction_on_degree (R := K) b (by simp) (fun s b hb => ?_)
      (fun b b' hb hb' => ?_)
    · have hg := comp_mem_degree ha
        (comp_mem_degree (ELVOld.relation_mem_degreeOver D sy 𝒜 Sc hP cutoff j t) hb)
      by_cases h : r + (2 * sy.d j * cutoff j + s) = m
      · rw [← h, dproj_of_mem hg]
        exact Submodule.subset_span ⟨j, t, a, b, rfl⟩
      · rw [dproj_of_mem_ne hg h]
        exact Submodule.zero_mem _
    · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
  · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'

end OddMath.QuiverHecke
