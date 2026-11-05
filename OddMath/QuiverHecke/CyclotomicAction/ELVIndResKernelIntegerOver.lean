/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelInteger
import OddMath.Diagrams.GradedTensor

/-! # Integer degree on represented induction-restriction kernels over a graded base

Over a commutative `K`-algebra `R` graded by `𝒜`, let the source and target categories carry
`K`-linear degree decompositions compatible with homogeneous scalars of `R`. The represented
kernel is a balanced quotient of tensor products over `R` of two Hom modules. Its integer degree
is the `K`-span of the classes of pure tensors whose two Hom degrees add to the given integer, and
these parts form an internal direct sum (`IndResKernel.integerDegreeOver_internal`). The degree
projections are induced by the graded tensor projections of
`OddMath.Diagrams.GradedTensor`; the balancing relations are homogeneous.

For `K = R` with the trivial grading this is `IndResKernel.integerDegree`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory TensorProduct
open OddMath.Diagrams
attribute [local instance] Classical.propDecidable Classical.decEq
namespace OddMath.QuiverHecke.ELVOld.IndResKernel
universe u
variable {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  {C D : Type u} [Category.{u} C] [Preadditive C] [Linear K C] [Supercategory K C]
  [GradedSupercategory K C]
  [Category.{u} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [Linear K D] [∀ X Y : D, IsScalarTower K R (X ⟶ Y)] [Supercategory K D]
  [GradedSupercategory K D]
  (J : C ⥤ D) [J.Additive]
  (hJ : ∀ {X Y : C} {n : ℤ} {f : X ⟶ Y}, f ∈ degree (R := K) X Y n →
    J.map f ∈ degree (R := K) (J.obj X) (J.obj Y) n)
  (hD : ∀ {X Y : D} {a n : ℤ} {r : R} {f : X ⟶ Y}, r ∈ 𝒜 a →
    f ∈ degree (R := K) X Y n → r • f ∈ degree (R := K) X Y (a + n))

/-- The degree-`n` projection of a tensor product of two Hom modules over `R`. -/
def homTensorProj (X Y Z : D) (n : ℤ) :
    (Y ⟶ Z) ⊗[R] (X ⟶ Y) →ₗ[K] (Y ⟶ Z) ⊗[R] (X ⟶ Y) :=
  letI := degreeDecomposition K Y Z
  letI := degreeDecomposition K X Y
  { toFun := GradedTensor.proj 𝒜 (degree (R := K) Y Z) (degree (R := K) X Y)
      (fun hr hf => hD hr hf) (fun hr hf => hD hr hf) n
    map_add' := map_add _
    map_smul' := fun c y => GradedTensor.proj_smul 𝒜 _ _
      (fun hr hf => hD hr hf) (fun hr hf => hD hr hf) n c y }

omit [∀ X Y : D, IsScalarTower K R (X ⟶ Y)] in
/-- A homogeneous pure tensor is fixed or killed by the degree projection. -/
theorem homTensorProj_tmul (X Y Z : D) (n : ℤ) (g : Y ⟶ Z) (b : X ⟶ Y) {q r : ℤ}
    (hg : g ∈ degree (R := K) Y Z q) (hb : b ∈ degree (R := K) X Y r) :
    homTensorProj 𝒜 hD X Y Z n (g ⊗ₜ[R] b) = if q + r = n then g ⊗ₜ[R] b else 0 := by
  letI := degreeDecomposition K Y Z
  letI := degreeDecomposition K X Y
  change GradedTensor.proj 𝒜 (degree (R := K) Y Z) (degree (R := K) X Y)
    (fun hr hf => hD hr hf) (fun hr hf => hD hr hf) n (g ⊗ₜ[R] b) = _
  rw [GradedTensor.proj_tmul, GradedTensor.projBihom_of_mem_of_mem _ _ hg hb]
  by_cases hn : q + r = n
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn]

/-- Project a tensor summand onto its sum integer degree, then descend to the balanced
quotient. -/
def integerSummandOver (v t : D) (n : ℤ) (s : C) :
    (J.obj s ⟶ t) ⊗[R] (v ⟶ J.obj s) →ₗ[K] Component (k := R) J v t :=
  (BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s).restrictScalars K ∘ₗ
    homTensorProj 𝒜 hD v (J.obj s) t n

/-- Projecting a homogeneous tensor summand selects precisely its sum degree. -/
theorem integerSummandOver_homogeneous (v t : D) (n : ℤ) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := K) (J.obj s) t q)
    (hb : b ∈ degree (R := K) v (J.obj s) r) :
    integerSummandOver 𝒜 J hD v t n s (g ⊗ₜ[R] b) =
      if q + r = n then componentTensor (k := R) J v t s g b else 0 := by
  rw [integerSummandOver, LinearMap.comp_apply, homTensorProj_tmul 𝒜 hD v (J.obj s) t n g b hg hb]
  by_cases hn : q + r = n
  · rw [if_pos hn, if_pos hn]
    rfl
  · rw [if_neg hn, if_neg hn, map_zero]

include hJ in
private theorem integerSummandOver_balance_homogeneous (v t : D) (n : ℤ)
    {s s' : C} (f : s ⟶ s') (g : J.obj s' ⟶ t) (b : v ⟶ J.obj s)
    {p q r : ℤ} (hf : f ∈ degree (R := K) s s' p)
    (hg : g ∈ degree (R := K) (J.obj s') t q)
    (hb : b ∈ degree (R := K) v (J.obj s) r) :
    integerSummandOver 𝒜 J hD v t n s ((J.map f ≫ g) ⊗ₜ[R] b) =
      integerSummandOver 𝒜 J hD v t n s' (g ⊗ₜ[R] (b ≫ J.map f)) := by
  rw [integerSummandOver_homogeneous 𝒜 J hD v t n s (J.map f ≫ g) b
      (comp_mem_degree (hJ hf) hg) hb,
    integerSummandOver_homogeneous 𝒜 J hD v t n s' g (b ≫ J.map f)
      hg (comp_mem_degree hb (hJ hf))]
  by_cases h : p + q + r = n
  · rw [if_pos h, if_pos (by omega)]
    exact BalancedInduction.balance J (J ⋙ homModule (k := R) v) f g b
  · rw [if_neg h, if_neg (by omega)]

include hJ in
/-- Integer projection respects balancing by every source arrow, including sums of different
integer degrees. -/
theorem integerSummandOver_balance (v t : D) (n : ℤ) (s s' : C)
    (f : s ⟶ s') (g : J.obj s' ⟶ t) (b : v ⟶ J.obj s) :
    integerSummandOver 𝒜 J hD v t n s ((J.map f ≫ g) ⊗ₜ[R] b) =
      integerSummandOver 𝒜 J hD v t n s' (g ⊗ₜ[R] (b ≫ J.map f)) := by
  refine induction_on_degree (R := K) f ?_ (fun p f hf => ?_) ?_
  · simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero, zero_tmul, tmul_zero,
      map_zero]
  · refine induction_on_degree (R := K) g ?_ (fun q g hg => ?_) ?_
    · simp only [Limits.comp_zero, zero_tmul, map_zero]
    · refine induction_on_degree (R := K) b ?_ (fun r b hb => ?_) ?_
      · simp only [Limits.zero_comp, zero_tmul, tmul_zero, map_zero]
      · exact integerSummandOver_balance_homogeneous 𝒜 J hJ hD v t n f g b hf hg hb
      · intro b b' hb hb'
        simpa only [Preadditive.add_comp, tmul_add, map_add] using congrArg₂ (· + ·) hb hb'
    · intro g g' hg hg'
      simpa only [Preadditive.comp_add, add_tmul, map_add] using congrArg₂ (· + ·) hg hg'
  · intro f f' hf hf'
    simpa only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      add_tmul, tmul_add, map_add] using congrArg₂ (· + ·) hf hf'

/-- The summand projections, on the unbalanced direct sum. -/
def rawProjectionOver (v t : D) (n : ℤ) :
    BalancedInduction.Raw J (J ⋙ homModule (k := R) v) t →ₗ[K] Component (k := R) J v t :=
  DirectSum.toModule K C _ fun s => integerSummandOver 𝒜 J hD v t n s

theorem rawProjectionOver_rawTensor (v t : D) (n : ℤ) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) :
    rawProjectionOver 𝒜 J hD v t n
        (BalancedInduction.rawTensor J (J ⋙ homModule (k := R) v) s g b) =
      integerSummandOver 𝒜 J hD v t n s (g ⊗ₜ[R] b) :=
  DirectSum.toModule_lof K s _

include hJ in
/-- The summand projections vanish on the balancing relations, which form an `R`-submodule
generated by homogeneous-scalar-stable relations. -/
theorem relations_le_ker_rawProjectionOver (v t : D) (n : ℤ) :
    (BalancedInduction.relations J (J ⋙ homModule (k := R) v) t).restrictScalars K ≤
      LinearMap.ker (rawProjectionOver 𝒜 J hD v t n) := by
  have key : ∀ x ∈ BalancedInduction.relations J (J ⋙ homModule (k := R) v) t, ∀ c : R,
      rawProjectionOver 𝒜 J hD v t n (c • x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, s', f, h, m, rfl⟩ := hx
      intro c
      have e1 : c • BalancedInduction.rawTensor J (J ⋙ homModule (k := R) v) s (J.map f ≫ h) m =
          BalancedInduction.rawTensor J (J ⋙ homModule (k := R) v) s (J.map f ≫ c • h) m := by
        rw [Linear.comp_smul, BalancedInduction.rawTensor, BalancedInduction.rawTensor,
          ← TensorProduct.smul_tmul', map_smul]
      have e2 : c • BalancedInduction.rawTensor J (J ⋙ homModule (k := R) v) s' h
            ((J ⋙ homModule (k := R) v).map f m) =
          BalancedInduction.rawTensor J (J ⋙ homModule (k := R) v) s' (c • h)
            ((J ⋙ homModule (k := R) v).map f m) := by
        rw [BalancedInduction.rawTensor, BalancedInduction.rawTensor,
          ← TensorProduct.smul_tmul', map_smul]
      rw [smul_sub, e1, e2, map_sub, rawProjectionOver_rawTensor, rawProjectionOver_rawTensor,
        sub_eq_zero]
      exact integerSummandOver_balance 𝒜 J hJ hD v t n s s' f (c • h) m
    | zero => intro c; rw [smul_zero, map_zero]
    | add x y _ _ hx hy => intro c; rw [smul_add, map_add, hx, hy, add_zero]
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx (c * a)
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  simpa only [one_smul] using key x hx 1

/-- Integer projection on the represented balanced kernel, as a `K`-linear map. -/
def integerProjectionOver (v t : D) (n : ℤ) :
    Component (k := R) J v t →ₗ[K] Component (k := R) J v t :=
  ((BalancedInduction.relations J (J ⋙ homModule (k := R) v) t).restrictScalars K).liftQ
      (rawProjectionOver 𝒜 J hD v t n) (relations_le_ker_rawProjectionOver 𝒜 J hJ hD v t n) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv K
      (BalancedInduction.relations J (J ⋙ homModule (k := R) v) t)).symm.toLinearMap

theorem integerProjectionOver_inclusion (v t : D) (n : ℤ) (s : C)
    (y : (J.obj s ⟶ t) ⊗[R] (v ⟶ J.obj s)) :
    integerProjectionOver 𝒜 J hJ hD v t n
        (BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s y) =
      integerSummandOver 𝒜 J hD v t n s y := by
  change ((BalancedInduction.relations J (J ⋙ homModule (k := R) v) t).restrictScalars K).liftQ
      (rawProjectionOver 𝒜 J hD v t n) _
      ((Submodule.Quotient.restrictScalarsEquiv K _).symm
        (Submodule.Quotient.mk (DirectSum.lof R C _ s y))) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  exact DirectSum.toModule_lof K s y

/-- A homogeneous pure tensor has the sum degree of its two Hom factors. -/
theorem integerProjectionOver_tensor (v t : D) (n : ℤ) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := K) (J.obj s) t q)
    (hb : b ∈ degree (R := K) v (J.obj s) r) :
    integerProjectionOver 𝒜 J hJ hD v t n (componentTensor (k := R) J v t s g b) =
      if q + r = n then componentTensor (k := R) J v t s g b else 0 := by
  rw [show componentTensor (k := R) J v t s g b =
      BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s (g ⊗ₜ[R] b) from rfl,
    integerProjectionOver_inclusion]
  exact integerSummandOver_homogeneous 𝒜 J hD v t n s g b hg hb

omit [GradedAlgebra 𝒜] [J.Additive] in
/-- The integer degree: the `K`-span of the classes of pure tensors whose two Hom degrees add
to the given integer. -/
def integerDegreeOver (v t : D) (n : ℤ) : Submodule K (Component (k := R) J v t) :=
  ⨆ s : C, (GradedTensor.part (R := R) (degree (R := K) (J.obj s) t)
      (degree (R := K) v (J.obj s)) n).map
    ((BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s).restrictScalars K)

omit [GradedAlgebra 𝒜] [J.Additive] in
/-- The class of a homogeneous pure tensor has its sum degree. -/
theorem componentTensor_mem_integerDegreeOver (v t : D) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := K) (J.obj s) t q)
    (hb : b ∈ degree (R := K) v (J.obj s) r) :
    componentTensor (k := R) J v t s g b ∈ integerDegreeOver J v t (q + r) :=
  Submodule.mem_iSup_of_mem s (Submodule.mem_map_of_mem (GradedTensor.tmul_mem_part hg hb))

omit [GradedAlgebra 𝒜] [J.Additive] in
/-- Check a degree-submodule containment on its homogeneous pure tensors. -/
theorem integerDegreeOver_le_iff (v t : D) (n : ℤ)
    (S : Submodule K (Component (k := R) J v t)) :
    integerDegreeOver J v t n ≤ S ↔
    ∀ (s : C) (q r : ℤ), q + r = n →
      ∀ g ∈ degree (R := K) (J.obj s) t q,
      ∀ b ∈ degree (R := K) v (J.obj s) r,
        componentTensor (k := R) J v t s g b ∈ S := by
  constructor
  · intro h s q r hqr g hg b hb
    exact h (hqr ▸ componentTensor_mem_integerDegreeOver J v t s g b hg hb)
  · intro h
    refine iSup_le fun s => (Submodule.map_le_iff_le_comap).2 ?_
    refine Submodule.span_le.2 ?_
    rintro y ⟨q, r, hqr, g, hg, b, hb, rfl⟩
    exact h s q r hqr g hg b hb

/-- Integer projection is the identity on its prescribed part and zero on every other part. -/
theorem integerProjectionOver_of_mem (v t : D) {m n : ℤ}
    {x : Component (k := R) J v t} (hx : x ∈ integerDegreeOver J v t m) :
    integerProjectionOver 𝒜 J hJ hD v t n x = if m = n then x else 0 := by
  let Q : Component (k := R) J v t →ₗ[K] Component (k := R) J v t :=
    if m = n then LinearMap.id else 0
  have hle : integerDegreeOver J v t m ≤
      (integerProjectionOver 𝒜 J hJ hD v t n).eqLocus Q := by
    apply (integerDegreeOver_le_iff J v t m _).2
    intro s q r hqr g hg b hb
    change integerProjectionOver 𝒜 J hJ hD v t n (componentTensor (k := R) J v t s g b) =
      Q (componentTensor (k := R) J v t s g b)
    rw [integerProjectionOver_tensor 𝒜 J hJ hD v t n s g b hg hb, hqr]
    by_cases h : m = n
    · simp only [Q, if_pos h, LinearMap.id_apply]
    · simp only [Q, if_neg h, LinearMap.zero_apply]
  have h := hle hx
  by_cases hmn : m = n
  · simpa only [LinearMap.mem_eqLocus, Q, if_pos hmn, LinearMap.id_apply] using h
  · simpa only [LinearMap.mem_eqLocus, Q, if_neg hmn, LinearMap.zero_apply] using h

omit [GradedAlgebra 𝒜] in
/-- Every represented balanced tensor is a finite sum of integer-homogeneous classes. -/
theorem iSup_integerDegreeOver_eq_top (v t : D) :
    (⨆ n : ℤ, integerDegreeOver J v t n) = ⊤ := by
  let S : Submodule K (Component (k := R) J v t) := ⨆ n : ℤ, integerDegreeOver J v t n
  have ht (s : C) (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) :
      componentTensor (k := R) J v t s g b ∈ S := by
    refine induction_on_degree (R := K) g ?_ (fun q g hg => ?_) ?_
    · simp [componentTensor]
    · refine induction_on_degree (R := K) b ?_ (fun r b hb => ?_) ?_
      · simp [componentTensor]
      · exact Submodule.mem_iSup_of_mem (q + r)
          (componentTensor_mem_integerDegreeOver J v t s g b hg hb)
      · intro b b' hb hb'
        simpa only [componentTensor, BalancedInduction.tensor, tmul_add, map_add] using
          Submodule.add_mem S hb hb'
    · intro g g' hg hg'
      simpa only [componentTensor, BalancedInduction.tensor_add_left] using
        Submodule.add_mem S hg hg'
  have hs (s : C) (y : (J.obj s ⟶ t) ⊗[R] (v ⟶ J.obj s)) :
      BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s y ∈ S := by
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem S
    | tmul g b => exact ht s g b
    | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
  apply top_unique
  rintro x -
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction x using DirectSum.induction_on with
    | zero => exact zero_mem S
    | of s y => exact hs s y
    | add x y hx hy => rw [Submodule.Quotient.mk_add]; exact add_mem hx hy

/-- The integer degrees form an internal direct sum on the represented balanced kernel. -/
theorem integerDegreeOver_internal (v t : D) :
    DirectSum.IsInternal (integerDegreeOver (K := K) J v t) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · refine iSupIndep_of_projections _ (integerProjectionOver 𝒜 J hJ hD v t)
      (fun n => ?_) (fun n m hmn => ?_)
    · intro x hx
      exact (integerProjectionOver_of_mem 𝒜 J hJ hD v t hx).trans (if_pos rfl)
    · intro x hx
      exact (integerProjectionOver_of_mem 𝒜 J hJ hD v t hx).trans (if_neg hmn)
  · exact iSup_integerDegreeOver_eq_top J v t

/-- Integer projection has its image in the prescribed part. -/
theorem integerProjectionOver_mem (v t : D) (n : ℤ) (x : Component (k := R) J v t) :
    integerProjectionOver 𝒜 J hJ hD v t n x ∈ integerDegreeOver J v t n := by
  have hle : (⨆ m : ℤ, integerDegreeOver (K := K) J v t m) ≤
      (integerDegreeOver J v t n).comap (integerProjectionOver 𝒜 J hJ hD v t n) := by
    refine iSup_le fun m => ?_
    intro y hy
    change integerProjectionOver 𝒜 J hJ hD v t n y ∈ integerDegreeOver J v t n
    rw [integerProjectionOver_of_mem 𝒜 J hJ hD v t hy]
    by_cases h : m = n
    · subst m
      simpa using hy
    · simp only [if_neg h, Submodule.zero_mem]
  rw [iSup_integerDegreeOver_eq_top J v t] at hle
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule K _))

end OddMath.QuiverHecke.ELVOld.IndResKernel
