import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelGrading
import StringDiagrams.Super.GSVecMonoidal
import StringDiagrams.Super.BoxProductGraded

/-! # Integer degree on represented induction-restriction kernels

The kernel used by the prescribed finite unit/cap matrices is the literal
balanced quotient of two Hom factors. Its integer degree is their sum.
This construction concerns represented coefficient kernels and does not
grade Homs between arbitrary ungraded modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory TensorProduct
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld.IndResKernel
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [GradedSupercategory k C]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D] [GradedSupercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsGradedSuperfunctor k J]

/-- Project a tensor summand onto its sum integer degree, then descend
to the existing balanced quotient. -/
def integerSummand (v t : D) (n : ℤ) (s : C) :
    (J.obj s ⟶ t) ⊗[k] (v ⟶ J.obj s) →ₗ[k] Component (k := k) J v t :=
  BalancedInduction.inclusion J (J ⋙ homModule (k := k) v) t s ∘ₗ
    (homGSpace k D (J.obj s) t).tensorProj (homGSpace k D v (J.obj s)) n

set_option backward.dsimp.instances true in
omit [Preadditive C] [Linear k C] [Supercategory k C] [GradedSupercategory k C]
  [J.Additive] [J.Linear k] [IsGradedSuperfunctor k J] in
/-- Projecting a homogeneous tensor summand selects precisely its sum degree. -/
theorem integerSummand_homogeneous (v t : D) (n : ℤ) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := k) (J.obj s) t q)
    (hb : b ∈ degree (R := k) v (J.obj s) r) :
    integerSummand J v t n s (g ⊗ₜ[k] b) =
      if q + r = n then componentTensor (k := k) J v t s g b else 0 := by
  let L : (J.obj s ⟶ t) ⊗[k] (v ⟶ J.obj s) →ₗ[k] Component (k := k) J v t :=
    BalancedInduction.inclusion J (J ⋙ homModule (k := k) v) t s
  have h := congrArg L (GradedSuperspace.tensorProj_tmul
    (homGSpace k D (J.obj s) t) (homGSpace k D v (J.obj s)) n q r hg hb)
  by_cases hn : q + r = n
  · simp only [ite_eq_left hn] at h ⊢
    dsimp only [L, integerSummand, componentTensor, BalancedInduction.tensor,
      LinearMap.comp_apply, homGSpace, homSVec, homModule, Functor.comp_obj] at h ⊢
    convert! h using 1
  · simp only [ite_eq_right hn, map_zero] at h ⊢
    dsimp only [L, integerSummand, LinearMap.comp_apply, homGSpace, homSVec,
      homModule, Functor.comp_obj] at h ⊢
    convert! h using 1

private theorem integerSummand_balance_homogeneous (v t : D) (n : ℤ)
    {s s' : C} (f : s ⟶ s') (g : J.obj s' ⟶ t) (b : v ⟶ J.obj s)
    {p q r : ℤ} (hf : f ∈ degree (R := k) s s' p)
    (hg : g ∈ degree (R := k) (J.obj s') t q)
    (hb : b ∈ degree (R := k) v (J.obj s) r) :
    integerSummand J v t n s ((J.map f ≫ g) ⊗ₜ[k] b) =
      integerSummand J v t n s' (g ⊗ₜ[k] (b ≫ J.map f)) := by
  rw [integerSummand_homogeneous J v t n s (J.map f ≫ g) b
      (comp_mem_degree (map_mem_degree J hf) hg) hb,
    integerSummand_homogeneous J v t n s' g (b ≫ J.map f)
      hg (comp_mem_degree hb (map_mem_degree J hf))]
  by_cases h : p + q + r = n
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    exact BalancedInduction.balance J (J ⋙ homModule (k := k) v) f g b
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- Integer projection respects balancing by every source arrow,
including sums of different integer degrees. -/
theorem integerSummand_balance (v t : D) (n : ℤ) (s s' : C)
    (f : s ⟶ s') (g : J.obj s' ⟶ t) (b : v ⟶ J.obj s) :
    integerSummand J v t n s ((J.map f ≫ g) ⊗ₜ[k] b) =
      integerSummand J v t n s' (g ⊗ₜ[k] (b ≫ J.map f)) := by
  refine induction_on_degree (R := k) f ?_ (fun p f hf => ?_) ?_
  · simp [integerSummand]
  · refine induction_on_degree (R := k) g ?_ (fun q g hg => ?_) ?_
    · simp [integerSummand]
    · refine induction_on_degree (R := k) b ?_ (fun r b hb => ?_) ?_
      · simp [integerSummand]
      · exact integerSummand_balance_homogeneous J v t n f g b hf hg hb
      · intro b b' hb hb'
        simpa only [Preadditive.add_comp, tmul_add, map_add] using congrArg₂ (· + ·) hb hb'
    · intro g g' hg hg'
      simpa only [Preadditive.comp_add, add_tmul, map_add] using congrArg₂ (· + ·) hg hg'
  · intro f f' hf hf'
    simpa only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      add_tmul, tmul_add, map_add] using congrArg₂ (· + ·) hf hf'

/-- Integer projection on the actual represented balanced kernel. -/
def integerProjection (v t : D) (n : ℤ) :
    Component (k := k) J v t →ₗ[k] Component (k := k) J v t :=
  BalancedInduction.lift J (J ⋙ homModule (k := k) v) t (integerSummand J v t n)
    (integerSummand_balance J v t n)

/-- A homogeneous pure tensor has the sum degree of its two Hom factors. -/
theorem integerProjection_tensor (v t : D) (n : ℤ) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := k) (J.obj s) t q)
    (hb : b ∈ degree (R := k) v (J.obj s) r) :
    integerProjection J v t n (componentTensor (k := k) J v t s g b) =
      if q + r = n then componentTensor (k := k) J v t s g b else 0 := by
  dsimp only [integerProjection, componentTensor]
  rw [BalancedInduction.lift_tensor]
  exact integerSummand_homogeneous J v t n s g b hg hb

/-- The intrinsic integer degree consists of sums of balanced tensors
whose two represented Hom degrees add to the given integer. -/
def integerDegree (v t : D) (n : ℤ) : Submodule k (Component (k := k) J v t) :=
  ⨆ s : C, ((homGSpace k D (J.obj s) t).tensorDeg (homGSpace k D v (J.obj s)) n).map
    (BalancedInduction.inclusion J (J ⋙ homModule (k := k) v) t s)

omit [Preadditive C] [Linear k C] [Supercategory k C] [GradedSupercategory k C]
  [J.Additive] [J.Linear k] [IsGradedSuperfunctor k J] in
/-- The class of a homogeneous pure tensor has its sum degree. -/
theorem componentTensor_mem_integerDegree (v t : D) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := k) (J.obj s) t q)
    (hb : b ∈ degree (R := k) v (J.obj s) r) :
    componentTensor (k := k) J v t s g b ∈ integerDegree (k := k) J v t (q + r) :=
  Submodule.mem_iSup_of_mem s (Submodule.mem_map_of_mem
    (GradedSuperspace.tmul_mem_tensorDeg (homGSpace k D (J.obj s) t)
      (homGSpace k D v (J.obj s)) hg hb))

omit [Preadditive C] [Linear k C] [Supercategory k C] [GradedSupercategory k C]
  [J.Additive] [J.Linear k] [IsGradedSuperfunctor k J] in
/-- Check a degree-submodule containment on its homogeneous pure tensors. -/
theorem integerDegree_le_iff (v t : D) (n : ℤ) (S : Submodule k (Component (k := k) J v t)) :
    integerDegree (k := k) J v t n ≤ S ↔
    ∀ (s : C) (q r : ℤ), q + r = n →
      ∀ g ∈ degree (R := k) (J.obj s) t q,
      ∀ b ∈ degree (R := k) v (J.obj s) r,
        componentTensor (k := k) J v t s g b ∈ S := by
  constructor
  · intro h s q r hqr g hg b hb
    exact h (hqr ▸ componentTensor_mem_integerDegree (k := k) J v t s g b hg hb)
  · intro h
    refine iSup_le fun s => (Submodule.map_le_iff_le_comap).2 ?_
    apply (GradedSuperspace.tensorDeg_le_iff (homGSpace k D (J.obj s) t)
      (homGSpace k D v (J.obj s))).2
    intro q r hqr g hg b hb
    exact h s q r hqr g hg b hb

/-- Integer projection is identity on its prescribed part and zero on
every other intrinsic degree part. -/
theorem integerProjection_of_mem (v t : D) {m n : ℤ}
    {x : Component (k := k) J v t} (hx : x ∈ integerDegree (k := k) J v t m) :
    integerProjection J v t n x = if m = n then x else 0 := by
  let Q : Component (k := k) J v t →ₗ[k] Component (k := k) J v t :=
    if m = n then LinearMap.id else 0
  have hle : integerDegree (k := k) J v t m ≤ (integerProjection J v t n).eqLocus Q := by
    apply (integerDegree_le_iff J v t m _).2
    intro s q r hqr g hg b hb
    change integerProjection J v t n (componentTensor (k := k) J v t s g b) =
      Q (componentTensor (k := k) J v t s g b)
    rw [integerProjection_tensor J v t n s g b hg hb, hqr]
    by_cases h : m = n <;> simp only [Q, h, ↓reduceIte, LinearMap.id_apply, LinearMap.zero_apply]
  have h := hle hx
  by_cases hmn : m = n
  · simpa only [LinearMap.mem_eqLocus, Q, ite_eq_left hmn, LinearMap.id_apply] using h
  · simpa only [LinearMap.mem_eqLocus, Q, ite_eq_right hmn, LinearMap.zero_apply] using h

omit [Preadditive C] [Linear k C] [Supercategory k C] [GradedSupercategory k C]
  [J.Additive] [J.Linear k] [IsGradedSuperfunctor k J] in
/-- Every represented balanced tensor is a finite sum of intrinsic
integer-homogeneous classes. -/
theorem iSup_integerDegree_eq_top (v t : D) : (⨆ n : ℤ, integerDegree (k := k) J v t n) = ⊤ := by
  let S : Submodule k (Component (k := k) J v t) := ⨆ n : ℤ, integerDegree (k := k) J v t n
  have ht (s : C) (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) :
      componentTensor (k := k) J v t s g b ∈ S := by
    refine induction_on_degree (R := k) g ?_ (fun q g hg => ?_) ?_
    · simp [componentTensor]
    · refine induction_on_degree (R := k) b ?_ (fun r b hb => ?_) ?_
      · simp [componentTensor]
      · exact Submodule.mem_iSup_of_mem (q + r) (componentTensor_mem_integerDegree (k := k) J v t s g b hg hb)
      · intro b b' hb hb'
        simpa only [componentTensor, BalancedInduction.tensor, tmul_add, map_add] using Submodule.add_mem S hb hb'
    · intro g g' hg hg'
      simpa only [componentTensor, BalancedInduction.tensor_add_left] using Submodule.add_mem S hg hg'
  have hq : S.mkQ = (0 : Component (k := k) J v t →ₗ[k] (Component (k := k) J v t ⧸ S)) := by
    apply BalancedInduction.hom_ext
    intro s g b
    change S.mkQ (componentTensor (k := k) J v t s g b) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (ht s g b)
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero S).mp (LinearMap.congr_fun hq x)

/-- Integer projection has its image in the prescribed intrinsic part. -/
theorem integerProjection_mem (v t : D) (n : ℤ) (x : Component (k := k) J v t) :
    integerProjection J v t n x ∈ integerDegree (k := k) J v t n := by
  have hle : (⨆ m : ℤ, integerDegree (k := k) J v t m) ≤
      (integerDegree (k := k) J v t n).comap (integerProjection J v t n) := by
    refine iSup_le fun m => ?_
    intro y hy
    change integerProjection J v t n y ∈ integerDegree (k := k) J v t n
    rw [integerProjection_of_mem J v t hy]
    by_cases h : m = n
    · subst m
      simpa using hy
    · simp only [ite_eq_right h, Submodule.zero_mem]
  rw [iSup_integerDegree_eq_top J v t] at hle
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule k _))

end OddMath.QuiverHecke.ELVOld.IndResKernel
