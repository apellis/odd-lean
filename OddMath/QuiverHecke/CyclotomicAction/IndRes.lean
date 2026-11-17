import StringDiagrams.Super.GSVecMonoidal
import StringDiagrams.Super.BoxProductGraded
import OddMath.Diagrams.GradedTensor
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree

/-!
# Ind res

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Grading of the induction-restriction coefficient kernel

The concrete ordinary-right grading input for the kernel tensor step in
DeformedMatrixComparison, section 4. The coefficient space is the existing
balanced-induction superspace. Precomposition by a homogeneous source arrow
has that arrow's parity, including the full coefficient parity.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.IndResKernel
universe u
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] [Supercategory k D]

instance homModule_additive (v : D) : (homModule (k := k) v).Additive where
  map_add {w z} f g := by
    apply LinearMap.ext
    intro b
    exact Preadditive.comp_add v w z b f g

instance homModule_linear (v : D) : (homModule (k := k) v).Linear k where
  map_smul {w z} f r := by
    apply LinearMap.ext
    intro b
    exact Linear.comp_smul v w z b r f

instance homModule_super (v : D) : IsSuperfunctor k (homModule (k := k) v) where
  map_mem := by
    intro w z p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q b hb
    change b ∈ (homSVec k D v w).part q at hb
    change b ≫ f ∈ (homSVec k D v z).part (q + p)
    exact (mem_homSVec_part_iff k).2
      (comp_mem ((mem_homSVec_part_iff k).1 hb) hf)

variable (J : C ⥤ D)

theorem precompose_add {v w : D} (a b : v ⟶ w) (t : D) :
    precompose (k := k) J (a + b) t =
      precompose (k := k) J a t + precompose (k := k) J b t := by
  apply BalancedInduction.hom_ext
  intro s g c
  change precompose (k := k) J (a + b) t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) w) s g c) =
    precompose (k := k) J a t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) w) s g c) +
    precompose (k := k) J b t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) w) s g c)
  rw [precompose_tensor, precompose_tensor, precompose_tensor, Preadditive.add_comp,
    BalancedInduction.tensor_add_right]

instance kernel_additive (t : D) : (kernel (k := k) J t).Additive where
  map_add {v w} a b := by
    apply ModuleCat.hom_ext
    change precompose (k := k) J (a.unop + b.unop) t =
      precompose (k := k) J a.unop t + precompose (k := k) J b.unop t
    exact precompose_add J a.unop b.unop t

/-- A balanced tensor with the coefficient bound as a raw category arrow. -/
def componentTensor (v t : D) (s : C) (g : J.obj s ⟶ t)
    (b : v ⟶ J.obj s) : Component (k := k) J v t :=
  BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b

@[simp] theorem precompose_componentTensor {v w : D} (a : v ⟶ w) (t : D)
    (s : C) (g : J.obj s ⟶ t) (b : w ⟶ J.obj s) :
    precompose (k := k) J a t (componentTensor (k := k) J w t s g b) =
      componentTensor (k := k) J v t s g (a ≫ b) :=
  precompose_tensor J a t s g b

variable [Preadditive C] [Linear k C] [Supercategory k C]
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]

end OddMath.QuiverHecke.ELV.IndResKernel
end

end

section

/-! # Integer degree on represented induction-restriction kernels

The kernel used by the prescribed finite unit/cap matrices is the literal
balanced quotient of two Hom factors. Its integer degree is their sum.
This construction concerns represented coefficient kernels and does not
grade Homs between arbitrary ungraded modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory TensorProduct
open scoped Classical
namespace OddMath.QuiverHecke.ELV.IndResKernel
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

end OddMath.QuiverHecke.ELV.IndResKernel
end

end

section

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
-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory TensorProduct
open OddMath.Diagrams
attribute [local instance] Classical.propDecidable Classical.decEq
namespace OddMath.QuiverHecke.ELV.IndResKernel
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

omit [Supercategory R D] in
/-- A homogeneous pure tensor is fixed or killed by the degree projection. -/
theorem homTensorProj_tmul (X Y Z : D) (n : ℤ) (g : Y ⟶ Z) (b : X ⟶ Y) {q r : ℤ}
    (hg : g ∈ degree (R := K) Y Z q) (hb : b ∈ degree (R := K) X Y r) :
    homTensorProj 𝒜 hD X Y Z n (g ⊗ₜ[R] b) = if q + r = n then g ⊗ₜ[R] b else 0 := by
  letI := degreeDecomposition K Y Z
  letI := degreeDecomposition K X Y
  change GradedTensor.proj 𝒜 (degree (R := K) Y Z) (degree (R := K) X Y)
    (fun hr hf => hD hr hf) (fun hr hf => hD hr hf) n (g ⊗ₜ[R] b) = _
  rw [GradedTensor.proj_tmul, GradedTensor.projBihom_of_mem_of_mem _ _ hg hb]

/-- Project a tensor summand onto its sum integer degree, then descend to the balanced
quotient. -/
def integerSummandOver (v t : D) (n : ℤ) (s : C) :
    (J.obj s ⟶ t) ⊗[R] (v ⟶ J.obj s) →ₗ[K] Component (k := R) J v t :=
  (BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s).restrictScalars K ∘ₗ
    homTensorProj 𝒜 hD v (J.obj s) t n

omit [Preadditive C] [Linear K C] [Supercategory K C] [GradedSupercategory K C] [J.Additive] in
/-- Projecting a homogeneous tensor summand selects precisely its sum degree. -/
theorem integerSummandOver_homogeneous (v t : D) (n : ℤ) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := K) (J.obj s) t q)
    (hb : b ∈ degree (R := K) v (J.obj s) r) :
    integerSummandOver 𝒜 J hD v t n s (g ⊗ₜ[R] b) =
      if q + r = n then componentTensor (k := R) J v t s g b else 0 := by
  have h := homTensorProj_tmul 𝒜 hD v (J.obj s) t n g b hg hb
  change BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s
      (homTensorProj 𝒜 hD v (J.obj s) t n (g ⊗ₜ[R] b)) = _
  rw [h]
  by_cases hn : q + r = n
  · rw [ite_eq_left hn, ite_eq_left hn]
    rfl
  · rw [ite_eq_right hn, ite_eq_right hn, map_zero]

omit [J.Additive] in
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
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    exact BalancedInduction.balance J (J ⋙ homModule (k := R) v) f g b
  · rw [ite_eq_right h, ite_eq_right (by omega)]

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
      · simp only [Limits.zero_comp, tmul_zero, map_zero]
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

omit [Preadditive C] [Linear K C] [Supercategory K C] [GradedSupercategory K C] [J.Additive] in
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
          BalancedInduction.rawTensor J (J ⋙ homModule (k := R) v) s (J.map f ≫ (c • h)) m := by
        rw [Linear.comp_smul (R := R), BalancedInduction.rawTensor, BalancedInduction.rawTensor,
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
  simpa only [one_smul, LinearMap.mem_ker] using key x hx 1

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
      (rawProjectionOver 𝒜 J hD v t n) (relations_le_ker_rawProjectionOver 𝒜 J hJ hD v t n)
      ((Submodule.Quotient.restrictScalarsEquiv K _).symm
        (Submodule.Quotient.mk (DirectSum.lof R C _ s y))) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  exact DirectSum.toModule_lof K s _

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

omit [GradedAlgebra 𝒜] [J.Additive] [Preadditive C] [Linear K C] [Supercategory K C]
  [GradedSupercategory K C] in
/-- The class of a homogeneous pure tensor has its sum degree. -/
theorem componentTensor_mem_integerDegreeOver (v t : D) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) {q r : ℤ}
    (hg : g ∈ degree (R := K) (J.obj s) t q)
    (hb : b ∈ degree (R := K) v (J.obj s) r) :
    componentTensor (k := R) J v t s g b ∈ integerDegreeOver (K := K) (R := R) J v t (q + r) :=
  Submodule.mem_iSup_of_mem s (Submodule.mem_map_of_mem (GradedTensor.tmul_mem_part hg hb))

omit [GradedAlgebra 𝒜] [J.Additive] [Preadditive C] [Linear K C] [Supercategory K C]
  [GradedSupercategory K C] in
/-- Check a degree-submodule containment on its homogeneous pure tensors. -/
theorem integerDegreeOver_le_iff (v t : D) (n : ℤ)
    (S : Submodule K (Component (k := R) J v t)) :
    integerDegreeOver (K := K) (R := R) J v t n ≤ S ↔
    ∀ (s : C) (q r : ℤ), q + r = n →
      ∀ g ∈ degree (R := K) (J.obj s) t q,
      ∀ b ∈ degree (R := K) v (J.obj s) r,
        componentTensor (k := R) J v t s g b ∈ S := by
  constructor
  · intro h s q r hqr g hg b hb
    exact h (hqr ▸ componentTensor_mem_integerDegreeOver (K := K) (R := R) J v t s g b hg hb)
  · intro h
    refine iSup_le fun s => (Submodule.map_le_iff_le_comap).2 ?_
    refine Submodule.span_le.2 ?_
    rintro y ⟨q, r, hqr, g, hg, b, hb, rfl⟩
    exact h s q r hqr g hg b hb

/-- Integer projection is the identity on its prescribed part and zero on every other part. -/
theorem integerProjectionOver_of_mem (v t : D) {m n : ℤ}
    {x : Component (k := R) J v t} (hx : x ∈ integerDegreeOver (K := K) (R := R) J v t m) :
    integerProjectionOver 𝒜 J hJ hD v t n x = if m = n then x else 0 := by
  let Q : Component (k := R) J v t →ₗ[K] Component (k := R) J v t :=
    if m = n then LinearMap.id else 0
  have hle : integerDegreeOver (K := K) (R := R) J v t m ≤
      (integerProjectionOver 𝒜 J hJ hD v t n).eqLocus Q := by
    apply (integerDegreeOver_le_iff (K := K) (R := R) J v t m _).2
    intro s q r hqr g hg b hb
    change integerProjectionOver 𝒜 J hJ hD v t n (componentTensor (k := R) J v t s g b) =
      Q (componentTensor (k := R) J v t s g b)
    rw [integerProjectionOver_tensor 𝒜 J hJ hD v t n s g b hg hb, hqr]
    by_cases h : m = n
    · simp only [Q, ite_eq_left h, LinearMap.id_apply]
    · simp only [Q, ite_eq_right h, LinearMap.zero_apply]
  have h := hle hx
  by_cases hmn : m = n
  · simpa only [LinearMap.mem_eqLocus, Q, ite_eq_left hmn, LinearMap.id_apply] using h
  · simpa only [LinearMap.mem_eqLocus, Q, ite_eq_right hmn, LinearMap.zero_apply] using h

omit [GradedAlgebra 𝒜] [J.Additive] [Preadditive C] [Linear K C] [Supercategory K C]
  [GradedSupercategory K C] in
/-- Every represented balanced tensor is a finite sum of integer-homogeneous classes. -/
theorem iSup_integerDegreeOver_eq_top (v t : D) :
    (⨆ n : ℤ, integerDegreeOver (K := K) (R := R) J v t n) = ⊤ := by
  let S : Submodule K (Component (k := R) J v t) :=
    ⨆ n : ℤ, integerDegreeOver (K := K) (R := R) J v t n
  have ht (s : C) (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) :
      componentTensor (k := R) J v t s g b ∈ S := by
    refine induction_on_degree (R := K) g ?_ (fun q g hg => ?_) ?_
    · simp [componentTensor]
    · refine induction_on_degree (R := K) b ?_ (fun r b hb => ?_) ?_
      · simp [componentTensor]
      · exact Submodule.mem_iSup_of_mem (q + r)
          (componentTensor_mem_integerDegreeOver (K := K) (R := R) J v t s g b hg hb)
      · intro b b' hb hb'
        simpa only [componentTensor, BalancedInduction.tensor, tmul_add, map_add] using
          Submodule.add_mem S hb hb'
    · intro g g' hg hg'
      simpa only [componentTensor, BalancedInduction.tensor_add_left] using
        Submodule.add_mem S hg hg'
  have hs (s : C) (y : (J.obj s ⟶ t) ⊗[R] (v ⟶ J.obj s)) :
      BalancedInduction.inclusion J (J ⋙ homModule (k := R) v) t s y ∈ S := by
    induction y using TensorProduct.inductionOn with
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

/-- Integer projection has its image in the prescribed part. -/
theorem integerProjectionOver_mem (v t : D) (n : ℤ) (x : Component (k := R) J v t) :
    integerProjectionOver 𝒜 J hJ hD v t n x ∈ integerDegreeOver (K := K) (R := R) J v t n := by
  have hle : (⨆ m : ℤ, integerDegreeOver (K := K) (R := R) J v t m) ≤
      (integerDegreeOver (K := K) (R := R) J v t n).comap
        (integerProjectionOver 𝒜 J hJ hD v t n) := by
    refine iSup_le fun m => ?_
    intro y hy
    change integerProjectionOver 𝒜 J hJ hD v t n y ∈ integerDegreeOver (K := K) (R := R) J v t n
    rw [integerProjectionOver_of_mem 𝒜 J hJ hD v t hy]
    by_cases h : m = n
    · subst m
      simpa using hy
    · simp only [ite_eq_right h, Submodule.zero_mem]
  rw [iSup_integerDegreeOver_eq_top (K := K) (R := R) J v t] at hle
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule K _))

end OddMath.QuiverHecke.ELV.IndResKernel
end

end
