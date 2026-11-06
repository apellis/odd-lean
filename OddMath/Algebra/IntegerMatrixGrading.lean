import StringDiagrams.Super.GSVec
import StringDiagrams.Super.GradedSub
import Mathlib.LinearAlgebra.Pi

/-! # Intrinsic shifted coordinates for finite graded matrices

Supporting the homogeneous inverse step (G8) of DeformedGradedAction:
the source and target degrees are specified independently of the matrix.
A bijective degree-zero linear map preserves their projections in both
directions. Finite products use the convention `shift a` in degree `n`
means the original degree `n + a`.
-/
noncomputable section
namespace OddMath.IntegerMatrix
open StringDiagrams
universe u v w
variable {k : Type u} [CommRing k]

/-- An intrinsic integer decomposition together with its actual projections. -/
structure Coordinates (M : Type v) [AddCommGroup M] [Module k M] where
  degree : ℤ → Submodule k M
  projection : ℤ → M →ₗ[k] M
  projection_mem : ∀ n x, projection n x ∈ degree n
  projection_of_mem : ∀ {m n} {x}, x ∈ degree m →
    projection n x = if m = n then x else 0
  spanning : (⨆ n, degree n) = ⊤

namespace Coordinates
variable {M : Type v} [AddCommGroup M] [Module k M]
  {N : Type w} [AddCommGroup N] [Module k N]

theorem mem_iff_projection (A : Coordinates (k := k) M) (n : ℤ) (x : M) :
    x ∈ A.degree n ↔ A.projection n x = x := by
  constructor
  · intro hx
    exact (A.projection_of_mem (n := n) hx).trans (ite_eq_left rfl)
  · intro hx
    simpa only [hx] using A.projection_mem n x

/-- The degree parts are an internal direct sum on the original module. -/
theorem internal (A : Coordinates (k := k) M) : DirectSum.IsInternal A.degree := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · refine iSupIndep_of_projections _ A.projection (fun n x hx => ?_)
      (fun n m hmn x hx => ?_)
    · exact (A.projection_of_mem (n := n) hx).trans (ite_eq_left rfl)
    · exact (A.projection_of_mem (n := n) hx).trans (ite_eq_right hmn)
  · exact A.spanning

/-- A homogeneous map commutes with the independently prescribed projections. -/
theorem map_projection (A : Coordinates (k := k) M) (B : Coordinates (k := k) N)
    (f : M →ₗ[k] N) (d : ℤ)
    (hf : ∀ n x, x ∈ A.degree n → f x ∈ B.degree (n + d)) (n : ℤ) (x : M) :
    f (A.projection n x) = B.projection (n + d) (f x) := by
  have hx : x ∈ ⨆ n, A.degree n := by rw [A.spanning]; exact Submodule.mem_top
  refine Submodule.iSup_induction A.degree (motive := fun x =>
    f (A.projection n x) = B.projection (n + d) (f x)) hx (fun m y hy => ?_) ?_ ?_
  · rw [A.projection_of_mem hy, B.projection_of_mem (hf m y hy)]
    by_cases h : m = n
    · subst m; simp only [↓reduceIte]
    · rw [ite_eq_right h, ite_eq_right (fun e => h (add_right_cancel e)), map_zero]
  · simp only [map_zero]
  · intro y z hy hz
    simp only [map_add, hy, hz]

/-- The inverse of a degree-zero bijection commutes with the original
coordinate projections; the inverse does not define the grading. -/
theorem inverse_projection (A : Coordinates (k := k) M) (B : Coordinates (k := k) N)
    (e : M ≃ₗ[k] N) (he : ∀ n x, x ∈ A.degree n → e x ∈ B.degree n)
    (n : ℤ) (y : N) : e.symm (B.projection n y) = A.projection n (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply]
  simpa only [LinearEquiv.coe_coe, add_zero, e.apply_symm_apply] using
    (A.map_projection B e.toLinearMap 0 (fun n x hx => by
      change e x ∈ B.degree (n + 0)
      rw [add_zero]
      exact he n x hx)
      n (e.symm y)).symm

/-- A raw bijective degree-zero finite matrix has a degree-zero raw inverse. -/
theorem inverse_mem (A : Coordinates (k := k) M) (B : Coordinates (k := k) N)
    (e : M ≃ₗ[k] N) (he : ∀ n x, x ∈ A.degree n → e x ∈ B.degree n)
    {n : ℤ} {y : N} (hy : y ∈ B.degree n) : e.symm y ∈ A.degree n := by
  apply (A.mem_iff_projection n _).2
  rw [← A.inverse_projection B e he n y, (B.mem_iff_projection n y).1 hy]

/-- The integer degree on a shifted coordinate family, without changing
its underlying product module. -/
def shiftedDegree {ι : Type v} {V : ι → Type w}
    [∀ a, AddCommGroup (V a)] [∀ a, Module k (V a)]
    (A : ∀ a, Coordinates (k := k) (V a)) (s : ι → ℤ) (n : ℤ) :
    Submodule k (∀ a, V a) := Submodule.pi Set.univ (fun a => (A a).degree (n + s a))

/-- The corresponding componentwise intrinsic degree projection. -/
def shiftedProjection {ι : Type v} {V : ι → Type w}
    [∀ a, AddCommGroup (V a)] [∀ a, Module k (V a)]
    (A : ∀ a, Coordinates (k := k) (V a)) (s : ι → ℤ) (n : ℤ) :
    (∀ a, V a) →ₗ[k] (∀ a, V a) :=
  LinearMap.pi (fun a => (A a).projection (n + s a) ∘ₗ LinearMap.proj a)

theorem mem_shiftedDegree {ι : Type v} {V : ι → Type w}
    [∀ a, AddCommGroup (V a)] [∀ a, Module k (V a)]
    (A : ∀ a, Coordinates (k := k) (V a)) (s : ι → ℤ) (n : ℤ) (x : ∀ a, V a) :
    x ∈ shiftedDegree A s n ↔ ∀ a, x a ∈ (A a).degree (n + s a) := by
  simp only [shiftedDegree, Submodule.mem_pi, Set.mem_univ, forall_true_left]

/-- A finite shifted coordinate family has its intrinsic product decomposition. -/
def shiftedFamily {ι : Type v} [Fintype ι] {V : ι → Type w}
    [∀ a, AddCommGroup (V a)] [∀ a, Module k (V a)]
    (A : ∀ a, Coordinates (k := k) (V a)) (s : ι → ℤ) :
    Coordinates (k := k) (∀ a, V a) where
  degree := shiftedDegree A s
  projection := shiftedProjection A s
  projection_mem n x := (mem_shiftedDegree A s n _).2 fun a => (A a).projection_mem _ _
  projection_of_mem {m n} {x} hx := by
    classical
    funext a
    change (A a).projection (n + s a) (x a) = (if m = n then x else 0) a
    rw [(A a).projection_of_mem ((mem_shiftedDegree A s m x).1 hx a)]
    by_cases h : m = n
    · subst m; simp only [↓reduceIte]
    · rw [ite_eq_right h, ite_eq_right (fun e => h (add_right_cancel e))]
      rfl
  spanning := by
    classical
    apply top_unique
    intro x _
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro a _
    have hx : x a ∈ ⨆ n, (A a).degree n := by rw [(A a).spanning]; exact Submodule.mem_top
    refine Submodule.iSup_induction (A a).degree (motive := fun y =>
      Pi.single a y ∈ ⨆ n, shiftedDegree A s n) hx (fun n y hy => ?_) ?_ ?_
    · apply Submodule.mem_iSup_of_mem (n - s a)
      apply (mem_shiftedDegree A s _ _).2
      intro b
      by_cases h : a = b
      · subst b
        simpa using hy
      · rw [Pi.single_eq_of_ne (Ne.symm h)]
        exact Submodule.zero_mem _
    · simpa only [Pi.single_zero] using
        (Submodule.zero_mem (⨆ n, shiftedDegree A s n))
    · intro y z hy hz
      simpa only [Pi.single_add] using Submodule.add_mem _ hy hz

/-- The same decomposition, forgetting the scalars down to `ℤ`. The inverse step only uses the
additive structure, so coordinates over a base ring `K` of an `R`-module may be compared with
`R`-linear matrices through this. -/
def toInt {K : Type*} [CommRing K] [Module K M] (A : Coordinates (k := K) M) :
    Coordinates (k := ℤ) M where
  degree n := (A.degree n).restrictScalars ℤ
  projection n := (A.projection n).toAddMonoidHom.toIntLinearMap
  projection_mem n x := A.projection_mem n x
  projection_of_mem hx := A.projection_of_mem hx
  spanning := by
    apply top_unique
    intro x _
    have hx : x ∈ ⨆ n, A.degree n := by rw [A.spanning]; exact Submodule.mem_top
    exact Submodule.iSup_induction A.degree (motive := fun y =>
      y ∈ ⨆ n, (A.degree n).restrictScalars ℤ) hx
      (fun n y hy => Submodule.mem_iSup_of_mem n hy) (zero_mem _) (fun _ _ => add_mem)

theorem mem_toInt {K : Type*} [CommRing K] [Module K M] (A : Coordinates (k := K) M)
    (n : ℤ) (x : M) : x ∈ A.toInt.degree n ↔ x ∈ A.degree n := Iff.rfl

end Coordinates
end OddMath.IntegerMatrix
