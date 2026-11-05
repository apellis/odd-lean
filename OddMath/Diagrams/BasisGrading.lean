/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Gradings of free modules over a graded ring

Let `R` be a commutative `K`-algebra graded by `K`-submodules `𝒜 : ℤ → Submodule K R`, and let
`δ : ι → ℤ` assign degrees to an index set. The finitely supported functions `ι →₀ R` are graded
by the `K`-submodules `part 𝒜 δ n = {f | f i ∈ 𝒜 (n - δ i) for all i}`, and these form an internal
direct sum (`isInternal_part`). Transporting along a basis `b : Basis ι R M` grades any free
`R`-module with homogeneous basis vectors (`basisPart`, `isInternal_basisPart`).

For `𝒜` concentrated in degree `0` this is the usual grading of a free module by the degrees of
its basis vectors. It grades the coefficient algebras of the quiver Hecke categories over a
graded base ring (truncated-Rees parameters, `docs/Nondegeneracy/Phase2Plan.md`, step 2).
-/

noncomputable section

namespace OddMath.Diagrams.BasisGrading

open DirectSum

variable {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) (δ : ι → ℤ)

/-- The degree-`n` part of `ι →₀ R`: coefficients at `i` of degree `n - δ i`. -/
def part (n : ℤ) : Submodule K (ι →₀ R) where
  carrier := {f | ∀ i, f i ∈ 𝒜 (n - δ i)}
  add_mem' hf hg i := by
    rw [Finsupp.add_apply]
    exact add_mem (hf i) (hg i)
  zero_mem' i := zero_mem _
  smul_mem' c f hf i := by
    rw [Finsupp.smul_apply]
    exact Submodule.smul_mem _ c (hf i)

variable {𝒜 δ}

theorem mem_part {n : ℤ} {f : ι →₀ R} : f ∈ part 𝒜 δ n ↔ ∀ i, f i ∈ 𝒜 (n - δ i) :=
  Iff.rfl

theorem single_mem_part {i : ι} {e : ℤ} {r : R} (hr : r ∈ 𝒜 e) :
    Finsupp.single i r ∈ part 𝒜 δ (e + δ i) := by
  classical
  intro j
  rw [Finsupp.single_apply]
  split_ifs with h
  · subst h
    simpa using hr
  · exact zero_mem _

variable (𝒜 δ) [Decomposition 𝒜]

/-- The projection onto the degree-`n` part, coefficientwise. -/
def proj (n : ℤ) : (ι →₀ R) →+ (ι →₀ R) where
  toFun f := f.support.sum fun i => Finsupp.single i (decompose 𝒜 (f i) (n - δ i) : R)
  map_zero' := by simp
  map_add' f g := by
    classical
    have key : ∀ h : ι →₀ R, ∀ s : Finset ι, h.support ⊆ s →
        h.support.sum (fun i => Finsupp.single i (decompose 𝒜 (h i) (n - δ i) : R)) =
          s.sum (fun i => Finsupp.single i (decompose 𝒜 (h i) (n - δ i) : R)) := by
      intro h s hs
      refine Finset.sum_subset hs fun i _ hi => ?_
      rw [Finsupp.notMem_support_iff.mp hi]
      simp
    rw [key (f + g) (f.support ∪ g.support) Finsupp.support_add,
      key f (f.support ∪ g.support) Finset.subset_union_left,
      key g (f.support ∪ g.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finsupp.single_add, Finsupp.add_apply, decompose_add, add_apply,
      Submodule.coe_add]

theorem proj_apply (n : ℤ) (f : ι →₀ R) (i : ι) :
    proj 𝒜 δ n f i = decompose 𝒜 (f i) (n - δ i) := by
  classical
  change (f.support.sum fun j => Finsupp.single j (decompose 𝒜 (f j) (n - δ j) : R)) i = _
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hi
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hi]
    simp

theorem proj_of_mem_part {n j : ℤ} {f : ι →₀ R} (hf : f ∈ part 𝒜 δ j) :
    proj 𝒜 δ n f = if j = n then f else 0 := by
  ext i
  rw [proj_apply]
  split_ifs with h
  · subst h
    rw [decompose_of_mem_same 𝒜 (hf i)]
  · rw [decompose_of_mem_ne 𝒜 (hf i) (by omega), Finsupp.zero_apply]

theorem iSup_part : ⨆ n, part 𝒜 δ n = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  induction f using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single i r =>
    induction r using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [Finsupp.single_zero]; exact zero_mem _
    | add r s hr hs => rw [Finsupp.single_add]; exact add_mem hr hs
    | @homogeneous e r => exact Submodule.mem_iSup_of_mem (e + δ i) (single_mem_part r.2)

theorem iSupIndep_part : iSupIndep (part 𝒜 δ) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro f hf hf'
  have h1 := proj_of_mem_part 𝒜 δ (n := n) hf
  simp only [↓reduceIte] at h1
  rw [← h1]
  refine Submodule.iSup_induction _ (motive := fun g => proj 𝒜 δ n g = 0) hf'
    (fun j g hg => ?_) (map_zero _) (fun g g' hg hg' => by rw [map_add, hg, hg', add_zero])
  refine Submodule.iSup_induction _ (motive := fun g => proj 𝒜 δ n g = 0) hg
    (fun hj g hg => ?_) (map_zero _) (fun g g' hg hg' => by rw [map_add, hg, hg', add_zero])
  rw [proj_of_mem_part 𝒜 δ hg]
  simp [hj]

/-- **Graded free modules over a graded ring.** The parts `part 𝒜 δ n` form an internal direct
sum decomposition of `ι →₀ R`. -/
theorem isInternal_part : DirectSum.IsInternal (part 𝒜 δ) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_part 𝒜 δ, iSup_part 𝒜 δ⟩

section Basis

variable {M : Type*} [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
  (b : Module.Basis ι R M)

/-- The degree-`n` part of a free module: the elements whose coordinate at `i` has degree
`n - δ i`. -/
def basisPart (n : ℤ) : Submodule K M :=
  (part 𝒜 δ n).comap ((b.repr : M →ₗ[R] ι →₀ R).restrictScalars K)

variable {𝒜 δ b}

omit [Decomposition 𝒜] in
theorem mem_basisPart {n : ℤ} {x : M} : x ∈ basisPart 𝒜 δ b n ↔ ∀ i, b.repr x i ∈ 𝒜 (n - δ i) :=
  Iff.rfl

omit [Decomposition 𝒜] in
theorem smul_basis_mem_basisPart {i : ι} {e : ℤ} {r : R} (hr : r ∈ 𝒜 e) :
    r • b i ∈ basisPart 𝒜 δ b (e + δ i) := by
  change b.repr (r • b i) ∈ part 𝒜 δ (e + δ i)
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact single_mem_part hr

omit [Decomposition 𝒜] in
/-- Multiplication by a homogeneous scalar shifts the degree. -/
theorem smul_mem_basisPart [SetLike.GradedMul 𝒜] {e n : ℤ} {r : R} (hr : r ∈ 𝒜 e) {x : M}
    (hx : x ∈ basisPart 𝒜 δ b n) : r • x ∈ basisPart 𝒜 δ b (e + n) := by
  intro i
  change b.repr (r • x) i ∈ 𝒜 (e + n - δ i)
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, add_sub_assoc]
  exact SetLike.GradedMul.mul_mem hr (hx i)

variable (𝒜 δ b)

/-- **Graded free modules with a homogeneous basis.** -/
theorem isInternal_basisPart : DirectSum.IsInternal (basisPart 𝒜 δ b) := by
  let o := Submodule.orderIsoMapComap (b.repr.restrictScalars K : M ≃ₗ[K] (ι →₀ R))
  have hb : basisPart 𝒜 δ b = o.symm ∘ part 𝒜 δ := rfl
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, hb]
  refine ⟨(iSupIndep_map_orderIso_iff o.symm).mpr (iSupIndep_part 𝒜 δ), ?_⟩
  rw [Function.comp_def, ← o.symm.map_iSup, iSup_part, map_top]

end Basis

end OddMath.Diagrams.BasisGrading
