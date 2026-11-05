/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Tensor products of graded modules over a graded ring

Let `R` be a commutative `K`-algebra graded by `K`-submodules `𝒜 : ℤ → Submodule K R`, and let
`M`, `N` be `R`-modules with `K`-linear gradings `ℳ`, `𝒩` compatible with `𝒜`
(`𝒜 a • ℳ n ⊆ ℳ (a + n)`). Then `M ⊗[R] N` is graded by the `K`-spans
`part n = span {m ⊗ x | m ∈ ℳ p, x ∈ 𝒩 q, p + q = n}`: these parts form an internal direct sum
(`isInternal_part`). No flatness or freeness is needed: the degree projections are defined on the
`K`-bilinear level and descend because the balancing relations are homogeneous.

This supplies the grading of the coefficient-extended quiver Hecke categories over a graded base
ring, where scalars of `R` carry positive degree (truncated-Rees parameters,
`docs/Nondegeneracy/Phase2Plan.md`, step 2). For the trivial grading of `R` (`𝒜 0 = ⊤`) it is the usual tensor grading over `R`.
-/

noncomputable section

namespace OddMath.Diagrams.GradedTensor

open DirectSum TensorProduct

variable {K R M N : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M]
  [AddCommGroup N] [Module R N] [Module K N]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M) (𝒩 : ℤ → Submodule K N)

section Projection

open Classical in
/-- The degree-`n` component of `m ⊗ x`, as a biadditive map over `ℤ`. -/
def projBihom [Decomposition ℳ] [Decomposition 𝒩] (n : ℤ) : M →+ N →+ M ⊗[R] N where
  toFun m :=
    { toFun := fun x => (decompose ℳ m).sum fun p a =>
        (a : M) ⊗ₜ[R] (decompose 𝒩 x (n - p) : N)
      map_zero' := by
        unfold DFinsupp.sum
        exact Finset.sum_eq_zero fun p _ => by
          simp only [decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero, tmul_zero]
      map_add' := fun x y => by
        unfold DFinsupp.sum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [decompose_add, DirectSum.add_apply, Submodule.coe_add, tmul_add] }
  map_zero' := by
    ext x
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, decompose_zero, AddMonoidHom.zero_apply]
    exact DFinsupp.sum_zero_index
  map_add' m m' := by
    ext x
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply, decompose_add]
    exact DFinsupp.sum_add_index (fun _ => by rw [ZeroMemClass.coe_zero, zero_tmul])
      fun _ _ _ => by rw [Submodule.coe_add, add_tmul]

variable [Decomposition ℳ] [Decomposition 𝒩]

omit [Algebra K R] in
theorem projBihom_of_mem {n p : ℤ} {m : M} (hm : m ∈ ℳ p) (x : N) :
    projBihom (R := R) ℳ 𝒩 n m x = m ⊗ₜ[R] (decompose 𝒩 x (n - p) : N) := by
  classical
  change (decompose ℳ m).sum (fun p (a : ℳ p) => (a : M) ⊗ₜ[R] (decompose 𝒩 x (n - p) : N)) = _
  have : decompose ℳ m = DirectSum.of (fun i => ℳ i) p ⟨m, hm⟩ :=
    decompose_coe (ℳ := ℳ) (⟨m, hm⟩ : ℳ p)
  rw [this]
  exact DFinsupp.sum_single_index (β := fun i => ℳ i)
    (h := fun p (a : ℳ p) => (a : M) ⊗ₜ[R] (decompose 𝒩 x (n - p) : N))
    (by rw [ZeroMemClass.coe_zero, zero_tmul])

omit [Algebra K R] in
theorem projBihom_of_mem_of_mem {n p q : ℤ} {m : M} {x : N} (hm : m ∈ ℳ p) (hx : x ∈ 𝒩 q) :
    projBihom (R := R) ℳ 𝒩 n m x = if p + q = n then m ⊗ₜ[R] x else 0 := by
  rw [projBihom_of_mem ℳ 𝒩 hm]
  split_ifs with h
  · rw [show n - p = q by omega, decompose_of_mem_same 𝒩 hx]
  · rw [decompose_of_mem_ne 𝒩 hx (by omega), tmul_zero]

/-- Every homogeneous `r ∈ R` moves across the projected tensor. -/
theorem projBihom_smul [Decomposition 𝒜]
    (hℳ : ∀ {a p : ℤ} {r : R} {m : M}, r ∈ 𝒜 a → m ∈ ℳ p → r • m ∈ ℳ (a + p))
    (h𝒩 : ∀ {a q : ℤ} {r : R} {x : N}, r ∈ 𝒜 a → x ∈ 𝒩 q → r • x ∈ 𝒩 (a + q))
    (n : ℤ) (r : R) (m : M) (x : N) :
    projBihom (R := R) ℳ 𝒩 n (r • m) x = projBihom (R := R) ℳ 𝒩 n m (r • x) := by
  induction r using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add r r' hr hr' => simp only [add_smul, map_add, AddMonoidHom.add_apply, hr, hr']
  | @homogeneous a r =>
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | add m m' hm hm' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hm, hm']
    | @homogeneous p m =>
      induction x using DirectSum.Decomposition.inductionOn 𝒩 with
      | zero => simp
      | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']
      | @homogeneous q x =>
        rw [projBihom_of_mem_of_mem ℳ 𝒩 (hℳ r.2 m.2) x.2,
          projBihom_of_mem_of_mem ℳ 𝒩 m.2 (h𝒩 r.2 x.2), smul_tmul]
        congr 1
        exact propext ⟨fun h => by omega, fun h => by omega⟩

/-- The degree-`n` projection of `M ⊗[R] N`. -/
def proj [Decomposition 𝒜]
    (hℳ : ∀ {a p : ℤ} {r : R} {m : M}, r ∈ 𝒜 a → m ∈ ℳ p → r • m ∈ ℳ (a + p))
    (h𝒩 : ∀ {a q : ℤ} {r : R} {x : N}, r ∈ 𝒜 a → x ∈ 𝒩 q → r • x ∈ 𝒩 (a + q))
    (n : ℤ) : M ⊗[R] N →+ M ⊗[R] N :=
  liftAddHom (projBihom (R := R) ℳ 𝒩 n) (projBihom_smul 𝒜 ℳ 𝒩 hℳ h𝒩 n)

end Projection

section Internal

variable [IsScalarTower K R M]

/-- The degree-`n` part of `M ⊗[R] N`: the `K`-span of the `m ⊗ x` with
`m ∈ ℳ p`, `x ∈ 𝒩 q` and `p + q = n`. -/
def part (n : ℤ) : Submodule K (M ⊗[R] N) :=
  Submodule.span K {y | ∃ p q : ℤ, p + q = n ∧ ∃ m ∈ ℳ p, ∃ x ∈ 𝒩 q, y = m ⊗ₜ[R] x}

variable {ℳ 𝒩} in
theorem tmul_mem_part {p q : ℤ} {m : M} {x : N} (hm : m ∈ ℳ p) (hx : x ∈ 𝒩 q) :
    m ⊗ₜ[R] x ∈ part ℳ 𝒩 (p + q) :=
  Submodule.subset_span ⟨p, q, rfl, m, hm, x, hx, rfl⟩

variable [Decomposition 𝒜] [Decomposition ℳ] [Decomposition 𝒩]
  (hℳ : ∀ {a p : ℤ} {r : R} {m : M}, r ∈ 𝒜 a → m ∈ ℳ p → r • m ∈ ℳ (a + p))
  (h𝒩 : ∀ {a q : ℤ} {r : R} {x : N}, r ∈ 𝒜 a → x ∈ 𝒩 q → r • x ∈ 𝒩 (a + q))

omit [IsScalarTower K R M] in
theorem proj_tmul (n : ℤ) (m : M) (x : N) :
    proj 𝒜 ℳ 𝒩 hℳ h𝒩 n (m ⊗ₜ[R] x) = projBihom (R := R) ℳ 𝒩 n m x :=
  liftAddHom_tmul _ _ _ _

omit [Decomposition 𝒜] in
theorem projBihom_smul_left (n : ℤ) (c : K) (m : M) (x : N) :
    projBihom (R := R) ℳ 𝒩 n (c • m) x = c • projBihom (R := R) ℳ 𝒩 n m x := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | add m m' hm hm' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hm, hm']
  | @homogeneous p m =>
    induction x using DirectSum.Decomposition.inductionOn 𝒩 with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx', smul_add]
    | @homogeneous q x =>
      rw [projBihom_of_mem_of_mem ℳ 𝒩 (Submodule.smul_mem _ c m.2) x.2,
        projBihom_of_mem_of_mem ℳ 𝒩 m.2 x.2]
      split_ifs
      · exact (smul_tmul' c (m : M) (x : N)).symm
      · rw [smul_zero]

theorem proj_smul (n : ℤ) (c : K) (y : M ⊗[R] N) :
    proj 𝒜 ℳ 𝒩 hℳ h𝒩 n (c • y) = c • proj 𝒜 ℳ 𝒩 hℳ h𝒩 n y := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]
  | tmul m x =>
    rw [smul_tmul', proj_tmul, proj_tmul, projBihom_smul_left]

theorem proj_of_mem_part {n j : ℤ} {y : M ⊗[R] N} (hy : y ∈ part ℳ 𝒩 j) :
    proj 𝒜 ℳ 𝒩 hℳ h𝒩 n y = if j = n then y else 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, rfl, m, hm, x, hx, rfl⟩ := hy
    rw [proj_tmul, projBihom_of_mem_of_mem ℳ 𝒩 hm hx]
  | zero => simp
  | add y y' _ _ hy hy' => rw [map_add, hy, hy']; split_ifs <;> simp
  | smul c y _ hy => rw [proj_smul, hy]; split_ifs <;> simp

omit [Decomposition 𝒜] in
theorem iSup_part : ⨆ n, part (R := R) ℳ 𝒩 n = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => exact Submodule.add_mem _ hy hy'
  | tmul m x =>
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero => rw [zero_tmul]; exact Submodule.zero_mem _
    | add m m' hm hm' => rw [add_tmul]; exact Submodule.add_mem _ hm hm'
    | @homogeneous p m =>
      induction x using DirectSum.Decomposition.inductionOn 𝒩 with
      | zero => rw [tmul_zero]; exact Submodule.zero_mem _
      | add x x' hx hx' => rw [tmul_add]; exact Submodule.add_mem _ hx hx'
      | @homogeneous q x => exact Submodule.mem_iSup_of_mem (p + q) (tmul_mem_part m.2 x.2)

include hℳ h𝒩 in
theorem iSupIndep_part : iSupIndep (part (R := R) ℳ 𝒩) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro y hy hy'
  have h1 := proj_of_mem_part 𝒜 ℳ 𝒩 hℳ h𝒩 (n := n) hy
  simp only [↓reduceIte] at h1
  rw [← h1]
  refine Submodule.iSup_induction _ (motive := fun y => proj 𝒜 ℳ 𝒩 hℳ h𝒩 n y = 0) hy'
    (fun j y hy => ?_) (map_zero _) (fun y y' hy hy' => by rw [map_add, hy, hy', add_zero])
  refine Submodule.iSup_induction _ (motive := fun y => proj 𝒜 ℳ 𝒩 hℳ h𝒩 n y = 0) hy
    (fun hj y hy => ?_) (map_zero _) (fun y y' hy hy' => by rw [map_add, hy, hy', add_zero])
  rw [proj_of_mem_part 𝒜 ℳ 𝒩 hℳ h𝒩 hy]
  simp [hj]

include hℳ h𝒩 in
/-- **Graded tensor products over a graded ring.** The parts `part ℳ 𝒩 n` form an internal
direct sum decomposition of `M ⊗[R] N`. -/
theorem isInternal_part : DirectSum.IsInternal (part (R := R) ℳ 𝒩) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_part 𝒜 ℳ 𝒩 hℳ h𝒩, iSup_part ℳ 𝒩⟩

end Internal

end OddMath.Diagrams.GradedTensor
