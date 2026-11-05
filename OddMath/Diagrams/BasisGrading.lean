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
omit [Decomposition 𝒜] in
/-- Multiplication by a homogeneous scalar shifts the degree. -/
theorem smul_mem_basisPart [SetLike.GradedMul 𝒜] {e n : ℤ} {r : R} (hr : r ∈ 𝒜 e) {x : M}
    (hx : x ∈ basisPart 𝒜 δ b n) : r • x ∈ basisPart 𝒜 δ b (e + n) := by
  intro i
  change b.repr (r • x) i ∈ 𝒜 (e + n - δ i)
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, add_sub_assoc]
  exact SetLike.GradedMul.mul_mem hr (hx i)

omit [Decomposition 𝒜] in
/-- If the base grading is bounded below by `a` and the basis degrees by `c`, the degrees of the
free module are bounded below by `a + c`. -/
theorem basisPart_eq_bot_of_lower_bound {a c n : ℤ} (h𝒜 : ∀ m, m < a → 𝒜 m = ⊥)
    (hδ : ∀ i, c ≤ δ i) (hn : n < a + c) : basisPart 𝒜 δ b n = ⊥ := by
  refine eq_bot_iff.2 fun x hx => (Submodule.mem_bot K).2 ?_
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  have hi := hx i
  rw [h𝒜 _ (by have := hδ i; omega), Submodule.mem_bot] at hi
  rw [map_zero, Finsupp.zero_apply]
  exact hi

variable (𝒜 δ b)

/-- **Graded free modules with a homogeneous basis.** -/
theorem isInternal_basisPart : DirectSum.IsInternal (basisPart 𝒜 δ b) := by
  let o := Submodule.orderIsoMapComap (b.repr.restrictScalars K : M ≃ₗ[K] (ι →₀ R))
  have hb : basisPart 𝒜 δ b = o.symm ∘ part 𝒜 δ := rfl
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, hb]
  refine ⟨(iSupIndep_map_orderIso_iff o.symm).mpr (iSupIndep_part 𝒜 δ), ?_⟩
  rw [Function.comp_def, ← o.symm.map_iSup, iSup_part, map_top]

end Basis

section LowerBound

variable {M : Type*} [AddCommGroup M] [Module R M] [Module K M] {ι' : Type*}

omit [Decomposition 𝒜] in
/-- **Lower bounds from a spanning family.** Let `R` be graded in nonnegative degrees and let
`𝒢` be a `K`-grading of an `R`-module `M` along which homogeneous scalars shift degrees. If `M`
is spanned over `R` by homogeneous elements of degrees at least `N`, then `𝒢 d = 0` for
`d < N`. -/
theorem eq_bot_of_span_lower_bound [Decomposition 𝒜] {𝒢 : ℤ → Submodule K M}
    (h𝒢 : iSupIndep 𝒢) (h𝒜 : ∀ m, m < 0 → 𝒜 m = ⊥)
    (hsmul : ∀ {e n : ℤ} {r : R} {y : M}, r ∈ 𝒜 e → y ∈ 𝒢 n → r • y ∈ 𝒢 (e + n))
    {v : ι' → M} {δ' : ι' → ℤ} (hv : ∀ i, v i ∈ 𝒢 (δ' i))
    (hspan : Submodule.span R (Set.range v) = ⊤) {N d : ℤ} (hN : ∀ i, N ≤ δ' i)
    (hd : d < N) : 𝒢 d = ⊥ := by
  let S : Submodule K M := ⨆ (m : ℤ) (_ : N ≤ m), 𝒢 m
  have hS : ∀ {m}, N ≤ m → 𝒢 m ≤ S := fun {m} hm =>
    le_iSup₂_of_le (f := fun (m : ℤ) (_ : N ≤ m) => 𝒢 m) m hm le_rfl
  have hsmulS : ∀ (r : R) {y : M}, y ∈ S → r • y ∈ S := by
    intro r y hy
    induction r using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [zero_smul]; exact zero_mem _
    | add r s hr hs => rw [add_smul]; exact add_mem hr hs
    | @homogeneous e r =>
      by_cases he : e < 0
      · have hr : (r : R) ∈ (⊥ : Submodule K R) := h𝒜 e he ▸ r.2
        rw [(Submodule.mem_bot K).1 hr, zero_smul]
        exact zero_mem S
      · have h0 : (r : R) • (0 : M) ∈ S := by rw [smul_zero]; exact zero_mem S
        have hadd : ∀ z z' : M, (r : R) • z ∈ S → (r : R) • z' ∈ S → (r : R) • (z + z') ∈ S :=
          fun z z' hz hz' => by rw [smul_add]; exact add_mem hz hz'
        refine Submodule.iSup_induction (motive := fun y => (r : R) • y ∈ S)
          (fun m : ℤ => ⨆ (_ : N ≤ m), 𝒢 m) hy (fun m z hz => ?_) h0 hadd
        exact Submodule.iSup_induction (motive := fun z => (r : R) • z ∈ S) _ hz
          (fun hm z hz => hS (by omega) (hsmul r.2 hz)) h0 hadd
  have hall : ∀ y : M, y ∈ S := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range v) := by rw [hspan]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hS (hN i) (hv i)
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy => exact hsmulS r hy
  refine eq_bot_iff.2 fun x hx => ?_
  have hle : S ≤ ⨆ (m : ℤ) (_ : m ≠ d), 𝒢 m :=
    iSup₂_mono' fun m hm => ⟨m, by omega, le_rfl⟩
  exact (Submodule.disjoint_def.1 (h𝒢 d)) x hx (hle (hall x)) ▸ zero_mem _

end LowerBound

section Span

variable {M : Type*} [AddCommGroup M] [Module R M] [Module K M] (𝒢 : ℤ → Submodule K M)
  [Decomposition 𝒢]

omit [Decomposition 𝒜] in
/-- Multiplication by a homogeneous scalar of degree `e` shifts homogeneous components by
`e`. -/
theorem decompose_smul_of_mem
    (hsmul : ∀ {e n : ℤ} {r : R} {y : M}, r ∈ 𝒜 e → y ∈ 𝒢 n → r • y ∈ 𝒢 (e + n))
    {e : ℤ} {r : R} (hr : r ∈ 𝒜 e) (y : M) (n : ℤ) :
    (decompose 𝒢 (r • y) n : M) = r • (decompose 𝒢 y (n - e) : M) := by
  induction y using DirectSum.Decomposition.inductionOn 𝒢 with
  | zero => simp
  | add y z hy hz => rw [smul_add, decompose_add, add_apply, Submodule.coe_add, hy, hz,
      decompose_add, add_apply, Submodule.coe_add, smul_add]
  | @homogeneous m y =>
    by_cases h : e + m = n
    · subst h
      rw [decompose_of_mem_same 𝒢 (hsmul hr y.2), add_sub_cancel_left,
        decompose_of_mem_same 𝒢 y.2]
    · rw [decompose_of_mem_ne 𝒢 (hsmul hr y.2) h, decompose_of_mem_ne 𝒢 y.2 (by omega),
        smul_zero]

/-- **Homogeneous spans over a graded base.** If every homogeneous component of each generator
of an `R`-submodule `I` lies in `I`, then so does every homogeneous component of every element
of `I`. -/
theorem decompose_mem_span
    (hsmul : ∀ {e n : ℤ} {r : R} {y : M}, r ∈ 𝒜 e → y ∈ 𝒢 n → r • y ∈ 𝒢 (e + n))
    {S : Set M} (hS : ∀ g ∈ S, ∀ n, (decompose 𝒢 g n : M) ∈ Submodule.span R S)
    {f : M} (hf : f ∈ Submodule.span R S) (n : ℤ) :
    (decompose 𝒢 f n : M) ∈ Submodule.span R S := by
  induction hf using Submodule.span_induction generalizing n with
  | mem g hg => exact hS g hg n
  | zero => simp
  | add f g _ _ hf hg =>
    rw [decompose_add, add_apply, Submodule.coe_add]
    exact add_mem (hf n) (hg n)
  | smul c f _ hf =>
    induction c using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add c c' hc hc' =>
      rw [add_smul, decompose_add, add_apply, Submodule.coe_add]
      exact add_mem hc hc'
    | @homogeneous e c =>
      rw [decompose_smul_of_mem 𝒜 𝒢 hsmul c.2]
      exact Submodule.smul_mem _ _ (hf _)

end Span

end OddMath.Diagrams.BasisGrading
