/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NativeCyclic.CyclicDiagonal

/-! Native cyclic injectivity on whole finite covering-ring spans. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
open PreF Coefficients TensorProduct NativeLeading
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

local instance : AddCommGroup
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  TensorProduct.addCommGroup

local instance : AddCommGroup
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.addCommGroup

/-- The exact native leading coefficient, acting on actual formal bidegree projections. -/
def leadingDiagonal (s : Bool) (N : ℕ) :=
  diagonal D hD N (fun α β => (scalarUnit D Λ Μ s α β : Coefficients.Ring))

/-- A genuine linear error map, not a choice of word expansion. -/
def error (s : Bool) (N : ℕ) :=
  cyclic D Λ Μ s - (toIntegrableTensor D Λ Μ).comp (leadingDiagonal D hD Λ Μ s N)

/-- The error strictly lowers both lengths on every linear combination in the square. -/
theorem error_mem_lower (s : Bool) (N n : ℕ) (hn : n ≤ N)
    {z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi}
    (hz : z ∈ truncation D n n) :
    error D hD Λ Μ s N z ∈ lowerBidegree D Λ Μ n n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    obtain ⟨_, r, hr, he⟩ := cyclic_wordTensor_leading D Λ Μ s a b
    have herr : error D hD Λ Μ s N (wordTensor D a b) = r := by
      simp only [error, LinearMap.sub_apply, LinearMap.comp_apply, leadingDiagonal,
        diagonal_word D hD N _ a b (ha.trans hn) (hb.trans hn), scalarUnit_word,
        map_smul, he]
      abel
    rw [herr]
    exact lowerBidegree_mono D Λ Μ ha hb hr
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- Vanishing of the native cyclic map forces the leading diagonal into the lower image. -/
theorem leading_mem_lower_of_cyclic_eq_zero (s : Bool) (N n : ℕ) (hn : n ≤ N)
    {z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi}
    (hz : z ∈ truncation D n n) (hzero : cyclic D Λ Μ s z = 0) :
    toIntegrableTensor D Λ Μ (leadingDiagonal D hD Λ Μ s N z) ∈
      lowerBidegree D Λ Μ n n := by
  have he := error_mem_lower D hD Λ Μ s N n hn hz
  simpa only [error, LinearMap.sub_apply, LinearMap.comp_apply, hzero,
    zero_sub, neg_mem_iff] using he

include hD

/-- Finite-filtration induction using quotient injectivity on the SAME full square.
The only injectivity hypothesis here is discharged by the next theorem. -/
theorem cyclic_kernel_truncation (s : Bool) (N : ℕ)
    (hQ : Set.InjOn (toIntegrableTensor D Λ Μ) (truncation D N N))
    {z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi}
    (hz : z ∈ truncation D N N) (hzero : cyclic D Λ Μ s z = 0) : z = 0 := by
  have step (n : ℕ) : n ≤ N → ∀ z ∈ truncation D n n,
      cyclic D Λ Μ s z = 0 → z = 0 := by
    induction n with
    | zero =>
      intro hn z hz hzero
      have he := leading_mem_lower_of_cyclic_eq_zero D hD Λ Μ s N 0 hn hz hzero
      have hDz : leadingDiagonal D hD Λ Μ s N z ∈ truncation D N N :=
        diagonal_mem_truncation D hD N N N le_rfl le_rfl _
          (truncation_mono D hn hn hz)
      have hd : leadingDiagonal D hD Λ Μ s N z = 0 := by
        apply hQ hDz (Submodule.zero_mem _)
        simpa only [lowerBidegree_zero_left, Submodule.mem_bot, map_zero] using he
      have hi := diagonal_inverse D hD N (scalarUnit D Λ Μ s)
        (truncation_mono D hn hn hz)
      change diagonal D hD N _ (leadingDiagonal D hD Λ Μ s N z) = z at hi
      simpa only [hd, map_zero] using hi.symm
    | succ n ih =>
      intro hn z hz hzero
      have hn' : n ≤ N := (Nat.le_succ n).trans hn
      have he := leading_mem_lower_of_cyclic_eq_zero D hD Λ Μ s N (n + 1) hn hz hzero
      have hm := lowerBidegree_le_map_truncation D Λ Μ
        (m := n) (n := n) le_rfl le_rfl he
      obtain ⟨t, ht, heq⟩ := hm
      have hDz : leadingDiagonal D hD Λ Μ s N z ∈ truncation D N N :=
        diagonal_mem_truncation D hD N N N le_rfl le_rfl _
          (truncation_mono D hn hn hz)
      have htd : t = leadingDiagonal D hD Λ Μ s N z :=
        hQ (truncation_mono D hn' hn' ht) hDz heq
      have hi := diagonal_inverse D hD N (scalarUnit D Λ Μ s)
        (truncation_mono D hn hn hz)
      change diagonal D hD N _ (leadingDiagonal D hD Λ Μ s N z) = z at hi
      have hsmall := diagonal_mem_truncation D hD N n n hn' hn'
        (fun α β => ↑(scalarUnit D Λ Μ s α β)⁻¹) (htd ▸ ht)
      rw [hi] at hsmall
      exact ih hn' z hsmall hzero
  exact step N le_rfl z hz hzero

/-- One common coroot threshold gives native cyclic injectivity on the whole square,
for both native coproducts, over the actual covering ring. -/
theorem cyclic_truncation_injective_bound (N : ℕ) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ Μ : X, (∀ i, B ≤ D.h i Λ) → (∀ i, B ≤ D.h i Μ) →
      ∀ s : Bool, Set.InjOn (cyclic D Λ Μ s) (truncation D N N) := by
  obtain ⟨B, hB, hQ⟩ := truncation_quotient_injective_bound D hD N N
  refine ⟨B, hB, fun Λ Μ hΛ hΜ s x hx y hy hxy => ?_⟩
  apply sub_eq_zero.mp
  apply cyclic_kernel_truncation D hD Λ Μ s N (hQ Λ Μ hΛ hΜ)
    ((truncation D N N).sub_mem hx hy)
  simpa only [map_sub, sub_eq_zero] using hxy

/-- Native cyclic injectivity on the entire covering-ring span of arbitrary finite
Serre tensors. No word independence, grading, field, or freeness is a premise. -/
theorem finite_span_cyclic_injective_bound
    (S : Finset (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi)) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ Μ : X, (∀ i, B ≤ D.h i Λ) → (∀ i, B ≤ D.h i Μ) →
      ∀ s : Bool, Set.InjOn (cyclic D Λ Μ s)
        (Submodule.span Coefficients.Ring
          (S : Set (D.serreF Coefficients.q pi ⊗[Coefficients.Ring]
            D.serreF Coefficients.q pi))) := by
  obtain ⟨m, n, hS⟩ := finite_span_le_truncation D S
  obtain ⟨B, hB, h⟩ := cyclic_truncation_injective_bound D hD (max m n)
  exact ⟨B, hB, fun Λ Μ hΛ hΜ s => (h Λ Μ hΛ hΜ s).mono
    (hS.trans (truncation_mono D (le_max_left _ _) (le_max_right _ _)))⟩

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
