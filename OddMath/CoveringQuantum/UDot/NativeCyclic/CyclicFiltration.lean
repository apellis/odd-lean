import OddMath.CoveringQuantum.UDot.NativeCyclic.CyclicNative
import Mathlib.Data.Set.Finite.List

/-! Finite rectangular word filtrations on actual Serre tensors. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
open PreF Coefficients TensorProduct NativeLeading
variable {I X : Type*} [AddCommGroup X]
variable (D : RootDatum I X)

/-- A finite word-length rectangle; no independence of its generators is asserted. -/
def truncation (m n : ℕ) : Submodule Coefficients.Ring
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  Submodule.span Coefficients.Ring
    {z | ∃ a b : List I, a.length ≤ m ∧ b.length ≤ n ∧ z = wordTensor D a b}

theorem wordTensor_mem_truncation (a b : List I) (m n : ℕ)
    (ha : a.length ≤ m) (hb : b.length ≤ n) : wordTensor D a b ∈ truncation D m n :=
  Submodule.subset_span ⟨a, b, ha, hb, rfl⟩

theorem truncation_mono {m n m' n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    truncation D m n ≤ truncation D m' n' := by
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, ha, hb, rfl⟩
  exact wordTensor_mem_truncation D a b m' n' (ha.trans hm) (hb.trans hn)

/-- Finite colours suffice for finite generation over the covering ring. -/
theorem truncation_fg [Finite I] (m n : ℕ) : (truncation D m n).FG := by
  apply Submodule.fg_span
  have hf := (List.finite_length_le I m).image2 (wordTensor D) (List.finite_length_le I n)
  apply hf.subset
  rintro z ⟨a, b, ha, hb, rfl⟩
  exact ⟨a, ha, b, hb, rfl⟩

section Quotient
variable [DecidableEq I] [DecidableEq X] [Finite I]
variable (hD : D.toSuperCartanDatum.BarConsistent)

/-- Every accepted correction belongs to the quotient image of the finite rectangle. -/
theorem lowerBidegree_le_map_truncation (Λ Μ : X) {a b m n : ℕ}
    (ha : a ≤ m + 1) (hb : b ≤ n + 1) :
    lowerBidegree D hD Λ Μ a b ≤
      (truncation D m n).map (toIntegrableTensor D hD Λ Μ) := by
  apply Submodule.span_le.mpr
  rintro z ⟨u, v, hu, hv, rfl⟩
  refine ⟨wordTensor D u v, wordTensor_mem_truncation D u v m n (by omega) (by omega), ?_⟩
  rfl

/-- A valid whole-span filtration comparison: all corrections remain in the same
finite quotient-injectivity domain as the leading terms. This is NOT injectivity. -/
theorem cyclic_truncation (Λ Μ : X) (s : Bool) (m n : ℕ) :
    (truncation D m n).map (cyclic D hD Λ Μ s) ≤
      (truncation D m n).map (toIntegrableTensor D hD Λ Μ) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, ha, hb, rfl⟩
  change cyclic D hD Λ Μ s (wordTensor D a b) ∈
    (truncation D m n).map (toIntegrableTensor D hD Λ Μ)
  obtain ⟨_, r, hr, he⟩ := cyclic_wordTensor_leading D hD Λ Μ s a b
  rw [he]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ ⟨wordTensor D a b,
      wordTensor_mem_truncation D a b m n ha hb, rfl⟩)
    (lowerBidegree_le_map_truncation D hD Λ Μ
      (ha.trans (Nat.le_succ _)) (hb.trans (Nat.le_succ _)) hr)

/-- One threshold detects the entire finite rectangle, including every native correction. -/
theorem truncation_quotient_injective_bound (m n : ℕ) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ Μ : X, (∀ i, B ≤ D.h i Λ) → (∀ i, B ≤ D.h i Μ) →
      Set.InjOn (toIntegrableTensor D hD Λ Μ) (truncation D m n) :=
  fg_toIntegrableTensor_injective_bound D hD _ (truncation_fg D m n)

end Quotient

/-- Every actual tensor has a finite rectangular word bound. -/
theorem exists_truncation (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring]
    D.serreF Coefficients.q pi) : ∃ m n, z ∈ truncation D m n := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
    obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
    induction x using induction_monomial with
    | zero => exact ⟨0, 0, by simp⟩
    | add x x' hx hx' =>
      obtain ⟨m, n, hm⟩ := hx
      obtain ⟨m', n', hm'⟩ := hx'
      refine ⟨max m m', max n n', ?_⟩
      simpa only [map_add, add_tmul] using Submodule.add_mem _
        (truncation_mono D (le_max_left _ _) (le_max_left _ _) hm)
        (truncation_mono D (le_max_right _ _) (le_max_right _ _) hm')
    | smul c x hx =>
      obtain ⟨m, n, hm⟩ := hx
      exact ⟨m, n, by simpa only [map_smul, smul_tmul, tmul_smul] using Submodule.smul_mem _ c hm⟩
    | word a =>
      induction y using induction_monomial with
      | zero => exact ⟨0, 0, by simp⟩
      | word b => exact ⟨a.length, b.length, wordTensor_mem_truncation D a b _ _ le_rfl le_rfl⟩
      | add y y' hy hy' =>
        obtain ⟨m, n, hm⟩ := hy
        obtain ⟨m', n', hm'⟩ := hy'
        refine ⟨max m m', max n n', ?_⟩
        simpa only [map_add, tmul_add] using Submodule.add_mem _
          (truncation_mono D (le_max_left _ _) (le_max_left _ _) hm)
          (truncation_mono D (le_max_right _ _) (le_max_right _ _) hm')
      | smul c y hy =>
        obtain ⟨m, n, hm⟩ := hy
        exact ⟨m, n, by simpa only [map_smul, tmul_smul] using Submodule.smul_mem _ c hm⟩
  | add x y hx hy =>
    obtain ⟨m, n, hm⟩ := hx
    obtain ⟨m', n', hm'⟩ := hy
    exact ⟨max m m', max n n', Submodule.add_mem _
      (truncation_mono D (le_max_left _ _) (le_max_left _ _) hm)
      (truncation_mono D (le_max_right _ _) (le_max_right _ _) hm')⟩

/-- An arbitrary finite covering-ring span fits in one finite rectangle. -/
theorem finite_span_le_truncation (S : Finset (D.serreF Coefficients.q pi ⊗[Coefficients.Ring]
    D.serreF Coefficients.q pi)) :
    ∃ m n, Submodule.span Coefficients.Ring (S : Set _) ≤ truncation D m n := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | @insert z S hz ih =>
    obtain ⟨m, n, hm⟩ := ih
    obtain ⟨m', n', hz'⟩ := exists_truncation D z
    refine ⟨max m m', max n n', Submodule.span_le.mpr ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact truncation_mono D (le_max_right _ _) (le_max_right _ _) hz'
    · exact truncation_mono D (le_max_left _ _) (le_max_left _ _)
        (hm (Submodule.subset_span hx))

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
