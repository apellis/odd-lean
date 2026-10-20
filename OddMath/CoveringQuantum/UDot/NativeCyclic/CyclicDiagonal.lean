/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NativeCyclic.CyclicDegree

/-! Finite, well-defined diagonal unit operations on the actual Serre tensor. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
open PreF Coefficients TensorProduct NativeLeading
variable {I X : Type*} [AddCommGroup X]
variable (D : RootDatum I X)

/-- Equal formal degrees mean equal multiplicities, not equal root images. -/
theorem amplitude_eq_of_wordWeight_eq (s : Bool) (Λ : X) {a b : List I}
    (h : wordWeight a = wordWeight b) :
    TensorPositive.amplitude D s Λ a = TensorPositive.amplitude D s Λ b := by
  classical
  have hp : a.Perm b := List.perm_iff_count.mpr fun i => by
    simpa only [wordWeight_apply] using congrArg (fun ν => ν i) h
  exact (hp.map _).prod_eq

/-- The native coefficient is constant on genuine formal bidegrees. -/
theorem leadingScalar_eq_of_wordWeight_eq (Λ Μ : X) (s : Bool) {a b a' b' : List I}
    (ha : wordWeight a = wordWeight a') (hb : wordWeight b = wordWeight b') :
    leadingScalar D Λ Μ s a b = leadingScalar D Λ Μ s a' b' := by
  unfold leadingScalar
  rw [amplitude_eq_of_wordWeight_eq D s Λ hb, hb,
    amplitude_eq_of_wordWeight_eq D false _ ha]

/-- A representative is used only to name the scalar; its independence is proved above. -/
def degreeWord (ν : I →₀ ℕ) : List I := by
  classical
  exact if h : ∃ w : List I, wordWeight w = ν then h.choose else []

theorem degreeWord_weight (w : List I) : wordWeight (degreeWord (wordWeight w)) = wordWeight w := by
  classical
  have h : ∃ v : List I, wordWeight v = wordWeight w := ⟨w, rfl⟩
  simp only [degreeWord, dite_eq_left h]
  exact h.choose_spec

/-- A unit for every formal bidegree, in the actual covering ring with zero divisors. -/
def scalarUnit (Λ Μ : X) (s : Bool) (α β : I →₀ ℕ) : Coefficients.Ringˣ :=
  (leadingScalar_isUnit D Λ Μ s (degreeWord α) (degreeWord β)).unit

@[simp] theorem scalarUnit_word (Λ Μ : X) (s : Bool) (a b : List I) :
    (scalarUnit D Λ Μ s (wordWeight a) (wordWeight b) : Coefficients.Ring) =
      leadingScalar D Λ Μ s a b := by
  rw [scalarUnit, IsUnit.unit_spec]
  exact leadingScalar_eq_of_wordWeight_eq D Λ Μ s (degreeWord_weight a) (degreeWord_weight b)

variable [Finite I] (hD : D.toSuperCartanDatum.BarConsistent)

/-- Only grades represented in the finite square are needed. -/
def grades (N : ℕ) : Finset (I →₀ ℕ) := by
  classical
  exact (List.finite_length_le I N).toFinset.image wordWeight

theorem wordWeight_mem_grades (N : ℕ) (w : List I) (hw : w.length ≤ N) :
    wordWeight w ∈ grades (I := I) N := by
  classical
  exact Finset.mem_image.mpr ⟨w, by simpa using hw, rfl⟩

/-- A finite sum of genuine descended projectors, hence a well-defined linear map. -/
def diagonal (N : ℕ) (c : (I →₀ ℕ) → (I →₀ ℕ) → Coefficients.Ring) :
    Module.End Coefficients.Ring
      (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  ∑ α ∈ grades (I := I) N, ∑ β ∈ grades (I := I) N, c α β • bidegree D hD α β

/-- The finite diagonal acts with exactly the specified scalar on every word in the square. -/
theorem diagonal_word (N : ℕ) (c : (I →₀ ℕ) → (I →₀ ℕ) → Coefficients.Ring)
    (a b : List I) (ha : a.length ≤ N) (hb : b.length ≤ N) :
    diagonal D hD N c (wordTensor D a b) =
      c (wordWeight a) (wordWeight b) • wordTensor D a b := by
  classical
  simp only [diagonal, LinearMap.sum_apply, LinearMap.smul_apply, bidegree_wordTensor]
  simp only [ite_and, smul_ite, smul_zero]
  simp [wordWeight_mem_grades N a ha, wordWeight_mem_grades N b hb]

/-- Any diagonal coefficients preserve every smaller word rectangle. -/
theorem diagonal_mem_truncation (N m n : ℕ) (hm : m ≤ N) (hn : n ≤ N)
    (c : (I →₀ ℕ) → (I →₀ ℕ) → Coefficients.Ring)
    {z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi}
    (hz : z ∈ truncation D m n) : diagonal D hD N c z ∈ truncation D m n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    rw [diagonal_word D hD N c a b (ha.trans hm) (hb.trans hn)]
    exact Submodule.smul_mem _ _ (wordTensor_mem_truncation D a b m n ha hb)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- Inverse unit coefficients give an actual left inverse on the entire square span. -/
theorem diagonal_inverse (N : ℕ) (u : (I →₀ ℕ) → (I →₀ ℕ) → Coefficients.Ringˣ)
    {z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi}
    (hz : z ∈ truncation D N N) :
    diagonal D hD N (fun α β => ↑(u α β)⁻¹)
      (diagonal D hD N (fun α β => ↑(u α β)) z) = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    rw [diagonal_word D hD N _ a b ha hb, map_smul,
      diagonal_word D hD N _ a b ha hb, smul_smul]
    simp
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul c x hx ih => simp only [map_smul, ih]

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
