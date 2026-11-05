import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixInteger

/-! # Degrees of the finite inverse window contractions

The coefficient calculation in SwappedHomInversion §4, equation (7), uses
every window coordinate of the literal finite kernel inverse. The unit
orientation extracts a coordinate after an arbitrary unit/dot column;
the cap orientation inserts a coordinate before an arbitrary dot/cap row.
These raw contractions have degree `2 dᵢ (n-m)` and `2 dᵢ (m-n)` respectively.
This calculation does not identify them with a chosen content local `g'`.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Every window coordinate of the positive raw matrix inverse. -/
def positiveKernelWindowInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k] (v ⟶ t) :=
  LinearMap.proj (some m) ∘ₗ (positiveKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap

/-- Every window column of the negative raw matrix inverse. -/
def negativeKernelWindowInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : Fin (contentCapCount D cutoff i (t.word : Multiset I))) :
    (v ⟶ t) →ₗ[k] IndResKernel.Component (k := k) (append D Sc cutoff i) v t :=
  (negativeKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap ∘ₗ
    LinearMap.single k (fun a => (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) (some m)

/-- Positive boundary: inverse window row `m` after unit/dot column `n`. -/
def positiveKernelBoundary (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (n : ℕ) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  positiveKernelWindowInverse D Sc cutoff i v t hh m ∘ₗ
    unitKernelComponent D Sc cutoff i n v t

/-- Negative boundary: dot/cap row `m` after inverse window column `n`. -/
def negativeKernelBoundary (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (n : Fin (contentCapCount D cutoff i (t.word : Multiset I))) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  capKernelComponent D Sc cutoff i m v t ∘ₗ
    negativeKernelWindowInverse D Sc cutoff i v t hh n

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The positive inverse window row has raw degree `-2 dᵢ m`. -/
theorem positiveKernelWindowInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) q) :
    positiveKernelWindowInverse D Sc cutoff i v t hh m y ∈
      oldDegree D sy Sc hc cutoff v.word t.word (q - 2 * sy.d i * m.val) := by
  exact (OddMath.IntegerMatrix.Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh hy) (some m)

/-- Inserting window column `m` gives raw inverse degree `-2 dᵢ m`. -/
theorem negativeKernelWindowInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegree D sy Sc hc cutoff v.word t.word q) :
    negativeKernelWindowInverse D Sc cutoff i v t hh m y ∈
      representedKernelDegree D Sc cutoff sy hc i v t (q - 2 * sy.d i * m.val) := by
  classical
  change (negativeKernelEquiv D Sc cutoff i v t hh).symm
    (Pi.single (some m) y) ∈ _
  apply negativeKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh
  apply (OddMath.IntegerMatrix.Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  by_cases ha : a = some m
  · subst a
    simp only [Pi.single_eq_same]
    change y ∈ oldDegree D sy Sc hc cutoff v.word t.word
      (q - 2 * sy.d i * m.val + 2 * sy.d i * m.val)
    simpa only [sub_add_cancel] using hy
  · rw [Pi.single_eq_of_ne ha]
    exact Submodule.zero_mem _

/-- All positive contractions have the difference degree, also outside the window. -/
theorem positiveKernelBoundary_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (n : ℕ) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegree D sy Sc hc cutoff v.word t.word q) :
    positiveKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegree D sy Sc hc cutoff v.word t.word (q + 2 * sy.d i * ((n : ℤ) - m.val)) := by
  have h := positiveKernelWindowInverse_degree D Sc cutoff sy hc i v t hh m
    (unitKernelComponent_degree D Sc cutoff sy hc i v t n hy)
  have he : q + 2 * sy.d i * n - 2 * sy.d i * m.val =
      q + 2 * sy.d i * ((n : ℤ) - m.val) := by ring
  simpa only [positiveKernelBoundary, LinearMap.comp_apply, he] using h

/-- All negative contractions have the difference degree, also outside the window. -/
theorem negativeKernelBoundary_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (n : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegree D sy Sc hc cutoff v.word t.word q) :
    negativeKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegree D sy Sc hc cutoff v.word t.word (q + 2 * sy.d i * ((m : ℤ) - n.val)) := by
  have h := capKernelComponent_degree D Sc cutoff sy hc i v t m
    (negativeKernelWindowInverse_degree D Sc cutoff sy hc i v t hh n hy)
  have he : q - 2 * sy.d i * n.val + 2 * sy.d i * m =
      q + 2 * sy.d i * ((m : ℤ) - n.val) := by ring
  simpa only [negativeKernelBoundary, LinearMap.comp_apply, he] using h

omit hc in

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
