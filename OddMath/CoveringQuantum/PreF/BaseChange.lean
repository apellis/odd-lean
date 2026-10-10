import OddMath.CoveringQuantum.PreF.GaugeForm

/-!
# Coefficient transport of the free bilinear form

The skew derivatives, bilinear form, and radical commute with coefficient
homomorphisms when the bicharacter and normalization are mapped accordingly.
-/

noncomputable section
namespace OddMath.CoveringQuantum.PreF

variable {k K I : Type*} [CommRing k] [CommRing K] [DecidableEq I]
  (φ : k →+* K) (χ : Bichar k I) (ψ : Bichar K I)
  (nm : I → k) (nm' : I → K)
  (hχ : ∀ i j, φ (χ i j) = ψ i j) (hn : ∀ i, φ (nm i) = nm' i)

omit [DecidableEq I] in
include hχ in
/-- Coefficient transport commutes with the diagonal twist. -/
theorem mapCoeffs_twist (i : I) (x : PreF k I) :
    FreeAlgebra.mapCoeffs φ (twist χ i x) = twist ψ i (FreeAlgebra.mapCoeffs φ x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 j => simp [θ, twist, FreeAlgebra.mapCoeffs_smul, hχ]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

include hχ in
/-- Coefficient transport commutes with the right skew derivative. -/
theorem mapCoeffs_rDeriv (i : I) (x : PreF k I) :
    FreeAlgebra.mapCoeffs φ (rDeriv χ i x) = rDeriv ψ i (FreeAlgebra.mapCoeffs φ x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 j =>
    change FreeAlgebra.mapCoeffs φ (rDeriv χ i (θ k j)) =
      rDeriv ψ i (FreeAlgebra.mapCoeffs φ (θ k j))
    rw [rDeriv_θ, show FreeAlgebra.mapCoeffs φ (θ k j) = θ K j from FreeAlgebra.mapCoeffs_ι φ j,
      rDeriv_θ]
    split_ifs <;> simp
  | mul a b ha hb =>
    rw [rDeriv_mul, map_add, map_mul, map_mul, ha, hb, mapCoeffs_twist φ χ ψ hχ,
      map_mul, rDeriv_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [DecidableEq I] in
/-- The counit commutes with a coefficient homomorphism. -/
theorem counit_mapCoeffs (x : PreF k I) : counit (FreeAlgebra.mapCoeffs φ x) = φ (counit x) :=
  FreeAlgebra.algebraMapInv_mapCoeffs φ x

include hχ hn in
/-- The two free bilinear forms agree after coefficient transport. -/
theorem form_mapCoeffs (x y : PreF k I) :
    form ψ nm' (FreeAlgebra.mapCoeffs φ x) (FreeAlgebra.mapCoeffs φ y) = φ (form χ nm x y) := by
  induction x using induction_right generalizing y with
  | algebraMap c => simp [form_algebraMap_left, counit_mapCoeffs, map_mul]
  | smul c x hx =>
    rw [FreeAlgebra.mapCoeffs_smul, LinearMap.map_smul₂, LinearMap.map_smul₂,
      smul_eq_mul, smul_eq_mul, map_mul, hx]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | mul_θ x i hx =>
    rw [map_mul, show FreeAlgebra.mapCoeffs φ (θ k i) = θ K i from FreeAlgebra.mapCoeffs_ι φ i,
      form_mul_θ, ← mapCoeffs_rDeriv φ χ ψ hχ, hx, form_mul_θ, map_mul, hn]

include hχ hn in
/-- Coefficient extension carries the free-form radical into the new radical. -/
theorem mapCoeffs_mem_radical {x : PreF k I} (hx : x ∈ radical χ nm) :
    FreeAlgebra.mapCoeffs φ x ∈ radical ψ nm' := by
  apply (mem_radical_iff ψ nm').mpr
  intro y
  induction y using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz, add_zero]
  | smul c y hy => simp only [map_smul, hy, smul_zero]
  | word w =>
    rw [← FreeAlgebra.mapCoeffs_wordBasis φ w, form_mapCoeffs φ χ ψ nm nm' hχ hn,
      (mem_radical_iff χ nm).mp hx, map_zero]

include hχ hn in
/-- An injective coefficient map also reflects the free-form radical. -/
theorem mapCoeffs_mem_radical_iff (hφ : Function.Injective φ) (x : PreF k I) :
    FreeAlgebra.mapCoeffs φ x ∈ radical ψ nm' ↔ x ∈ radical χ nm := by
  refine ⟨?_, mapCoeffs_mem_radical φ χ ψ nm nm' hχ hn⟩
  intro hx
  apply (mem_radical_iff χ nm).mpr
  intro y
  apply hφ
  rw [← form_mapCoeffs φ χ ψ nm nm' hχ hn, (mem_radical_iff ψ nm').mp hx, map_zero]

end OddMath.CoveringQuantum.PreF
