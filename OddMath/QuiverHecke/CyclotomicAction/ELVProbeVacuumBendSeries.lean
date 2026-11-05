import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumBendMonomials
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralBend
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenCentralBend

/-! # The ordered odd vacuum bend series

SwappedHomInversion §3 (4)–(5): the finite ordered series of prescribed
negative pre-caps and dotted post-units equals the evaluated A6 bend.
-/
noncomputable section
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction
universe u
local instance bendSeriesHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I) {muP nuR : X} (edgeP : -ΛP + D.α i = -muP)
  (edgeR : -ΛR + D.α i = nuR) (β : I →₀ ℕ)
variable (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR (-ΛR))
local instance bendSeriesProbeDotIso : IsIso (((probeOldRouquierFamily D Sc m ΛP hcP)).dot i edgeP) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m ΛP hcP i edgeP)

/-- The given chronological series keeps each negative pre-cap and
post-unit as the prescribed Hom maps before regular-probe evaluation. -/
def vacuumBendWordSum (N : ℕ) :=
  -∑ r ∈ Finset.range N, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) •
    (((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP (r + 1) (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) ≫
      SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR))

private theorem odd_coefficient (r : ℕ) :
    -((koszulSign (1 : ZMod 2) 1) ^ (r + 1)) = (-1 : ℤ) ^ r := by
  rw [koszulSign_one_one, pow_succ]
  ring

/-- At any given native reservoir nilpotence exponent, the actual
finite pre-cap/post-unit word sum is exactly the evaluated odd A6 bend.
The raw shifted pre-dot and raw reservoir unit/dot are retained. -/
theorem vacuumBendWordSum_odd (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D Sc m cutoff bound i (vacuumBendBlock D Sc m cutoff bound ΛR H) ^ n = 0) :
    vacuumBendWordSum D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H (2 * n) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      ProbeVacuumCap.evaluatedMixedBend D Sc m cutoff bound i hP (vacuumBendBlock D Sc m cutoff bound ΛR H) := by
  rw [ProbeVacuumCap.evaluatedMixedBend_odd_expansion D Sc m cutoff bound i hi hP (vacuumBendBlock D Sc m cutoff bound ΛR H) n hn]
  simp only [vacuumBendWordSum, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [vacuumBendMonomial_eq D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H hP hi (r + 1) r]
  have hs : -((koszulSign (D.parity i) (D.parity i)) ^ (r + 1)) = (-1 : ℤ) ^ r := by
    rw [hi, odd_coefficient]
  rw [← neg_zsmul, hs]
  congr 1

/-- Even colour: at any given native reservoir nilpotence exponent `n`, the actual
finite pre-cap/post-unit word sum of length `n` is exactly the evaluated even A6 bend. -/
theorem vacuumBendWordSum_even (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0)
    (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D Sc m cutoff bound i (vacuumBendBlock D Sc m cutoff bound ΛR H) ^ n = 0) :
    vacuumBendWordSum D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H n ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      ProbeVacuumCap.evaluatedMixedBend D Sc m cutoff bound i hP (vacuumBendBlock D Sc m cutoff bound ΛR H) := by
  rw [ProbeVacuumCap.evaluatedMixedBend_even_expansion D Sc m cutoff bound i hi hP (vacuumBendBlock D Sc m cutoff bound ΛR H) n hn]
  simp only [vacuumBendWordSum, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [vacuumBendMonomial_even D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H hP hi (r + 1) r]
  have hs : -((koszulSign (D.parity i) (D.parity i)) ^ (r + 1)) = (-1 : ℤ) := by
    rw [hi, koszulSign_zero_left, one_pow]
  rw [← neg_zsmul, hs]
  congr 1

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
