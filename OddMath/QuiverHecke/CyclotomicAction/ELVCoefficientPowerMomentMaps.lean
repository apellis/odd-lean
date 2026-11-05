import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerOddSeries

/-! # Full moment maps on the literal coefficient-power vacuum

The all-vector interpretation of the scalar reservoir series in
`SwappedVacuumNonpositiveBubbles.md`, §2. The actual ordinary unit,
signed induction dot and prescribed inverse row define the maps.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private abbrev coefficientProjection :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
private abbrev target (i : I) := mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩
private def dot (i : I) : Module.End k (target D Sc cutoff L i) :=
  inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    ((append D Sc cutoff i).obj ⟨[]⟩)
private def outputCoefficient (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    Module.End k (target D Sc cutoff L i) :=
  SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      (coefficientPowerVacuum D Sc cutoff L))).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a))

/-- The actual signed n-th-dot moment on every input vector of literal A/T. -/
def momentMap (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    Module.End k (CoefficientPowerQuotient (k := k) D cutoff L) :=
  (functional D Sc cutoff L i hN).comp
    ((dot D Sc cutoff L i ^ n).comp (unit D Sc cutoff L i))

private theorem unit_eq (i : I) (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    unit D Sc cutoff L i z = BalancedInduction.unit (append D Sc cutoff i)
      (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z) := by
  exact adjunctionUnit_total_apply D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    (⟨[]⟩ : OldCategory D Sc cutoff) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)

private theorem unit_coefficient (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    outputCoefficient D Sc cutoff L i a (unit D Sc cutoff L i z) =
      unit D Sc cutoff L i (coefficientProjection D cutoff L a * z) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let J := append D Sc cutoff i
  let f : (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ ⟨[]⟩ := coefficientEndomorphism D Sc cutoff [] a
  have h := LinearMap.congr_fun (BalancedInduction.unit_naturality J M.toFunctor f)
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)
  simp only [LinearMap.comp_apply] at h
  change outputCoefficient D Sc cutoff L i a
    (BalancedInduction.unit J M.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)) =
    BalancedInduction.unit J M.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      ((coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)) at h
  rw [empty_coefficient_action D Sc cutoff L a z] at h
  simpa only [unit_eq] using h

private theorem scalar_commuting_power {V : Type u} [AddCommGroup V] [Module k V]
    (d a : Module.End k V) (s : k) (h : d.comp a = s • (a.comp d)) (n : ℕ) :
    (d ^ n).comp a = s ^ n • (a.comp (d ^ n)) := by
  have h' : d.comp a = a.comp (s • d) := by simpa only [LinearMap.comp_smul] using h
  have hp := Module.End.commute_pow_left_of_commute h' n
  simpa only [smul_pow, LinearMap.comp_smul] using hp

private theorem sign_nsmul (p : ZMod 2) (n : ℕ) : sign k (n • p) = sign k p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, sign_add, ih, pow_succ]

private theorem dot_pow_coefficient (i : I) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) (n : ℕ) :
    (dot D Sc cutoff L i ^ n).comp (outputCoefficient D Sc cutoff L i a) =
      koszulSign (n • D.parity i) p •
        ((outputCoefficient D Sc cutoff L i a).comp (dot D Sc cutoff L i ^ n)) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let J := append D Sc cutoff i
  let f : J.obj (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ J.obj ⟨[]⟩ :=
    J.map (X := ⟨[]⟩) (Y := ⟨[]⟩) (coefficientEndomorphism D Sc cutoff [] a)
  have hf : f ∈ parity (R := k) _ _ p :=
    IsSuperfunctor.map_mem (F := J) (coefficientEndomorphism_mem D Sc cutoff [] ha)
  have h := (BalancedInduction.transformLinear_supernatural
    (oldAppendDot_supernatural D Sc cutoff i) M).naturality hf
  change (dot D Sc cutoff L i).comp (outputCoefficient D Sc cutoff L i a) =
    sign k (D.parity i * p) •
      ((outputCoefficient D Sc cutoff L i a).comp (dot D Sc cutoff L i)) at h
  have hp := scalar_commuting_power (dot D Sc cutoff L i) (outputCoefficient D Sc cutoff L i a)
    (sign k (D.parity i * p)) h n
  rw [← sign_nsmul] at hp
  have he : n • (D.parity i * p) = (n • D.parity i) * p := by
    simp only [nsmul_eq_mul]
    ring
  rw [he, ← koszulSign_smul (R := k)] at hp
  exact hp

/-- Full coefficient superlinearity of every higher moment map, with
its total parity and the original left coefficient order. -/
theorem momentMap_coefficient (i : I) (hN : 0 < cutoff i) (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    momentMap D Sc cutoff L i hN n (coefficientProjection D cutoff L a) =
      koszulSign ((n + (cutoff i - 1)) • D.parity i) p •
        (coefficientProjection D cutoff L a * signedMoment D Sc cutoff L i hN n) := by
  have hu := unit_coefficient D Sc cutoff L i a (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  rw [mul_one] at hu
  have hd := LinearMap.congr_fun (dot_pow_coefficient D Sc cutoff L i ha n)
    (unit D Sc cutoff L i 1)
  have h := congrArg (functional D Sc cutoff L i hN) hd
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  have hcap := functional_coefficient D Sc cutoff L i hN ha
    ((dot D Sc cutoff L i ^ n) (unit D Sc cutoff L i 1))
  change functional D Sc cutoff L i hN
    (outputCoefficient D Sc cutoff L i a ((dot D Sc cutoff L i ^ n) (unit D Sc cutoff L i 1))) =
    koszulSign ((cutoff i - 1) • D.parity i) p •
      (coefficientProjection D cutoff L a * signedMoment D Sc cutoff L i hN n) at hcap
  rw [map_zsmul, hcap] at h
  rw [smul_smul, ← koszulSign_add_left, ← add_nsmul] at h
  change functional D Sc cutoff L i hN
    ((dot D Sc cutoff L i ^ n) (outputCoefficient D Sc cutoff L i a (unit D Sc cutoff L i 1))) = _ at h
  rw [hu] at h
  exact h

private theorem unit_apply_mem (i : I) {p : ZMod 2}
    {z : CoefficientPowerQuotient (k := k) D cutoff L}
    (hz : z ∈ coefficientPowerParity D cutoff L p) :
    unit D Sc cutoff L i z ∈ (target D Sc cutoff L i).part p := by
  rw [unit_eq]
  have h := SVec.apply_mem_part (BalancedInduction.unit_mem (append D Sc cutoff i)
    (coefficientPowerVacuum D Sc cutoff L) (⟨[]⟩ : OldCategory D Sc cutoff))
      (coefficientPowerVacuumEmptyEquiv_mem D Sc cutoff L hz)
  change BalancedInduction.unit (append D Sc cutoff i)
    (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z) ∈
        (target D Sc cutoff L i).part (p + 0) at h
  simpa only [add_zero] using h

private theorem dot_pow_apply_mem (i : I) {p : ZMod 2}
    {z : target D Sc cutoff L i} (hz : z ∈ (target D Sc cutoff L i).part p) (n : ℕ) :
    (dot D Sc cutoff L i ^ n) z ∈ (target D Sc cutoff L i).part (p + n • D.parity i) := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply, zero_nsmul, add_zero] using hz
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := SVec.apply_mem_part (BalancedInduction.transformLinear_mem
      (oldAppendDot_supernatural D Sc cutoff i) (coefficientPowerVacuum D Sc cutoff L)
        ((append D Sc cutoff i).obj (⟨[]⟩ : OldCategory D Sc cutoff))) ih
    change dot D Sc cutoff L i ((dot D Sc cutoff L i ^ n) z) ∈
      (target D Sc cutoff L i).part ((p + n • D.parity i) + D.parity i) at h
    simpa only [succ_nsmul, add_assoc] using h

/-- The actual full moment map retains the total parity of its chosen
inverse row and all n signed dots. -/
theorem momentMap_mem (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    momentMap D Sc cutoff L i hN n ∈ parity (R := k)
      (coefficientPowerSpace D cutoff L) (coefficientPowerSpace D cutoff L)
        ((n + (cutoff i - 1)) • D.parity i) := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p z hz
  have hu := unit_apply_mem D Sc cutoff L i hz
  have hd := dot_pow_apply_mem D Sc cutoff L i hu n
  have h := SVec.apply_mem_part (functional_mem D Sc cutoff L i hN) hd
  change momentMap D Sc cutoff L i hN n z ∈
    (coefficientPowerSpace D cutoff L).part (p + ((n + (cutoff i - 1)) • D.parity i))
  change momentMap D Sc cutoff L i hN n z ∈
    (coefficientPowerSpace D cutoff L).part ((p + n • D.parity i) + (cutoff i - 1) • D.parity i) at h
  simpa only [add_nsmul, add_assoc] using h

private theorem homogeneous_lift {p : ZMod 2}
    {z : CoefficientPowerQuotient (k := k) D cutoff L}
    (hz : z ∈ coefficientPowerParity D cutoff L p) :
    ∃ a ∈ SKM.SYM.elvCoefficientParity D cutoff p, coefficientProjection D cutoff L a = z := by
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon z
  refine ⟨GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a,
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property, ?_⟩
  rw [← coefficientPowerSpace_projection D cutoff L p a]
  exact (SVec.mem_part_iff _).mp hz

private theorem homogeneous_comm {p q : ZMod 2}
    {a b : CoefficientPowerQuotient (k := k) D cutoff L}
    (ha : a ∈ coefficientPowerParity D cutoff L p)
    (hb : b ∈ coefficientPowerParity D cutoff L q) :
    a * b = koszulSign p q • (b * a) := by
  obtain ⟨a0, ha0, ea⟩ := homogeneous_lift D cutoff L ha
  obtain ⟨b0, hb0, eb⟩ := homogeneous_lift D cutoff L hb
  rw [← ea, ← eb]
  have h := congrArg (coefficientProjection D cutoff L) (ELVPScalar.elv_comm D cutoff ha0 hb0)
  simpa only [map_mul, map_zsmul] using h

/-- Every actual higher moment on every coefficient vector is the original
left multiplication by its proved scalar value on 1. No bubble-value
hypothesis or ordinary commutativity of A/T is used. -/
theorem momentMap_apply (i : I) (hN : 0 < cutoff i) (n : ℕ)
    (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    momentMap D Sc cutoff L i hN n z = signedMoment D Sc cutoff L i hN n * z := by
  have hvalue : signedMoment D Sc cutoff L i hN n ∈
      coefficientPowerParity D cutoff L ((n + (cutoff i - 1)) • D.parity i) := by
    have h := SVec.apply_mem_part (momentMap_mem D Sc cutoff L i hN n)
      (SetLike.one_mem_graded (coefficientPowerParity (k := k) D cutoff L))
    change signedMoment D Sc cutoff L i hN n ∈ coefficientPowerParity D cutoff L
      (0 + ((n + (cutoff i - 1)) • D.parity i)) at h
    simpa only [zero_add] using h
  have hh {p : ZMod 2} {a : CoefficientPowerQuotient (k := k) D cutoff L}
      (ha : a ∈ coefficientPowerParity D cutoff L p) :
      momentMap D Sc cutoff L i hN n a = signedMoment D Sc cutoff L i hN n * a := by
    obtain ⟨b, hb, rfl⟩ := homogeneous_lift D cutoff L ha
    have h := momentMap_coefficient D Sc cutoff L i hN n hb
    have hc := homogeneous_comm D cutoff L (coefficientPowerQuotient_mem D cutoff L hb) hvalue
    have hs : koszulSign ((n + (cutoff i - 1)) • D.parity i) p *
        koszulSign p ((n + (cutoff i - 1)) • D.parity i) = 1 := by
      rw [koszulSign_comm p _, koszulSign_mul_self]
    rw [hc, smul_smul, hs, one_smul] at h
    exact h
  have hz : z = (coefficientPowerSpace D cutoff L).proj 0 z +
      (coefficientPowerSpace D cutoff L).proj 1 z :=
    ((coefficientPowerSpace D cutoff L).proj_apply_add z).symm
  calc
    _ = momentMap D Sc cutoff L i hN n
        ((coefficientPowerSpace D cutoff L).proj 0 z + (coefficientPowerSpace D cutoff L).proj 1 z) :=
      congrArg (momentMap D Sc cutoff L i hN n) hz
    _ = _ := by
      rw [map_add, hh ((coefficientPowerSpace D cutoff L).proj_mem_part 0 z),
        hh ((coefficientPowerSpace D cutoff L).proj_mem_part 1 z), ← mul_add, ← hz]

/-- The same all-vector identity as an endomorphism equality, for use
when whiskering the source bubble map through a chosen word functor. -/
theorem momentMap_eq_mulLeft (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    momentMap D Sc cutoff L i hN n = LinearMap.mulLeft k (signedMoment D Sc cutoff L i hN n) := by
  apply LinearMap.ext
  intro z
  exact momentMap_apply D Sc cutoff L i hN n z

/-- The complete even-index odd-colour reservoir series, as literal
endomorphisms on every vector of the actual power quotient. -/
theorem momentMap_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    momentMap D Sc cutoff L i hN (cutoff i - 1 + 2 * r) =
      LinearMap.mulLeft k (completeCoefficient D cutoff L i r) := by
  rw [momentMap_eq_mulLeft, signedMoment_even D Sc cutoff L i hi hN r]

/-- The complete odd-index reservoir series as literal endomorphisms,
retaining the original left exterior coefficient. -/
theorem momentMap_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    momentMap D Sc cutoff L i hN (cutoff i - 1 + (2 * r + 1)) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r)) := by
  rw [momentMap_eq_mulLeft, signedMoment_odd D Sc cutoff L i hi hN r]

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
