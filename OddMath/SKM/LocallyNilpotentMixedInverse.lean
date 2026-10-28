import OddMath.SKM.RouquierHomMixedRational
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Inputwise locally finite mixed coefficients

Module-level local inverse assembly for `SwappedHomInversion.md` §3 (2)–(3).
Bounds depend on individual inputs. The odd ordered sum reuses the finite
paired-sum identity. Signed intertwiners are treated at module level only;
assembly on the Hom supercategory and bending (4)–(5) remain open.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.SKM
variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

private theorem one_sub_geom (z : Module.End k V) (n : ℕ) :
    (1 - z) * (∑ r ∈ Finset.range n, z ^ r) = 1 - z ^ n := by
  rw [← neg_sub z 1, neg_mul, mul_geom_sum]
  exact neg_sub _ _

/-- Inputwise nilpotence suffices; no common exponent is chosen. -/
theorem locallyNilpotent_one_sub_bijective (z : Module.End k V)
    (hz : ∀ v, ∃ n : ℕ, (z ^ n) v = 0) : Function.Bijective (1 - z : Module.End k V) := by
  have ker : ∀ v, (1 - z : Module.End k V) v = 0 → v = 0 := by
    intro v hv
    have he : z v = v := (sub_eq_zero.mp hv).symm
    have hp (n : ℕ) : (z ^ n) v = v := by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [pow_succ', Module.End.mul_apply, ih] using he
    obtain ⟨n, hn⟩ := hz v
    exact (hp n).symm.trans hn
  constructor
  · intro a b hab
    exact sub_eq_zero.mp (ker (a - b) (by rw [map_sub, hab, sub_self]))
  · intro v
    obtain ⟨n, hn⟩ := hz v
    refine ⟨(∑ r ∈ Finset.range n, z ^ r) v, ?_⟩
    change ((1 - z) * (∑ r ∈ Finset.range n, z ^ r)) v = v
    rw [one_sub_geom]
    simp [hn]

/-- Inverting a unit minus an inputwise locally nilpotent commuting operator. -/
theorem localMixedEven_bijective (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : Commute (x : Module.End k V) y)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) :
    Function.Bijective ((x : Module.End k V) - y) := by
  let z : Module.End k V := (↑x⁻¹ : Module.End k V) * y
  have hz : ∀ v, ∃ n : ℕ, (z ^ n) v = 0 := by
    intro v
    obtain ⟨n, hn⟩ := hy v
    refine ⟨n, ?_⟩
    simp [z, h.units_inv_left.mul_pow, Module.End.mul_apply, hn]
  have hx : Function.Bijective (x : Module.End k V) := by
    constructor
    · intro a b hab
      have := congrArg (fun v => (↑x⁻¹ : Module.End k V) v) hab
      simpa only [← Module.End.mul_apply, x.inv_mul, Module.End.one_apply] using this
    · intro v
      exact ⟨(↑x⁻¹ : Module.End k V) v, by
        rw [← Module.End.mul_apply, x.mul_inv, Module.End.one_apply]⟩
  have hf : (x : Module.End k V) - y = (x : Module.End k V) * (1 - z) := by
    simp [z, mul_sub, ← mul_assoc]
  rw [hf]
  exact hx.comp (locallyNilpotent_one_sub_bijective z hz)

/-- The assembled linear inverse, with no bound in its type. -/
def localMixedEvenInverse (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : Commute (x : Module.End k V) y)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) : Module.End k V :=
  (LinearEquiv.ofBijective _ (localMixedEven_bijective x y h hy)).symm.toLinearMap

theorem localMixedEvenInverse_left (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : Commute (x : Module.End k V) y)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) :
    ((x : Module.End k V) - y) * localMixedEvenInverse x y h hy = 1 := by
  ext v
  exact (LinearEquiv.ofBijective _ (localMixedEven_bijective x y h hy)).apply_symm_apply v

theorem localMixedEvenInverse_right (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : Commute (x : Module.End k V) y)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) :
    localMixedEvenInverse x y h hy * ((x : Module.End k V) - y) = 1 := by
  ext v
  exact (LinearEquiv.ofBijective _ (localMixedEven_bijective x y h hy)).symm_apply_apply v

/-- Every annihilating bound gives the same inverse value, so the pointwise
finite series is additive and linear even when bounds vary with the input. -/
theorem localMixedEvenInverse_expansion (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : Commute (x : Module.End k V) y)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) (v : V) (n : ℕ) (hn : (y ^ n) v = 0) :
    localMixedEvenInverse x y h hy v =
      (∑ r ∈ Finset.range n, (↑x⁻¹ : Module.End k V) ^ (r + 1) * y ^ r) v := by
  let z : Module.End k V := (↑x⁻¹ : Module.End k V) * y
  have hi := h.units_inv_left
  have hs : (∑ r ∈ Finset.range n, (↑x⁻¹ : Module.End k V) ^ (r + 1) * y ^ r) =
      (↑x⁻¹ : Module.End k V) * (∑ r ∈ Finset.range n, z ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [z, hi.mul_pow, ← mul_assoc, ← pow_succ']
  have hd : ((x : Module.End k V) - y) * (↑x⁻¹ : Module.End k V) = 1 - z := by
    rw [sub_mul, x.mul_inv, ← hi.eq]
  apply (localMixedEven_bijective x y h hy).injective
  change (((x : Module.End k V) - y) * localMixedEvenInverse x y h hy) v = _
  rw [localMixedEvenInverse_left, hs]
  change v = ((((x : Module.End k V) - y) *
    ((↑x⁻¹ : Module.End k V) * (∑ r ∈ Finset.range n, z ^ r))) v)
  rw [← mul_assoc, hd, one_sub_geom]
  simp [z, hi.mul_pow, Module.End.mul_apply, hn]

/-- The assembled inverse is the ring inverse of the prescribed denominator. -/
theorem localMixedEvenInverse_rational (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : Commute (x : Module.End k V) y)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) :
    IsUnit ((x : Module.End k V) - y) ∧
      Ring.inverse ((x : Module.End k V) - y) = localMixedEvenInverse x y h hy := by
  let u : (Module.End k V)ˣ :=
    ⟨(x : Module.End k V) - y, localMixedEvenInverse x y h hy,
      localMixedEvenInverse_left x y h hy, localMixedEvenInverse_right x y h hy⟩
  exact ⟨⟨u, rfl⟩, Ring.inverse_unit u⟩

theorem localMixed_square_nilpotent (y : Module.End k V)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) :
    ∀ v, ∃ n : ℕ, ((y ^ 2) ^ n) v = 0 := by
  intro v
  obtain ⟨n, hn⟩ := hy v
  refine ⟨n, ?_⟩
  rw [← pow_mul]
  exact Module.End.pow_map_zero_of_le (by omega : n ≤ 2 * n) hn

/-- The odd coefficient uses the prescribed square denominator, not an inverse
of `x-y`. Its square-denominator inverse is linear with input-dependent bounds. -/
def localMixedOddCoefficient (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : (x : Module.End k V) * y = -(y * x))
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) : Module.End k V :=
  ((x : Module.End k V) - y) * localMixedEvenInverse (x ^ 2) (y ^ 2)
    ((mixedOdd_square_commute _ _ h).pow_left 2) (localMixed_square_nilpotent y hy)

theorem localMixedOddCoefficient_rational (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : (x : Module.End k V) * y = -(y * x))
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) :
    IsUnit ((x : Module.End k V) ^ 2 - y ^ 2) ∧
      localMixedOddCoefficient x y h hy =
        ((x : Module.End k V) - y) * Ring.inverse ((x : Module.End k V) ^ 2 - y ^ 2) := by
  have he := localMixedEvenInverse_rational (x ^ 2) (y ^ 2)
    ((mixedOdd_square_commute _ _ h).pow_left 2) (localMixed_square_nilpotent y hy)
  exact ⟨he.1, congrArg (((x : Module.End k V) - y) * ·) he.2.symm⟩

/-- Signed ordered expansion with any bound annihilating this input. The
bound `2*n` need not annihilate the operator on other inputs. -/
theorem localMixedOddCoefficient_expansion (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : (x : Module.End k V) * y = -(y * x))
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0) (v : V) (n : ℕ) (hn : (y ^ n) v = 0) :
    localMixedOddCoefficient x y h hy v =
      (∑ r ∈ Finset.range (2 * n), (-1 : Module.End k V) ^ r *
        (↑x⁻¹ : Module.End k V) ^ (r + 1) * y ^ r) v := by
  have hs : ((y ^ 2) ^ n) v = 0 := by
    rw [← pow_mul]
    exact Module.End.pow_map_zero_of_le (by omega : n ≤ 2 * n) hn
  have he := localMixedEvenInverse_expansion (x ^ 2) (y ^ 2)
    ((mixedOdd_square_commute _ _ h).pow_left 2) (localMixed_square_nilpotent y hy) v n hs
  simp only [localMixedOddCoefficient, Module.End.mul_apply]
  rw [he]
  simp only [Units.inv_pow_eq_pow_inv, ← pow_mul]
  change (((x : Module.End k V) - y) * _) v = _
  rw [mixedOdd_paired_sum x y h n]

section Intertwining
variable {W : Type*} [AddCommGroup W] [Module k W]

/-- Inverses transport through a signed intertwiner of their denominators.
This also covers odd morphisms; no invertibility of the intertwiner is needed. -/
theorem linearInverse_signed_intertwine
    (d a : Module.End k V) (e b : Module.End k W)
    (ha : d * a = 1) (hb : b * e = 1)
    (f : V →ₗ[k] W) (c : k) (hc : c * c = 1)
    (hf : ∀ v, f (d v) = c • e (f v)) :
    ∀ v, f (a v) = c • b (f v) := by
  intro v
  have ht := congrArg (fun w => c • b w) (hf (a v))
  have hda : d (a v) = v := congrArg (fun t : Module.End k V => t v) ha
  have hbe (w : W) : b (e w) = w := congrArg (fun t : Module.End k W => t w) hb
  simpa only [hda, map_smul, hbe, smul_smul, hc, one_smul] using ht.symm

/-- Signed compatibility for the assembled even coefficient follows from the
two dot intertwinings, with the same sign on both dots. -/
theorem localMixedEvenInverse_intertwine
    (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : Commute (x : Module.End k V) y)
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0)
    (x' : (Module.End k W)ˣ) (y' : Module.End k W)
    (h' : Commute (x' : Module.End k W) y')
    (hy' : ∀ w, ∃ n : ℕ, (y' ^ n) w = 0)
    (f : V →ₗ[k] W) (c : k) (hc : c * c = 1)
    (hx : ∀ v, f ((x : Module.End k V) v) = c • (x' : Module.End k W) (f v))
    (hf : ∀ v, f (y v) = c • y' (f v)) (v : V) :
    f (localMixedEvenInverse x y h hy v) =
      c • localMixedEvenInverse x' y' h' hy' (f v) := by
  apply linearInverse_signed_intertwine _ _ _ _
    (localMixedEvenInverse_left x y h hy) (localMixedEvenInverse_right x' y' h' hy')
    f c hc _ v
  intro w
  simp only [LinearMap.sub_apply, map_sub, hx, hf, smul_sub]

/-- The square denominator is even under simultaneous signed dot transport;
the odd rational coefficient retains precisely that sign. -/
theorem localMixedOddCoefficient_intertwine
    (x : (Module.End k V)ˣ) (y : Module.End k V)
    (h : (x : Module.End k V) * y = -(y * x))
    (hy : ∀ v, ∃ n : ℕ, (y ^ n) v = 0)
    (x' : (Module.End k W)ˣ) (y' : Module.End k W)
    (h' : (x' : Module.End k W) * y' = -(y' * x'))
    (hy' : ∀ w, ∃ n : ℕ, (y' ^ n) w = 0)
    (f : V →ₗ[k] W) (c : k) (hc : c * c = 1)
    (hx : ∀ v, f ((x : Module.End k V) v) = c • (x' : Module.End k W) (f v))
    (hf : ∀ v, f (y v) = c • y' (f v)) (v : V) :
    f (localMixedOddCoefficient x y h hy v) =
      c • localMixedOddCoefficient x' y' h' hy' (f v) := by
  have hs := localMixedEvenInverse_intertwine (x ^ 2) (y ^ 2)
    ((mixedOdd_square_commute _ _ h).pow_left 2) (localMixed_square_nilpotent y hy)
    (x' ^ 2) (y' ^ 2) ((mixedOdd_square_commute _ _ h').pow_left 2)
    (localMixed_square_nilpotent y' hy') f 1 (one_mul 1)
    (by intro w; simp [pow_two, Module.End.mul_apply, hx, smul_smul, hc])
    (by intro w; simp [pow_two, Module.End.mul_apply, hf, smul_smul, hc]) v
  simp only [one_smul] at hs
  simp only [localMixedOddCoefficient, Module.End.mul_apply, LinearMap.sub_apply,
    map_sub, hx, hf, hs, smul_sub]
end Intertwining
end OddMath.SKM
