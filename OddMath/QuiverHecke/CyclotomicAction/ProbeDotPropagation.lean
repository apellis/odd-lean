import OddMath.QuiverHecke.CyclotomicAction.Intertwiner

/-! # Kernel propagation for probe dots

The equal-colour step of `InvertibleDotProbe.md` §3 needs only the kernel
of the next dot. The nilHecke intertwiner carries that kernel into the
kernel of the preceding dot; its square then detects the original vector.
No finite-dimensionality or generalized zero-primary decomposition is used.
-/
namespace OddMath.QuiverHecke.SignedNilHecke
variable {B : Type*} [Ring B]

/-- The distinct-colour dot-slide and quadratic relation detect the next-dot
kernel once the positive next-dot terms are factored on the right. This is
the algebraic kernel step in `InvertibleDotProbe.md` §3, without commuting
any coefficient or localizing the quadratic polynomial. -/
theorem distinct_dot_kernel {u v w a b t r z : B} (d : ℕ)
    (hu : Function.Injective (fun x : B => u * x))
    (hw : Function.Injective (fun x : B => w * x))
    (ht : Function.Injective (fun x : B => t * x))
    (slide : w * a = a * v) (quadratic : b * a = t * u ^ d + r * v)
    (hz : v * z = 0) : z = 0 := by
  have ha : a * z = 0 := by
    apply hw
    rw [mul_zero, ← mul_assoc, slide, mul_assoc, hz, mul_zero]
  have htu : t * (u ^ d * z) = 0 := by
    have h := congrArg (fun c : B => c * z) quadratic
    simpa only [mul_assoc, ha, mul_zero, add_mul, hz, add_zero] using h.symm
  have hud : u ^ d * z = 0 := ht (by simpa only [mul_zero] using htu)
  have hpow : ∀ n : ℕ, Function.Injective (fun x : B => u ^ n * x) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, one_mul] using Function.injective_id
    | succ n ih =>
      intro x y h
      apply ih
      apply hu
      simpa only [pow_succ', mul_assoc] using h
  exact hpow d (by simpa only [mul_zero] using hud)

theorem EvenTwo.right_mul_eq_zero {u v T z : B} (h : EvenTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) (hz : v * z = 0) : z = 0 := by
  have hp : phiEven u v T * z = 0 := by
    apply hu
    rw [mul_zero, ← mul_assoc, h.x_mul_phiEven, mul_assoc, hz, mul_zero]
  have hs := congrArg (fun a : B => a * z) h.phiEven_mul_phiEven
  simpa only [mul_assoc, hp, mul_zero, one_mul] using hs.symm

theorem EvenTwo.right_mul_injective {u v T : B} (h : EvenTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) :
    Function.Injective (fun x : B => v * x) := by
  intro x y hxy
  apply sub_eq_zero.mp
  exact h.right_mul_eq_zero hu (by rw [mul_sub, hxy, sub_self])

theorem OddTwo.right_mul_eq_zero {u v T z : B} (h : OddTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) (hz : v * z = 0) : z = 0 := by
  have hp : phiOdd u v T * z = 0 := by
    apply hu
    rw [mul_zero, ← mul_assoc, h.x_mul_phiOdd, neg_mul, mul_assoc, hz,
      mul_zero, neg_zero]
  have hvu : v * (u * z) = 0 := by
    rw [← mul_assoc, h.vu', neg_mul, mul_assoc, hz, mul_zero, neg_zero]
  have hs := congrArg (fun a : B => a * z) h.phiOdd_mul_phiOdd
  have huu : u * (u * z) = 0 := by
    simpa only [mul_assoc, hp, mul_zero, sub_mul, mul_sub, hz,
      zero_sub, mul_neg, hvu, neg_zero, sub_neg_eq_add, zero_add] using hs.symm
  apply hu
  rw [mul_zero]
  exact hu (by simpa only [mul_zero] using huu)

theorem OddTwo.right_mul_injective {u v T : B} (h : OddTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) :
    Function.Injective (fun x : B => v * x) := by
  intro x y hxy
  apply sub_eq_zero.mp
  exact h.right_mul_eq_zero hu (by rw [mul_sub, hxy, sub_self])

end OddMath.QuiverHecke.SignedNilHecke
