import Mathlib.Tactic.NoncommRing

/-! An even-cutoff ELV polynomial has a monic central multiple. These ring
identities do not assert exactness or projectivity of a cyclotomic action. -/
namespace OddMath.OddNilHecke.CyclotomicNorm
variable {R : Type*} [Ring R]

theorem exterior_term_square (x d q : R) (hd : d * d = 0)
    (hx : d * x = -(x * d)) (hqx : q * x = x * q)
    (hqd : q * d = d * q) : (x * d * q) * (x * d * q) = 0 := by
  calc
    (x * d * q) * (x * d * q) = x * (d * (q * x)) * d * q := by noncomm_ring
    _ = -(x * x * (d * d) * q * q) := by
      rw [hqx, ← mul_assoc d x q, hx]
      noncomm_ring [hqd]
    _ = 0 := by rw [hd]; simp

theorem conjugate_product (c u : R) (hu : u * u = 0)
    (hcu : c * u = u * c) : (c + u) * (c - u) = c * c := by
  noncomm_ring [hu, hcu]

theorem even_cutoff_multiple (x d q c : R) (hd : d * d = 0)
    (hx : d * x = -(x * d)) (hqx : q * x = x * q)
    (hqd : q * d = d * q) (hc : c * (x * d * q) = (x * d * q) * c) :
    (c + x * d * q) * (c - x * d * q) = c * c :=
  conjugate_product c (x * d * q) (exterior_term_square x d q hd hx hqx hqd) hc

/-- In the odd-intertwiner case the dot and its exterior coefficient both
pick up a minus sign. The even cyclotomic polynomial therefore transports
without changing its exterior parameter. -/
theorem even_cutoff_transport_neg (x y d e q r c b g : R)
    (hx : x * g = -(g * y)) (hd : d * g = -(g * e))
    (hq : q * g = g * r) (hc : c * g = g * b) :
    (c - x * d * q) * g = g * (b - y * e * r) := by
  have ht : (x * d * q) * g = g * (y * e * r) := by
    calc
      (x * d * q) * g = x * (d * (q * g)) := by noncomm_ring
      _ = x * (d * (g * r)) := by rw [hq]
      _ = x * ((d * g) * r) := by rw [mul_assoc]
      _ = -((x * g) * e * r) := by rw [hd]; noncomm_ring
      _ = g * (y * e * r) := by rw [hx]; noncomm_ring
  rw [sub_mul, hc, ht, mul_sub]

theorem even_cutoff_transport_pos (x y d e q r c b g : R)
    (hx : x * g = g * y) (hd : d * g = g * e)
    (hq : q * g = g * r) (hc : c * g = g * b) :
    (c - x * d * q) * g = g * (b - y * e * r) := by
  have ht : (x * d * q) * g = g * (y * e * r) := by
    calc
      (x * d * q) * g = x * (d * (q * g)) := by noncomm_ring
      _ = x * (d * (g * r)) := by rw [hq]
      _ = x * ((d * g) * r) := by rw [mul_assoc]
      _ = (x * g) * e * r := by rw [hd]; noncomm_ring
      _ = g * (y * e * r) := by rw [hx]; noncomm_ring
  rw [sub_mul, hc, ht, mul_sub]
end OddMath.OddNilHecke.CyclotomicNorm
