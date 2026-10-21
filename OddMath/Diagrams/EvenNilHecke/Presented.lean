import OddMath.Frontier.NilHeckeAction

/-!
# The integral even nilHecke presentation

The even same-colour algebra needed for BE2, arXiv:1701.04133v2, §11
before Lemma 11.1. The parameter `n` denotes `n + 2` strands, as in the
existing odd presentation. Positions increase from left to right, and
products act rightmost first. In particular `T X_left - X_right T = 1`
and `X_left T - T X_right = 1`.

This is a presentation by the nilHecke relations, not an endomorphism algebra
defined by an assumed splitting. The universal map has the same unital ring
homomorphism interface as the odd presentation.
-/

namespace OddMath.EvenNilHecke

abbrev Gen (n : ℕ) := Sum (Fin (n + 2)) (Fin (n + 1))
abbrev Free (n : ℕ) := FreeAlgebra ℤ (Gen n)

def dotFree (n : ℕ) (j : Fin (n + 2)) : Free n := FreeAlgebra.ι ℤ (Sum.inl j)
def crossingFree (n : ℕ) (i : Fin (n + 1)) : Free n := FreeAlgebra.ι ℤ (Sum.inr i)

/-- The seven classical nilHecke relation families. -/
inductive Relator (n : ℕ) : Free n → Prop
  | square (i : Fin (n + 1)) : Relator n (crossingFree n i * crossingFree n i)
  | braid (i j : Fin (n + 1)) (h : j.val = i.val + 1) :
      Relator n (crossingFree n i * crossingFree n j * crossingFree n i -
        crossingFree n j * crossingFree n i * crossingFree n j)
  | dots (i j : Fin (n + 2)) :
      Relator n (dotFree n i * dotFree n j - dotFree n j * dotFree n i)
  | distant (i j : Fin (n + 1)) (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
      Relator n (crossingFree n i * crossingFree n j - crossingFree n j * crossingFree n i)
  | mixedRight (i : Fin (n + 1)) :
      Relator n (dotFree n i.castSucc * crossingFree n i -
        crossingFree n i * dotFree n i.succ - 1)
  | mixedLeft (i : Fin (n + 1)) :
      Relator n (crossingFree n i * dotFree n i.castSucc -
        dotFree n i.succ * crossingFree n i - 1)
  | spectator (i : Fin (n + 1)) (j : Fin (n + 2))
      (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) :
      Relator n (crossingFree n i * dotFree n j - dotFree n j * crossingFree n i)

def relTwoSided (n : ℕ) : TwoSidedIdeal (Free n) := TwoSidedIdeal.span {w | Relator n w}
def relIdeal (n : ℕ) : Ideal (Free n) := (relTwoSided n).asIdeal
instance (n : ℕ) : (relIdeal n).IsTwoSided :=
  inferInstanceAs ((relTwoSided n).asIdeal.IsTwoSided)

def Presented (n : ℕ) : Type := Free n ⧸ relIdeal n
instance (n : ℕ) : Ring (Presented n) := Ideal.Quotient.ring (relIdeal n)

def dot (n : ℕ) (j : Fin (n + 2)) : Presented n :=
  Ideal.Quotient.mk (relIdeal n) (dotFree n j)
def crossing (n : ℕ) (i : Fin (n + 1)) : Presented n :=
  Ideal.Quotient.mk (relIdeal n) (crossingFree n i)

private theorem relator_zero {n : ℕ} {r : Free n} (h : Relator n r) :
    Ideal.Quotient.mk (relIdeal n) r = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ (relTwoSided n).asIdeal
  rw [TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span h

variable {n : ℕ}

theorem crossing_square (i : Fin (n + 1)) : crossing n i * crossing n i = 0 := by
  simpa only [map_mul, crossing] using relator_zero (Relator.square i)

theorem crossing_braid (i j : Fin (n + 1)) (h : j.val = i.val + 1) :
    crossing n i * crossing n j * crossing n i =
      crossing n j * crossing n i * crossing n j := by
  simpa only [map_sub, map_mul, crossing, sub_eq_zero] using relator_zero (Relator.braid i j h)

theorem dots_commute (i j : Fin (n + 2)) : dot n i * dot n j = dot n j * dot n i := by
  simpa only [map_sub, map_mul, dot, sub_eq_zero] using relator_zero (Relator.dots i j)

theorem crossing_distant (i j : Fin (n + 1))
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    crossing n i * crossing n j = crossing n j * crossing n i := by
  simpa only [map_sub, map_mul, crossing, sub_eq_zero] using
    relator_zero (Relator.distant i j h)

theorem crossing_dot_left (i : Fin (n + 1)) :
    crossing n i * dot n i.castSucc = dot n i.succ * crossing n i + 1 := by
  have h := relator_zero (Relator.mixedLeft i)
  simp only [map_sub, map_mul, map_one, sub_eq_zero] at h
  exact sub_eq_iff_eq_add'.mp h

theorem crossing_dot_right (i : Fin (n + 1)) :
    crossing n i * dot n i.succ = dot n i.castSucc * crossing n i - 1 := by
  have h := relator_zero (Relator.mixedRight i)
  simp only [map_sub, map_mul, map_one, sub_eq_zero] at h
  exact eq_sub_iff_add_eq.mpr ((sub_eq_iff_eq_add'.mp h).symm)

theorem crossing_dot_other (i : Fin (n + 1)) (j : Fin (n + 2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) :
    crossing n i * dot n j = dot n j * crossing n i := by
  simpa only [map_sub, map_mul, dot, crossing, sub_eq_zero] using
    relator_zero (Relator.spectator i j hl hr)

/-- A nilHecke family in an arbitrary unital ring. No faithfulness or decomposition
is part of the data. -/
structure Family (n : ℕ) (A : Type*) [Ring A] where
  x : Fin (n + 2) → A
  t : Fin (n + 1) → A
  square : ∀ i, t i * t i = 0
  braid : ∀ i j, j.val = i.val + 1 → t i * t j * t i = t j * t i * t j
  dots : ∀ i j, x i * x j = x j * x i
  distant : ∀ i j, (i.val + 1 < j.val ∨ j.val + 1 < i.val) → t i * t j = t j * t i
  mixedRight : ∀ i, x i.castSucc * t i - t i * x i.succ = 1
  mixedLeft : ∀ i, t i * x i.castSucc - x i.succ * t i = 1
  spectator : ∀ i j, j ≠ i.castSucc → j ≠ i.succ → t i * x j = x j * t i

namespace Family
variable {A : Type*} [Ring A] (F : Family n A)

noncomputable def freeMap : Free n →ₐ[ℤ] A :=
  FreeAlgebra.lift ℤ (Sum.elim F.x F.t)

@[simp] theorem freeMap_dot (j : Fin (n + 2)) : F.freeMap (dotFree n j) = F.x j := by
  simp [freeMap, dotFree]
@[simp] theorem freeMap_crossing (i : Fin (n + 1)) :
    F.freeMap (crossingFree n i) = F.t i := by simp [freeMap, crossingFree]

theorem relator_killed {r : Free n} (hr : Relator n r) : F.freeMap r = 0 := by
  cases hr with
  | square i => simpa using F.square i
  | braid i j h => simpa using sub_eq_zero.mpr (F.braid i j h)
  | dots i j => simpa using sub_eq_zero.mpr (F.dots i j)
  | distant i j h => simpa using sub_eq_zero.mpr (F.distant i j h)
  | mixedRight i => simpa using sub_eq_zero.mpr (F.mixedRight i)
  | mixedLeft i => simpa using sub_eq_zero.mpr (F.mixedLeft i)
  | spectator i j hl hr => simpa using sub_eq_zero.mpr (F.spectator i j hl hr)

/-- The universal unital map, used for coefficients and same-colour corners. -/
noncomputable def lift : Presented n →+* A :=
  Ideal.Quotient.lift (relIdeal n) F.freeMap.toRingHom (by
    intro r hr
    rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hr
    induction hr using TwoSidedIdeal.span_induction with
    | mem r hr => exact F.relator_killed hr
    | zero => exact map_zero _
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | neg x _ hx => simp only [map_neg, hx, neg_zero]
    | left_absorb a x _ hx => simp only [map_mul, hx, mul_zero]
    | right_absorb b x _ hx => simp only [map_mul, hx, zero_mul])

@[simp] theorem lift_dot (j : Fin (n + 2)) : F.lift (dot n j) = F.x j := F.freeMap_dot j
@[simp] theorem lift_crossing (i : Fin (n + 1)) : F.lift (crossing n i) = F.t i :=
  F.freeMap_crossing i

end Family
end OddMath.EvenNilHecke
