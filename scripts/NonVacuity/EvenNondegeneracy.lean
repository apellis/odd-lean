import OddMath

/-! Non-vacuity checks in `NonVacuity.EvenNondegeneracy`: the Nondegeneracy Conjecture of
Brundan–Ellis for the purely even datum of `sl₂` (one even colour) over `ℚ`, with every
hypothesis of `nondegeneracyConjecture_of_isEven` proved. Conventions are in
`scripts/NonVacuity.lean`. -/

noncomputable section

namespace NonVacuity.EvenNondegeneracy

open OddMath.SKM OddMath.SKM.EvenBridge TwoStrandShiftConsumer

/-- Khovanov–Lauda scalars for the one-colour datum over `ℚ`. -/
def scalarsQ : Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by
    rintro ⟨i, hi⟩
    exact (zero_ne_one hi).elim

def csQ : CScalars scalarsQ where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [scalarsQ]

/-- The Cartan datum of `sl₂`: `i · i = 2`. -/
def cartanSl2 : Categorification.QuantumGroup.CartanDatum Unit where
  dot := fun _ _ => 2
  symm := fun _ _ => rfl
  dot_self_pos := fun _ => by norm_num
  dot_self_even := fun _ => even_two
  dot_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
  dvd_two_mul := fun _ _ => dvd_mul_left _ _

theorem compatible : Compatible datum cartanSl2 := fun _ _ => by
  simp [Categorification.QuantumGroup.UDot.A, cartanSl2, datum, Datum.h, Datum.α]

theorem isEven : IsEven datum := fun _ => rfl

theorem isKLScalars : IsKLScalars datum ℚ scalarsQ := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

example : NondegeneracyConjecture csQ :=
  nondegeneracyConjecture_of_isEven cartanSl2 compatible isEven isKLScalars csQ

end NonVacuity.EvenNondegeneracy
