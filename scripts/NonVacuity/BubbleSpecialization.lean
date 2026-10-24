import OddMath.SKM.BubbleSpecialization
import OddMath.SKM.MixedCrossingLocalExamples

/-! Unit-top specialization on a concrete two-odd-colour datum. -/

noncomputable section
open scoped Classical
namespace NonVacuity.BubbleSpecialization

open OddMath.SKM
private abbrev D := MixedCrossingLocalExamples.oddDatum
private abbrev B := SYM D (ZMod 4)
private def i : {i : Bool // D.parity i = 1} := ⟨false, rfl⟩
private def j : {i : Bool // D.parity i = 1} := ⟨true, rfl⟩
private def cut (b : Bool) : ℕ := if b then 4 else 3
private def p : B := SYM.e D (ZMod 4) false 1 * SYM.delta D (ZMod 4) i * SYM.delta D (ZMod 4) j
private def q : B := SYM.e D (ZMod 4) true 2 ^ 2 + SYM.delta D (ZMod 4) j
private def coefficients : Fin 2 →₀ B := Finsupp.single 0 p + Finsupp.single 1 q

example : i.val ≠ j.val := by decide

/-- Distinct-colour exterior products are preserved, not replaced by zero. -/
example : SYM.unitCutoff D (ZMod 4) cut p = p := by
  simp [p, cut]

example : SYM.unitCutoff D (ZMod 4) cut q = q := by
  simp [q, cut]

example : SYM.unitCutoff D (ZMod 4) cut (SYM.e D (ZMod 4) false 3) = 1 :=
  SYM.unitCutoff_top D (ZMod 4) cut false

example : SYM.unitCutoff D (ZMod 4) cut (SYM.delta D (ZMod 4) i) =
    SYM.delta D (ZMod 4) i := SYM.unitCutoff_delta D (ZMod 4) cut i

example : ∃ N : ℕ, ∀ c : Bool → ℕ, (∀ b, N ≤ c b) →
    SYM.unitCutoff D (ZMod 4) c p = p :=
  SYM.exists_unitCutoff_fixed D (ZMod 4) p

example : ∃ N : ℕ, ∀ c : Bool → ℕ, (∀ b, N ≤ c b) →
    ∀ z ∈ ({p, q} : Finset B), SYM.unitCutoff D (ZMod 4) c z = z :=
  SYM.exists_unitCutoff_fixed_finset D (ZMod 4) {p, q}

example : ∃ N : ℕ, ∀ c : Bool → ℕ, (∀ b, N ≤ c b) →
    ∀ a, SYM.unitCutoff D (ZMod 4) c (coefficients a) = coefficients a :=
  SYM.exists_unitCutoff_fixed_coefficients D (ZMod 4) coefficients

#print axioms SYM.unitCutoff
#print axioms SYM.exists_unitCutoff_fixed_coefficients

end NonVacuity.BubbleSpecialization
