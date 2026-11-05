/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SpectatorDetection

/-! # Cyclotomic separation on words with spectators

For a fixed spectator word, cofinal cutoffs separate the whole extended Hom
space. For a varying spectator word the degree bound must be checked on the
whole word at the chosen cutoff. No fixed-weight cofinality assertion is made.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- Cofinal cutoffs, of either parity, separate the full Hom space with a
fixed spectator word. Cofinality and the spectator word are independent inputs;
a lowest-weight action does not in general allow them to be chosen independently. -/
theorem cofinal_elv_quotients_with_spectators_detect {A : Type*}
    (cutoff : A → I → ℕ) (hcofinal : ∀ N, ∃ a, ∀ i, N ≤ cutoff a i)
    (s t t' : List I)
    (f : coefficientObj D Sc (s ++ t) ⟶ coefficientObj D Sc (s ++ t'))
    (hf : ∀ a, (ELVRelationSpan D Sc (cutoff a) (s ++ t) (s ++ t')).mkQ f = 0) :
    f = 0 := by
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc (s ++ t) (s ++ t') f
  obtain ⟨a, ha⟩ := hcofinal (d + 2 * (s ++ t).length.choose 2 + 1)
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc
    (cutoff := cutoff a) (t := s ++ t) (t' := s ++ t')
    (d := d) ha (Nat.lt_succ_self _)
  have h := hinj (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa using hf a)
  exact congrArg Subtype.val h

/-- The quadratic crossing-loss estimate cannot certify detection when the
cutoff is at most twice the total strand number and there are at least three
strands. This is a limitation of that estimate, not vanishing in the quotient. -/
theorem spectator_crossing_bound_obstruction {n N d : ℕ}
    (hn : 3 ≤ n) (hN : N ≤ 2 * n) : ¬ (d + 2 * n.choose 2 < N) := by
  rw [mul_comm 2, Nat.choose_two_right,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  have hp : 2 ≤ n - 1 := by omega
  have hm := Nat.mul_le_mul_left n hp
  omega

end OddMath.QuiverHecke
