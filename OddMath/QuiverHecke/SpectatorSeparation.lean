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

/-- A nonzero product of bubble and affine operators survives if the cutoff
exceeds its extended degree plus the crossing loss for *all* strands. -/
theorem spectator_quotientImage_ne_zero {μ : X} {t t' : List I}
    (P : SpectatorImage D Sc μ t t')
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t') {d N : ℕ}
    (hf : P.image f ≠ 0)
    (hdeg : P.image f ∈ ExtendedAtMost D Sc (P.spectators ++ t) (P.spectators ++ t') d)
    (hcutoff : ∀ i, N ≤ P.cutoff i)
    (hbound : d + 2 * (P.spectators ++ t).length.choose 2 < N) :
    P.quotientImage f ≠ 0 := by
  intro hz
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc
    (t := P.spectators ++ t) (t' := P.spectators ++ t') (d := d) hcutoff hbound
  apply hf
  exact congrArg Subtype.val (hinj (a₁ := ⟨P.image f, hdeg⟩) (a₂ := 0)
    (by simpa [SpectatorImage.quotientImage] using hz))

/-- Sufficient algebraic separation input for a family with moving spectators.
Both nonvanishing of the joint image and a compatible cutoff bound must be
proved. Neither is supplied by weight coverage alone. -/
theorem spectator_images_detect_of_bounds {μ : X} {t t' : List I} {A : Type*}
    (P : A → SpectatorImage D Sc μ t t')
    (h : ∀ f : coefficientObj D Sc t ⟶ coefficientObj D Sc t', f ≠ 0 →
      ∃ a d N, (P a).image f ≠ 0 ∧
        (P a).image f ∈ ExtendedAtMost D Sc ((P a).spectators ++ t) ((P a).spectators ++ t') d ∧
        (∀ i, N ≤ (P a).cutoff i) ∧ d + 2 * ((P a).spectators ++ t).length.choose 2 < N)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : ∀ a, (P a).quotientImage f = 0) : f = 0 := by
  by_contra hn
  obtain ⟨a, d, N, ha, hd, hN, hb⟩ := h f hn
  exact spectator_quotientImage_ne_zero D Sc (P a) f ha hd hN hb (hf a)

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
