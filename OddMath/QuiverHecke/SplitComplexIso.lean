/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SplitComplexK0
import OddMath.QuiverHecke.SplitComplex

/-!
# The isomorphism between the even and odd terms of a split complex

The isomorphism step of Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang,
arXiv:1202.2769v2, Theorem 5.9). Let `X₀, …, X_M` be objects of `Karoubi C` with maps
`F a : X a ⟶ X (a + 1)`, `G a : X (a + 1) ⟶ X a` satisfying the identities of `IsSplitK`. Then
the matrix with entries `F a` and `G a` between neighbouring terms is an isomorphism
`⨁_{a even} X a ≅ ⨁_{a odd} X a`, with inverse the matrix of the same form
(`IsSplitK.evenOddIso`): its two composites are `F a ≫ G a + G (a - 1) ≫ F (a - 1) = 𝟙`
on the diagonal and `F ≫ F = 0`, `G ≫ G = 0` off it. Reindexing by `r = M - a` gives
`⨁_{r even} X (M - r) ≅ ⨁_{r odd} X (M - r)` (`IsSplitK.nonempty_revSum_iso`).
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.SplitComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

variable {C : Type*} [Category C] [Preadditive C]
variable {M : ℕ} {T : ℕ → Karoubi C}
  {F : ∀ a (_ : a < M), T a ⟶ T (a + 1)} {G : ∀ a (_ : a < M), T (a + 1) ⟶ T a}

theorem decide_even_succ (x : ℕ) : decide (Even (x + 1)) = !decide (Even x) := by
  simp only [Nat.even_add_one, decide_not]

/-- The reversal `r ↦ M - r` between the terms of parity `q` and those of parity `p`. -/
def revEquiv (M : ℕ) (q p : Bool)
    (h : ∀ r ≤ M, decide (Even (M - r)) = p ↔ decide (Even r) = q) : terms M q ≃ terms M p where
  toFun r := ⟨M - r.1, mem_terms.2 ⟨by omega, (h r.1 (mem_terms.1 r.2).1).2 (mem_terms.1 r.2).2⟩⟩
  invFun a := ⟨M - a.1, mem_terms.2 ⟨by omega, by
    have ha := mem_terms.1 a.2
    have := (h (M - a.1) (by omega))
    rw [Nat.sub_sub_self ha.1] at this
    exact this.1 ha.2⟩⟩
  left_inv r := Subtype.ext (by have := (mem_terms.1 r.2).1; simp only; omega)
  right_inv a := Subtype.ext (by have := (mem_terms.1 a.2).1; simp only; omega)

theorem decide_even_sub {M r : ℕ} (hr : r ≤ M) :
    decide (Even (M - r)) = (decide (Even M) == decide (Even r)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.even_sub hr, beq_iff_eq, Bool.eq_iff_iff,
    decide_eq_true_iff, decide_eq_true_iff]

namespace IsSplitK

variable (F G) in
/-- The entries of the maps between the even and odd parts: `F a` from `a` to `a + 1`, `G a`
from `a + 1` to `a`, and `0` otherwise. -/
def matEnt (x y : ℕ) : T x ⟶ T y :=
  if h : x + 1 = y ∧ x < M then F x h.2 ≫ eqToHom (congrArg T h.1)
  else if h' : y + 1 = x ∧ y < M then eqToHom (congrArg T h'.1.symm) ≫ G y h'.2
  else 0

theorem matEnt_up {x : ℕ} (hx : x < M) : matEnt F G x (x + 1) = F x hx := by
  rw [matEnt, dite_eq_left ⟨rfl, hx⟩, eqToHom_refl, Category.comp_id]

theorem matEnt_down {x : ℕ} (hx : x < M) : matEnt F G (x + 1) x = G x hx := by
  rw [matEnt, dite_eq_right (by omega), dite_eq_left ⟨rfl, hx⟩, eqToHom_refl, Category.id_comp]

theorem matEnt_eq_zero {x y : ℕ} (h₁ : x + 1 = y → M ≤ x) (h₂ : y + 1 = x → M ≤ y) :
    matEnt F G x y = 0 := by
  rw [matEnt, dite_eq_right (by omega), dite_eq_right (by omega)]

theorem sum_matEnt {x z : ℕ} (hx : x ≤ M) {p : Bool} (hp : decide (Even x) = p) :
    ∑ y ∈ terms M (!p), matEnt F G x y ≫ matEnt F G y z =
      matEnt F G x (x + 1) ≫ matEnt F G (x + 1) z + matEnt F G x (x - 1) ≫ matEnt F G (x - 1) z := by
  subst hp
  refine Finset.sum_eq_add _ _ (by omega) (fun c _ hc => ?_) (fun hn => ?_) (fun hn => ?_)
  · rw [matEnt_eq_zero (x := x) (y := c) (by omega) (by omega), zero_comp]
  · rw [matEnt_eq_zero (x := x) (y := x + 1) (fun _ => ?_) (by omega), zero_comp]
    by_contra hlt
    exact hn (mem_terms.2 ⟨by omega, decide_even_succ x⟩)
  · rcases x with _ | x
    · rw [matEnt_eq_zero (x := 0) (y := 0 - 1) (by omega) (by omega), zero_comp]
    · exact absurd (mem_terms.2 ⟨by omega, by rw [decide_even_succ, Nat.add_sub_cancel]; simp⟩) hn

variable (h : IsSplitK M (fun a _ => T a) F G)
include h

theorem matEnt_diag {x : ℕ} (hx : x ≤ M) :
    matEnt F G x (x + 1) ≫ matEnt F G (x + 1) x + matEnt F G x (x - 1) ≫ matEnt F G (x - 1) x = 𝟙 (T x) := by
  rcases x with _ | x
  · rw [matEnt_up h.pos, matEnt_down h.pos, matEnt_eq_zero (y := 0 - 1) (by omega) (by omega), zero_comp,
      add_zero]
    exact h.split_zero.symm
  · rw [Nat.add_sub_cancel, matEnt_down (x := x) (by omega), matEnt_up (x := x) (by omega)]
    rcases Nat.lt_or_ge (x + 1) M with hlt | hge
    · rw [matEnt_up hlt, matEnt_down hlt]
      exact (h.split_succ x hlt).symm
    · rw [matEnt_eq_zero (y := x + 1 + 1) (by omega) (by omega), zero_comp, zero_add]
      exact (h.split_top x (by omega) (by omega)).symm

theorem matEnt_off {x z : ℕ} (hz : z ≠ x) :
    matEnt F G x (x + 1) ≫ matEnt F G (x + 1) z + matEnt F G x (x - 1) ≫ matEnt F G (x - 1) z = 0 := by
  have h₁ : matEnt F G x (x + 1) ≫ matEnt F G (x + 1) z = 0 := by
    by_cases e : z = x + 2
    · subst e
      by_cases hlt : x + 1 < M
      · rw [matEnt_up (x := x) (by omega), matEnt_up hlt]
        exact h.ff x hlt
      · rw [matEnt_eq_zero (x := x + 1) (y := x + 2) (by omega) (by omega), comp_zero]
    · rw [matEnt_eq_zero (x := x + 1) (y := z) (by omega) (by omega), comp_zero]
  have h₂ : matEnt F G x (x - 1) ≫ matEnt F G (x - 1) z = 0 := by
    rcases x with _ | x
    · rw [matEnt_eq_zero (x := 0) (y := 0 - 1) (by omega) (by omega), zero_comp]
    · rw [Nat.add_sub_cancel]
      by_cases e : x = z + 1
      · subst e
        by_cases hlt : z + 1 < M
        · rw [matEnt_down (x := z + 1) hlt, matEnt_down (x := z) (by omega)]
          exact h.gg z hlt
        · rw [matEnt_eq_zero (x := z + 1 + 1) (y := z + 1) (by omega) (by omega), zero_comp]
      · rw [matEnt_eq_zero (x := x) (y := z) (by omega) (by omega), comp_zero]
  rw [h₁, h₂, add_zero]

variable [HasFiniteBiproducts (Karoubi C)]

variable (T) in
/-- The direct sum of the terms of parity `p`. -/
abbrev sumTerms (M : ℕ) (p : Bool) : Karoubi C := ⨁ fun x : terms M p => T x.1

variable (F G) in
/-- The map between the sums of the terms of the two parities. -/
def mat (p q : Bool) : sumTerms T M p ⟶ sumTerms T M q :=
  biproduct.matrix fun x y => matEnt F G x.1 y.1

theorem mat_comp_mat (p : Bool) : mat F G p (!p) ≫ mat F G (!p) p = 𝟙 _ := by
  apply biproduct.hom_ext'
  intro x
  apply biproduct.hom_ext
  intro z
  obtain ⟨hx, hpx⟩ := mem_terms.1 x.2
  simp only [mat, biproduct.ι_matrix_assoc, biproduct.lift_matrix, biproduct.lift_π]
  rw [Finset.sum_coe_sort (terms M (!p)) (fun y => matEnt F G x.1 y ≫ matEnt F G y z.1)]
  rw [sum_matEnt hx hpx, Category.comp_id]
  by_cases e : x = z
  · subst e
    rw [biproduct.ι_π_self, h.matEnt_diag hx]
  · rw [biproduct.ι_π_ne _ e, h.matEnt_off (fun e' => e (Subtype.ext e'.symm))]

/-- **A split complex identifies the sums of its even and odd terms**:
`⨁_{a even} X a ≅ ⨁_{a odd} X a`. -/
def evenOddIso (p : Bool) : sumTerms T M p ≅ sumTerms T M (!p) where
  hom := mat F G p (!p)
  inv := mat F G (!p) p
  hom_inv_id := h.mat_comp_mat p
  inv_hom_id := by cases p <;> exact h.mat_comp_mat _

/-- The terms indexed by `r = M - a`, with `r` of parity `q`. -/
abbrev revSum (T : ℕ → Karoubi C) (M : ℕ) (q : Bool) : Karoubi C :=
  ⨁ fun r : terms M q => T (M - r.1)

/-- The sum over even `r = M - a` is isomorphic to the sum over odd `r`. -/
theorem nonempty_revSum_iso : Nonempty (revSum T M true ≅ revSum T M false) := by
  have W : ∀ q, revSum T M q ≅ sumTerms T M (decide (Even M) == q) := fun q =>
    biproduct.whiskerEquiv (f := fun r : terms M q => T (M - r.1))
      (g := fun a : terms M (decide (Even M) == q) => T a.1)
      (revEquiv M q (decide (Even M) == q) fun r hr => by
        rw [decide_even_sub hr]
        cases decide (Even M) <;> cases q <;> cases decide (Even r) <;> decide)
      fun _ => Iso.refl _
  refine ⟨W true ≪≫ h.evenOddIso _ ≪≫ eqToIso ?_ ≪≫ (W false).symm⟩
  cases decide (Even M) <;> rfl

end IsSplitK

end OddMath.QuiverHecke.SplitComplex
