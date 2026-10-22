/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Idempotents.Biproducts
import StringDiagrams.Super.K0

/-!
# Split complexes in an idempotent completion and their classes

The `K₀` step of Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang,
arXiv:1202.2769v2, Theorem 5.9). In the idempotent completion `Karoubi C` of a preadditive
category whose completion has binary biproducts, let `X₀, …, X_M` be objects with maps
`F a : X a ⟶ X (a + 1)` and `G a : X (a + 1) ⟶ X a` such that consecutive `F`'s and consecutive
`G`'s compose to zero, `F M = 0`, and

`𝟙 (X 0) = F 0 ≫ G 0`, `𝟙 (X (a + 1)) = F (a + 1) ≫ G (a + 1) + G a ≫ F a` (`a + 1 ≤ M`).

Then `∑_{a ≤ M} (-1)^a [X a] = 0` in split `K₀` (`alternating_sum_eq_zero`): each `X (a + 1)`
splits as the images of `F (a + 1) ≫ G (a + 1)` and `G a ≫ F a`, and the latter is isomorphic to
the image of `F a ≫ G a` (`img_iso`), so the sum telescopes.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.SplitComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts (Karoubi C)]

/-- The summand of `P` cut out by an idempotent endomorphism `p`. -/
def img {P : Karoubi C} (p : P ⟶ P) (hp : p ≫ p = p) : Karoubi C where
  X := P.X
  p := p.f
  idem := by rw [← Karoubi.comp_f, hp]

/-- `P` is the sum of the images of two complementary orthogonal idempotents. -/
theorem mk_eq_add {P : Karoubi C} (p q : P ⟶ P) (hp : p ≫ p = p) (hq : q ≫ q = q)
    (hpq : p ≫ q = 0) (hqp : q ≫ p = 0) (hsum : p + q = 𝟙 P) :
    K₀.mk P = K₀.mk (img p hp) + K₀.mk (img q hq) := by
  have hp' : p.f ≫ p.f = p.f := by rw [← Karoubi.comp_f, hp]
  have hq' : q.f ≫ q.f = q.f := by rw [← Karoubi.comp_f, hq]
  have hpq' : p.f ≫ q.f = 0 := by rw [← Karoubi.comp_f, hpq]; rfl
  have hqp' : q.f ≫ p.f = 0 := by rw [← Karoubi.comp_f, hqp]; rfl
  let ip : img p hp ⟶ P := ⟨p.f, by change p.f ≫ p.f ≫ P.p = p.f; rw [Karoubi.comp_p, hp']⟩
  let iq : img q hq ⟶ P := ⟨q.f, by change q.f ≫ q.f ≫ P.p = q.f; rw [Karoubi.comp_p, hq']⟩
  let rp : P ⟶ img p hp := ⟨p.f, by change P.p ≫ p.f ≫ p.f = p.f; rw [hp', Karoubi.p_comp]⟩
  let rq : P ⟶ img q hq := ⟨q.f, by change P.p ≫ q.f ≫ q.f = q.f; rw [hq', Karoubi.p_comp]⟩
  have e : P ≅ img p hp ⊞ img q hq :=
    { hom := biprod.lift rp rq
      inv := biprod.desc ip iq
      hom_inv_id := by
        rw [biprod.lift_desc, ← hsum]
        apply Karoubi.hom_ext
        change p.f ≫ p.f + q.f ≫ q.f = (p + q).f
        rw [hp', hq']
        rfl
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc,
            biprod.lift_fst, biprod.lift_snd, Category.comp_id, biprod.inl_fst, biprod.inl_snd,
            biprod.inr_fst, biprod.inr_snd] <;>
          apply Karoubi.hom_ext
        · exact hp'
        · exact hpq'
        · exact hqp'
        · exact hq' }
  rw [K₀.mk_eq_mk_of_iso e, K₀.mk_biprod]

/-- Maps `u`, `v` with `u v u = u` and `v u v = v` identify the images of `u ≫ v` and
`v ≫ u`. -/
def imgIso {P Q : Karoubi C} (u : P ⟶ Q) (v : Q ⟶ P) (huvu : u ≫ v ≫ u = u)
    (hvuv : v ≫ u ≫ v = v) (h₁ : (u ≫ v) ≫ (u ≫ v) = u ≫ v)
    (h₂ : (v ≫ u) ≫ (v ≫ u) = v ≫ u) : img (u ≫ v) h₁ ≅ img (v ≫ u) h₂ where
  hom := ⟨u.f, by
    change (u.f ≫ v.f) ≫ u.f ≫ (v.f ≫ u.f) = u.f
    rw [← Karoubi.comp_f, ← Karoubi.comp_f, ← Karoubi.comp_f, ← Karoubi.comp_f]
    simp only [Category.assoc, huvu]⟩
  inv := ⟨v.f, by
    change (v.f ≫ u.f) ≫ v.f ≫ (u.f ≫ v.f) = v.f
    rw [← Karoubi.comp_f, ← Karoubi.comp_f, ← Karoubi.comp_f, ← Karoubi.comp_f]
    simp only [Category.assoc, hvuv]⟩
  hom_inv_id := Karoubi.hom_ext _ _ rfl
  inv_hom_id := Karoubi.hom_ext _ _ rfl

theorem mk_img_zero {P : Karoubi C} (h : (0 : P ⟶ P) ≫ 0 = 0) : K₀.mk (img 0 h) = 0 := by
  have hz : IsZero (img (0 : P ⟶ P) h) := by
    rw [IsZero.iff_id_eq_zero]
    exact Karoubi.hom_ext _ _ rfl
  have e := K₀.mk_biprod (img (0 : P ⟶ P) h) (img (0 : P ⟶ P) h)
  rw [K₀.mk_eq_mk_of_iso (((biprod_isZero_iff _ _).2 ⟨hz, hz⟩).iso hz)] at e
  simpa using e

theorem mk_img_eq {P : Karoubi C} {p q : P ⟶ P} (hp : p ≫ p = p) (hq : q ≫ q = q) (e : p = q) :
    K₀.mk (img p hp) = K₀.mk (img q hq) := by
  subst e; rfl

variable {X : ℕ → Karoubi C} {F : ∀ a, X a ⟶ X (a + 1)} {G : ∀ a, X (a + 1) ⟶ X a} {M : ℕ}

/-- The identities of a split complex `X₀ ⇄ X₁ ⇄ ⋯ ⇄ X_M` (with the scalars absorbed into
`F`). -/
structure IsSplitK (M : ℕ) (X : ℕ → Karoubi C) (F : ∀ a, X a ⟶ X (a + 1))
    (G : ∀ a, X (a + 1) ⟶ X a) : Prop where
  ff : ∀ a, F a ≫ F (a + 1) = 0
  gg : ∀ a, G (a + 1) ≫ G a = 0
  f_top : F M = 0
  split_zero : 𝟙 (X 0) = F 0 ≫ G 0
  split_succ : ∀ a, a + 1 ≤ M → 𝟙 (X (a + 1)) = F (a + 1) ≫ G (a + 1) + G a ≫ F a

namespace IsSplitK

variable (h : IsSplitK M X F G)
include h

omit [HasBinaryBiproducts (Karoubi C)] in
theorem fgf {a : ℕ} (ha : a + 1 ≤ M) : F a ≫ G a ≫ F a = F a := by
  have e := congrArg (F a ≫ ·) (h.split_succ a ha)
  simp only [Category.comp_id, Preadditive.comp_add, ← Category.assoc, h.ff, zero_comp,
    zero_add] at e
  rw [Category.assoc] at e
  exact e.symm

omit [HasBinaryBiproducts (Karoubi C)] in
theorem gfg {a : ℕ} (ha : a + 1 ≤ M) : G a ≫ F a ≫ G a = G a := by
  rcases a with _ | b
  · have e := congrArg (G 0 ≫ ·) h.split_zero
    simp only [Category.comp_id] at e
    exact e.symm
  · have e := congrArg (G (b + 1) ≫ ·) (h.split_succ b (by omega))
    simp only [Category.comp_id, Preadditive.comp_add, ← Category.assoc, h.gg, zero_comp,
      add_zero] at e
    rw [Category.assoc] at e
    exact e.symm

omit [HasBinaryBiproducts (Karoubi C)] in
theorem fg_idem {a : ℕ} (ha : a ≤ M) : (F a ≫ G a) ≫ (F a ≫ G a) = F a ≫ G a := by
  by_cases ha' : a + 1 ≤ M
  · simp only [Category.assoc]; rw [h.gfg ha']
  · obtain rfl : a = M := by omega
    rw [h.f_top]; simp

omit [HasBinaryBiproducts (Karoubi C)] in
theorem gf_idem {a : ℕ} (ha : a + 1 ≤ M) : (G a ≫ F a) ≫ (G a ≫ F a) = G a ≫ F a := by
  simp only [Category.assoc]; rw [h.fgf ha]

/-- The class of the image of `F a ≫ G a`. -/
def c {a : ℕ} (ha : a ≤ M) : K₀ (Karoubi C) := K₀.mk (img (F a ≫ G a) (h.fg_idem ha))

theorem mk_zero_eq : K₀.mk (X 0) = h.c (Nat.zero_le M) := by
  rw [mk_eq_add (F 0 ≫ G 0) 0 (h.fg_idem (Nat.zero_le M)) (by simp) (by simp) (by simp)
    (by rw [add_zero, h.split_zero]), mk_img_zero, add_zero]
  rfl

theorem mk_succ_eq {a : ℕ} (ha : a + 1 ≤ M) :
    K₀.mk (X (a + 1)) = h.c ha + h.c (Nat.le_of_succ_le ha) := by
  rw [mk_eq_add (F (a + 1) ≫ G (a + 1)) (G a ≫ F a) (h.fg_idem ha) (h.gf_idem ha) ?_ ?_
    (h.split_succ a ha).symm]
  · congr 1
    exact (K₀.mk_eq_mk_of_iso (imgIso (F a) (G a) (h.fgf ha) (h.gfg ha) _ _)).symm
  · simp only [Category.assoc]
    rw [← Category.assoc (G (a + 1)), h.gg, zero_comp, comp_zero]
  · simp only [Category.assoc]
    rw [← Category.assoc (F a), h.ff, zero_comp, comp_zero]

theorem sum_eq {n : ℕ} (hn : n ≤ M) :
    ∑ a ∈ Finset.range (n + 1), ((-1 : ℤ) ^ a) • K₀.mk (X a) = ((-1 : ℤ) ^ n) • h.c hn := by
  induction n with
  | zero => simp [h.mk_zero_eq]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega), h.mk_succ_eq hn, smul_add, pow_succ]
    simp only [mul_neg, mul_one, neg_smul]
    abel

/-- **The alternating sum of a split complex vanishes**: `∑_{a ≤ M} (-1)^a [X a] = 0`. -/
theorem alternating_sum_eq_zero :
    ∑ a ∈ Finset.range (M + 1), ((-1 : ℤ) ^ a) • K₀.mk (X a) = 0 := by
  rw [h.sum_eq le_rfl, c]
  rw [mk_img_eq _ (show (0 : X M ⟶ X M) ≫ 0 = 0 by simp) (by rw [h.f_top, zero_comp])]
  rw [mk_img_zero, smul_zero]

end IsSplitK

end OddMath.QuiverHecke.SplitComplex
