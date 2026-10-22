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
`F a : X a ⟶ X (a + 1)` and `G a : X (a + 1) ⟶ X a` (`a < M`, `M ≥ 1`) such that consecutive
`F`'s and consecutive `G`'s compose to zero and

`𝟙 (X 0) = F 0 ≫ G 0`, `𝟙 (X (a + 1)) = F (a + 1) ≫ G (a + 1) + G a ≫ F a` (`a + 1 < M`),
`𝟙 (X M) = G (M - 1) ≫ F (M - 1)`.

Then `∑_{a ≤ M} (-1)^a [X a] = 0` in split `K₀` (`alternating_sum_eq_zero`): each `X (a + 1)`
splits as the images of `F (a + 1) ≫ G (a + 1)` and `G a ≫ F a`, and the latter is isomorphic to
the image of `F a ≫ G a` (`imgIso`), so the sum telescopes. The terms are indexed by `a ≤ M`,
so that they may live in a category whose objects make sense only for `a ≤ M` (a hom category
of `𝔘(𝔤)` with fixed end weights, for instance).
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

variable {M : ℕ} {X : (a : ℕ) → a ≤ M → Karoubi C}
  {F : ∀ a (h : a < M), X a h.le ⟶ X (a + 1) h} {G : ∀ a (h : a < M), X (a + 1) h ⟶ X a h.le}

/-- The identities of a split complex `X₀ ⇄ X₁ ⇄ ⋯ ⇄ X_M`, `M ≥ 1` (with the scalars absorbed
into `F`). The terms and maps are indexed by `a ≤ M` and `a < M`. -/
structure IsSplitK (M : ℕ) (X : (a : ℕ) → a ≤ M → Karoubi C)
    (F : ∀ a (h : a < M), X a h.le ⟶ X (a + 1) h)
    (G : ∀ a (h : a < M), X (a + 1) h ⟶ X a h.le) : Prop where
  pos : 0 < M
  ff : ∀ a (h : a + 1 < M), F a (Nat.lt_of_succ_lt h) ≫ F (a + 1) h = 0
  gg : ∀ a (h : a + 1 < M), G (a + 1) h ≫ G a (Nat.lt_of_succ_lt h) = 0
  split_zero : 𝟙 (X 0 (Nat.zero_le M)) = F 0 pos ≫ G 0 pos
  split_succ : ∀ a (h : a + 1 < M), 𝟙 (X (a + 1) h.le) =
    F (a + 1) h ≫ G (a + 1) h + G a (Nat.lt_of_succ_lt h) ≫ F a (Nat.lt_of_succ_lt h)
  split_top : ∀ a (h : a < M), a + 1 = M → 𝟙 (X (a + 1) h) = G a h ≫ F a h

namespace IsSplitK

variable (h : IsSplitK M X F G)
include h

omit [HasBinaryBiproducts (Karoubi C)] in
theorem fgf {a : ℕ} (ha : a < M) : F a ha ≫ G a ha ≫ F a ha = F a ha := by
  by_cases ht : a + 1 = M
  · have e := congrArg (F a ha ≫ ·) (h.split_top a ha ht)
    simp only [Category.comp_id] at e
    exact e.symm
  · have e := congrArg (F a ha ≫ ·) (h.split_succ a (by omega))
    simp only [Category.comp_id, Preadditive.comp_add, ← Category.assoc, h.ff a (by omega),
      zero_comp, zero_add] at e
    rw [Category.assoc] at e
    exact e.symm

omit [HasBinaryBiproducts (Karoubi C)] in
theorem gfg {a : ℕ} (ha : a < M) : G a ha ≫ F a ha ≫ G a ha = G a ha := by
  rcases a with _ | b
  · have e := congrArg (G 0 ha ≫ ·) h.split_zero
    simp only [Category.comp_id] at e
    exact e.symm
  · have e := congrArg (G (b + 1) ha ≫ ·) (h.split_succ b ha)
    simp only [Category.comp_id, Preadditive.comp_add, ← Category.assoc, h.gg b ha, zero_comp,
      add_zero] at e
    rw [Category.assoc] at e
    exact e.symm

omit [HasBinaryBiproducts (Karoubi C)] in
theorem fg_idem {a : ℕ} (ha : a < M) :
    (F a ha ≫ G a ha) ≫ (F a ha ≫ G a ha) = F a ha ≫ G a ha := by
  simp only [Category.assoc]; rw [h.gfg ha]

omit [HasBinaryBiproducts (Karoubi C)] in
theorem gf_idem {a : ℕ} (ha : a < M) :
    (G a ha ≫ F a ha) ≫ (G a ha ≫ F a ha) = G a ha ≫ F a ha := by
  simp only [Category.assoc]; rw [h.fgf ha]

/-- The class of the image of `F a ≫ G a`. -/
def c {a : ℕ} (ha : a < M) : K₀ (Karoubi C) := K₀.mk (img (F a ha ≫ G a ha) (h.fg_idem ha))

theorem c_eq_gf {a : ℕ} (ha : a < M) :
    h.c ha = K₀.mk (img (G a ha ≫ F a ha) (h.gf_idem ha)) :=
  K₀.mk_eq_mk_of_iso (imgIso (F a ha) (G a ha) (h.fgf ha) (h.gfg ha) _ _)

theorem mk_zero_eq : K₀.mk (X 0 (Nat.zero_le M)) = h.c h.pos := by
  rw [mk_eq_add (F 0 h.pos ≫ G 0 h.pos) 0 (h.fg_idem h.pos) (by simp) (by simp) (by simp)
    (by rw [add_zero, h.split_zero]), mk_img_zero, add_zero]
  rfl

theorem mk_succ_eq {a : ℕ} (ha : a + 1 < M) :
    K₀.mk (X (a + 1) ha.le) = h.c ha + h.c (Nat.lt_of_succ_lt ha) := by
  rw [mk_eq_add (F (a + 1) ha ≫ G (a + 1) ha)
    (G a (Nat.lt_of_succ_lt ha) ≫ F a (Nat.lt_of_succ_lt ha)) (h.fg_idem ha)
    (h.gf_idem (Nat.lt_of_succ_lt ha)) ?_ ?_ (h.split_succ a ha).symm]
  · rw [h.c_eq_gf (Nat.lt_of_succ_lt ha)]
    rfl
  · simp only [Category.assoc]
    rw [← Category.assoc (G (a + 1) ha), h.gg a ha, zero_comp, comp_zero]
  · simp only [Category.assoc]
    rw [← Category.assoc (F a _), h.ff a ha, zero_comp, comp_zero]

theorem mk_top_eq {a : ℕ} (ha : a < M) (ht : a + 1 = M) : K₀.mk (X (a + 1) ha) = h.c ha := by
  rw [h.c_eq_gf ha]
  rw [mk_eq_add (G a ha ≫ F a ha) 0 (h.gf_idem ha) (by simp) (by simp) (by simp)
    (by rw [add_zero, h.split_top a ha ht]), mk_img_zero, add_zero]

/-- The class of the term `a`, and `0` for `a > M`. -/
def cls (a : ℕ) : K₀ (Karoubi C) := if ha : a ≤ M then K₀.mk (X a ha) else 0

theorem sum_eq {n : ℕ} (hn : n < M) :
    ∑ a ∈ Finset.range (n + 1), ((-1 : ℤ) ^ a) • cls (X := X) a = ((-1 : ℤ) ^ n) • h.c hn := by
  induction n with
  | zero => simp [cls, h.mk_zero_eq]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega), cls, dite_eq_left hn.le, h.mk_succ_eq hn, smul_add,
      pow_succ]
    simp only [mul_neg, mul_one, neg_smul]
    abel

/-- **The alternating sum of a split complex vanishes**: `∑_{a ≤ M} (-1)^a [X a] = 0`. -/
theorem alternating_sum_eq_zero :
    ∑ a : Fin (M + 1), ((-1 : ℤ) ^ (a : ℕ)) • K₀.mk (X a (Nat.le_of_lt_succ a.2)) = 0 := by
  have hcls : ∀ a : Fin (M + 1), K₀.mk (X a (Nat.le_of_lt_succ a.2)) = cls (X := X) a :=
    fun a => by rw [cls, dite_eq_left (Nat.le_of_lt_succ a.2)]
  simp only [hcls]
  rw [Fin.sum_univ_eq_sum_range (fun a => ((-1 : ℤ) ^ a) • cls (X := X) a)]
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by have := h.pos; omega⟩
  rw [Finset.sum_range_succ, h.sum_eq (Nat.lt_succ_self n), cls, dite_eq_left le_rfl,
    h.mk_top_eq (Nat.lt_succ_self n) rfl, pow_succ]
  simp

end IsSplitK

end OddMath.QuiverHecke.SplitComplex
