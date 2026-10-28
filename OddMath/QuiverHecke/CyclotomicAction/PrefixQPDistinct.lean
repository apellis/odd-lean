/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LastToFirstSnoc
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerBalance
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading

/-!
# The distinct-colour step of the all-prefix QP induction

`docs/Nondegeneracy/DeformedGlobalQP.md`, §3, case `ν_n ≠ i` (the deformed form of
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5, (8.14)–(8.16)). Write
`Vₙ = moveHom i [] ν` and `Tₙ = lastToFirstHom i ν`. For a final letter `x ≠ i`,

    T_(n+1) V_(n+1) = Q_ix(x₁, x_(n+2)) ≫ ((Vₙ ≫ Tₙ) ⊗ 1_x)

as endomorphisms of `i :: (ν ++ [x])`, with the KLR polynomial `Q_ix` (`qPoly`) evaluated
at the dot on the moving strand and the dot on the new spectator. The local factor is
`τₙ gₙ = Q_ix(xₙ, x_(n+1))`; it is transported through `Vₙ ⊗ 1_x`.

The transport signs are trivial: by the scalar parity conditions of the datum, an odd
colour enters every monomial of `Q_ix` to an even power (`Sc.s_eq_zero`,
`Datum.even_d_of_odd`). Arbitrary colours, parities and words; `d_ix = 0` is included.

* `qPoly`: the polynomial `Q_ix(a, b)` in two commuting-free endomorphisms;
* `cross_cross_qPoly`: the double crossing on two strands of different colours is `qPoly`;
* `comp_qPoly`: `qPoly` is transported along a morphism moving both dots with signs that
  are trivial on the monomials that occur;
* `moveHom_lastToFirstHom_append_ne`: the displayed recursion.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The KLR polynomial `Q_ix(a, b)` of relation (1.7), in two endomorphisms. -/
def qPoly {A : (pres D Sc).Presented} (a b : End A) (i x : I) : End A :=
  if D.d i x = 0 then (Sc.t i x : k) • 1 else
    (∑ p ∈ Finset.Ioo 0 (D.dn i x), ∑ q ∈ Finset.Ioo 0 (D.dn x i),
        Sc.s i x p q • (a ^ p * b ^ q)) +
      ((Sc.t i x : k) • a ^ D.dn i x + (Sc.t x i : k) • b ^ D.dn x i)

/-- (1.7): the double crossing on strands of different colours is `Q_ix` in their dots. -/
theorem cross_cross_qPoly (l r : List I) {i x : I} (hix : i ≠ x)
    (h : SChain (l ++ [i, x] ++ r) (pl _ [.cross l.length, .cross l.length])
      (l ++ [i, x] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross l.length] h =
      qPoly D Sc (dotE D Sc (l ++ [i, x] ++ r) l.length)
        (dotE D Sc (l ++ [i, x] ++ r) (l.length + 1)) i x := by
  unfold qPoly
  split_ifs with hd
  · rw [cross_cross_ne_zero D Sc l r hix hd h]
    rfl
  · exact cross_cross_ne D Sc l r hix hd h

/-- Two transported classes compose to the class of the concatenated word. -/
@[reassoc]
theorem eqToHom_cl_eqToHom_cl {t₀ t t₁ t₂ t₃ : List I} {gs gs' : List PG} (e : t₀ = t)
    (e' : t₁ = t₂) (h₁ : SChain t (pl t gs) t₁) (h₂ : SChain t₂ (pl t₂ gs') t₃) :
    eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e) ≫ cl D Sc t t₁ gs h₁ ≫
        eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e') ≫ cl D Sc t₂ t₃ gs' h₂ =
      cl D Sc t₀ t₃ (gs ++ gs') (by subst e e'; exact sChain_append_of h₁ h₂) := by
  subst e e'
  simp only [eqToHom_refl, Category.id_comp]
  exact cl_comp D Sc gs gs' h₁ h₂

/-- The double crossing on a word given up to equality. -/
theorem cl_cross_cross_qPoly {w w' : List I} (l r : List I) {i x : I} (hix : i ≠ x)
    (hw : w = l ++ [i, x] ++ r) (hw' : w' = w) {gs : List PG}
    (hgs : gs = [.cross l.length, .cross l.length]) (h : SChain w (pl w gs) w') :
    cl D Sc w w' gs h =
      qPoly D Sc (dotE D Sc w l.length) (dotE D Sc w (l.length + 1)) i x ≫
        eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) hw'.symm) := by
  subst hw' hw hgs
  rw [eqToHom_refl, Category.comp_id]
  exact cross_cross_qPoly D Sc l r hix h

section Transport

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

theorem comp_pow_of_signed {A B : C} (g : A ⟶ B) (a' : End A) (a : End B) (e : k)
    (h : g ≫ a = e • (a' ≫ g)) : ∀ n : ℕ, g ≫ a ^ n = e ^ n • ((a' ^ n : End A) ≫ g)
  | 0 => by simp [End.one_def]
  | n + 1 => by
    rw [pow_succ, End.mul_def, ← Category.assoc, h, Linear.smul_comp, Category.assoc,
      comp_pow_of_signed g a' a e h n, Linear.comp_smul, smul_smul, ← Category.assoc,
      pow_succ, pow_succ, End.mul_def, mul_comm]

theorem comp_monomial_of_signed {A B : C} (g : A ⟶ B) (a' b' : End A) (a b : End B)
    (ea eb : k) (ha : g ≫ a = ea • (a' ≫ g)) (hb : g ≫ b = eb • (b' ≫ g)) (p q : ℕ) :
    g ≫ (a ^ p * b ^ q) = (ea ^ p * eb ^ q) • ((a' ^ p * b' ^ q : End A) ≫ g) := by
  rw [End.mul_def, ← Category.assoc, comp_pow_of_signed g b' b eb hb, Linear.smul_comp,
    Category.assoc, comp_pow_of_signed g a' a ea ha, Linear.comp_smul, smul_smul,
    End.mul_def, Category.assoc, mul_comm]

end Transport

theorem zsign_pow (p : ZMod 2) : ∀ n : ℕ, SKM.zsign k p ^ n = SKM.zsign k ((n : ZMod 2) * p)
  | 0 => by simp [SKM.zsign]
  | n + 1 => by
    rw [pow_succ, zsign_pow p n, ← zsign_add_eq]
    congr 1
    push_cast
    ring

theorem zsign_pow_eq_one {p : ZMod 2} {n : ℕ} (h : (n : ZMod 2) * p = 0) :
    SKM.zsign k p ^ n = 1 := by
  rw [zsign_pow, h]
  simp [SKM.zsign]

theorem zmod_two_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

theorem dn_mul_parity (i x : I) : (D.dn i x : ZMod 2) * D.parity i = 0 := by
  by_cases hi : D.parity i = 1
  · by_cases hix : i = x
    · subst hix
      simp [SKM.Datum.dn, D.d_self]
    · obtain ⟨m, hm⟩ := D.even_d_of_odd hi x
      have hc : (D.dn i x : ℤ) = m + m := by rw [D.dn_cast hix, hm]
      have : D.dn i x = m.toNat + m.toNat := by omega
      rw [this, hi]
      push_cast
      ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]
  · rw [zmod_two_eq_zero_of_ne_one hi, mul_zero]

section EndAdditive

variable {C : Type*} [Category C] [Preadditive C]

theorem comp_end_add {A B : C} (g : A ⟶ B) (u v : End B) :
    g ≫ (u + v) = g ≫ u + g ≫ v :=
  Preadditive.comp_add _ _ _ _ _ _

theorem end_add_comp {A B : C} (g : A ⟶ B) (u v : End A) :
    (u + v) ≫ g = u ≫ g + v ≫ g :=
  Preadditive.add_comp _ _ _ _ _ _

theorem comp_end_sum {A B : C} {ι : Type*} (s : Finset ι) (g : A ⟶ B) (u : ι → End B) :
    g ≫ (∑ j ∈ s, u j) = ∑ j ∈ s, g ≫ u j :=
  Preadditive.comp_sum _ _ _

theorem end_sum_comp {A B : C} {ι : Type*} (s : Finset ι) (g : A ⟶ B) (u : ι → End A) :
    (∑ j ∈ s, u j) ≫ g = ∑ j ∈ s, u j ≫ g :=
  Preadditive.sum_comp _ _ _

theorem comp_smul_end [Linear k C] {A B : C} (g : A ⟶ B) (c : k) (u : End B) :
    g ≫ (c • u) = c • (g ≫ u) :=
  Linear.comp_smul _ _ _ _ _ _

theorem smul_end_comp [Linear k C] {A B : C} (g : A ⟶ B) (c : k) (u : End A) :
    (c • u) ≫ g = c • (u ≫ g) :=
  Linear.smul_comp _ _ _ _ _ _

end EndAdditive

/-- `Q_ix` is transported along `g` when the two dots move with signs `ea`, `eb` that are
trivial on even powers of an odd colour. -/
theorem comp_qPoly {A B : (pres D Sc).Presented} (g : A ⟶ B) (a' b' : End A) (a b : End B)
    (i x : I) (ea eb : k) (ha : g ≫ a = ea • (a' ≫ g)) (hb : g ≫ b = eb • (b' ≫ g))
    (hea : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 → ea ^ n = 1)
    (heb : ∀ n : ℕ, (n : ZMod 2) * D.parity x = 0 → eb ^ n = 1) :
    g ≫ qPoly D Sc a b i x = qPoly D Sc a' b' i x ≫ g := by
  unfold qPoly
  split_ifs with hd
  · rw [End.one_def, End.one_def, Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp]
  · simp only [comp_end_add, end_add_comp, comp_smul_end, smul_end_comp]
    erw [comp_end_sum, end_sum_comp]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      erw [comp_end_sum, end_sum_comp]
      refine Finset.sum_congr rfl fun q _ => ?_
      erw [comp_smul_end, smul_end_comp]
      by_cases hs : Sc.s i x p q = 0
      · rw [hs, zero_smul, zero_smul]
      · rw [comp_monomial_of_signed g a' b' a b ea eb ha hb p q,
          hea p (zmod_two_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero i x p q h)),
          heb q (zmod_two_eq_zero_of_ne_one fun h => hs (by
            rw [Sc.s_symm]; exact Sc.s_eq_zero x i q p h)), one_mul, one_smul]
    · rw [comp_pow_of_signed g a' a ea ha, comp_pow_of_signed g b' b eb hb,
        hea _ (dn_mul_parity D i x), heb _ (dn_mul_parity D x i), one_smul, one_smul]

/-- A dot on an appended strand is the left whiskering of the one-strand dot. -/
theorem whiskerLeft_dotE (w : List I) (x : I) {a : ℕ} (ha : a = w.length) :
    (pres D Sc).obj (ob D w) ◁ dotE D Sc [x] 0 = dotE D Sc (w ++ [x]) a := by
  subst ha
  rw [dotE_eq, cl_whiskerLeft, dotE_eq]
  exact cl_congr_gs D Sc (by simp) _ _

/-- The moving-strand dot through `Vₙ ⊗ 1_x`. -/
theorem moveHom_whiskerRight_comp_dot (i x : I) (ν : List I) :
    (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x])) ≫
        dotE D Sc (ν ++ [i] ++ [x]) ν.length =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (dotE D Sc (i :: (ν ++ [x])) 0 ≫ (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x]))) := by
  have h := congrArg (· ▷ (pres D Sc).obj (ob D [x])) (dot_comp_moveHom D Sc i [] ν)
  simp only [MonoidalSupercategory.comp_whiskerRight (R := k),
    MonoidalSupercategory.smul_whiskerRight (R := k)] at h
  rw [dotE_whiskerRight D Sc _ _ _ (by simp),
    dotE_whiskerRight D Sc _ _ _ (by simp)] at h
  have h' := congrArg (SKM.zsign k (D.parity i * wordSumParity D ν) • ·) h
  simp only [smul_smul, zsign_mul_self, one_smul, List.length_nil, zero_add] at h'
  exact h'.symm

/-- The dot on the new spectator through `Vₙ ⊗ 1_x`, by super interchange. -/
theorem moveHom_whiskerRight_comp_last_dot (i x : I) (ν : List I) :
    (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x])) ≫
        dotE D Sc (ν ++ [i] ++ [x]) (ν.length + 1) =
      SKM.zsign k (D.parity i * wordSumParity D ν * D.parity x) •
        (dotE D Sc (i :: (ν ++ [x])) (ν.length + 1) ≫
          (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x]))) := by
  have e1 : dotE D Sc (ν ++ [i] ++ [x]) (ν.length + 1) =
      (pres D Sc).obj (ob D (ν ++ [i])) ◁ dotE D Sc [x] 0 :=
    (whiskerLeft_dotE D Sc (ν ++ [i]) x (by simp)).symm
  have e2 : dotE D Sc (i :: (ν ++ [x])) (ν.length + 1) =
      (pres D Sc).obj (ob D (i :: ν)) ◁ dotE D Sc [x] 0 :=
    (whiskerLeft_dotE D Sc (i :: ν) x (by simp)).symm
  rw [e1, e2]
  refine (MonoidalSupercategory.super_interchange (R := k) (moveHom_parity D Sc i [] ν)
      (positionedDot_parity D Sc [] [] x)).trans ?_
  unfold Supercategory.koszulSign SKM.zsign
  by_cases hp : D.parity i * wordSumParity D ν = 1 <;> by_cases hx : D.parity x = 1 <;>
    simp [hp, hx]

/-- The distinct-colour step: `T_(n+1) V_(n+1) = Q_ix(x₁, x_(n+2)) ((Tₙ Vₙ) ⊗ 1_x)`. -/
theorem moveHom_lastToFirstHom_append_ne {i x : I} (hix : i ≠ x) (ν : List I) :
    moveHom D Sc i [] (ν ++ [x]) ≫ lastToFirstHom D Sc i (ν ++ [x]) =
      qPoly D Sc (dotE D Sc (i :: (ν ++ [x])) 0) (dotE D Sc (i :: (ν ++ [x])) (ν.length + 1))
          i x ≫
        ((moveHom D Sc i [] ν ≫ lastToFirstHom D Sc i ν) ▷ (pres D Sc).obj (ob D [x])) := by
  rw [moveHom_append_singleton, lastToFirstHom_append_singleton,
    intertwinerHom_of_ne D Sc _ _ hix]
  simp only [Category.assoc]
  erw [eqToHom_cl_eqToHom_cl_assoc]
  rw [
    cl_cross_cross_qPoly D Sc ν [] hix (by simp [ob]) (by simp [ob]) (by simp)]
  erw [Category.id_comp]
  rw [MonoidalSupercategory.comp_whiskerRight (R := k), ← Category.assoc,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Category.assoc]
  erw [Category.comp_id]
  exact comp_qPoly D Sc _ _ _ _ _ i x _ _
    (moveHom_whiskerRight_comp_dot D Sc i x ν)
    (moveHom_whiskerRight_comp_last_dot D Sc i x ν)
    (fun n hn => by
      rw [zsign_pow_eq_one]
      rw [← mul_assoc, hn, zero_mul])
    (fun n hn => by
      rw [zsign_pow_eq_one]
      linear_combination (D.parity i * wordSumParity D ν) * hn)
  all_goals simp [ob]

end OddMath.QuiverHecke
