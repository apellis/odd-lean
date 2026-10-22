/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.MixedRelations

/-!
# The words `i^a j i^{M-a}` of the categorical Serre relation

Input to Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang, arXiv:1202.2769v2,
Theorem 5.9). For colours `i`, `j` and `M ≥ 0`, `serreWord i j M a = i^a j i^{M-a}` (positions
counted from the left). On it the dots and crossings of the left block `[0, a)` and of the right
block `[a + 1, M + 1)` are signed nilHecke families (`leftFamily`, `rightFamily`), and
`serreIdem a = 1_{i^{(a)}} ⊗ 1_j ⊗ 1_{i^{(M-a)}}` is the product of their longest Demazure
products. The crossing `crossHom` of the strand `j` with a neighbouring `i` moves between
consecutive words.

Generators away from that crossing pass through it by the super interchange law; `Slides`
records this for elements of the endomorphism rings, with an explicit sign, and is closed under
products, so the block idempotents pass through it unchanged.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
open Categorification.KLR.KL2.NH (wp Wb chL chR)
open Categorification.NilHecke (w0Word)
universe u v w

/-! ## Intertwiners -/

section Slides

variable {C : Type*} [Category C] [Preadditive C] {A B : C}

/-- `f ≫ σ = u • (σ ≫ g)`: `f` passes through `σ` as `g`, with the sign `u`. -/
def Slides (σ : A ⟶ B) (u : ℤˣ) (f : End A) (g : End B) : Prop := f ≫ σ = (u : ℤ) • (σ ≫ g)

namespace Slides

variable {σ : A ⟶ B} {u u' : ℤˣ} {f f' : End A} {g g' : End B}

theorem one : Slides σ 1 (1 : End A) (1 : End B) := by
  simp [Slides, End.one_def]

theorem mul (h : Slides σ u f g) (h' : Slides σ u' f' g') : Slides σ (u * u') (f * f') (g * g') := by
  simp only [Slides, End.mul_def, Category.assoc] at *
  rw [h, Preadditive.comp_zsmul, ← Category.assoc, h', Preadditive.zsmul_comp, Category.assoc,
    smul_smul, Units.val_mul]

theorem zsmul (h : Slides σ u f g) (c : ℤ) : Slides σ u (c • f) (c • g) := by
  simp only [Slides] at *
  rw [Preadditive.zsmul_comp, h, Preadditive.comp_zsmul, smul_comm]

theorem neg (h : Slides σ u f g) : Slides σ u (-f) (-g) := by
  simpa using h.zsmul (-1)

theorem add (h : Slides σ u f g) (h' : Slides σ u f' g') : Slides σ u (f + f') (g + g') := by
  simp only [Slides] at *
  rw [Preadditive.add_comp, h, h', Preadditive.comp_add, smul_add]

theorem wp {DA : ℕ → End A} {DB : ℕ → End B} {ρ : List ℕ}
    (h : ∀ j ∈ ρ, Slides σ 1 (DA j) (DB j)) : Slides σ 1 (wp DA ρ) (wp DB ρ) := by
  induction ρ with
  | nil => exact one
  | cons a ρ ih =>
    rw [Categorification.KLR.KL2.NH.wp_cons, Categorification.KLR.KL2.NH.wp_cons]
    simpa using (h a (by simp)).mul (ih fun j hj => h j (by simp [hj]))

theorem wp' {DA : ℕ → End A} {DB : ℕ → End B} {ρ : List ℕ}
    (h : ∀ j ∈ ρ, Slides σ u (DA j) (DB j)) :
    Slides σ (u ^ ρ.length) (Categorification.KLR.KL2.NH.wp DA ρ)
      (Categorification.KLR.KL2.NH.wp DB ρ) := by
  induction ρ with
  | nil => simpa using (one : Slides σ 1 (1 : End A) (1 : End B))
  | cons a ρ ih =>
    rw [Categorification.KLR.KL2.NH.wp_cons, Categorification.KLR.KL2.NH.wp_cons,
      List.length_cons, pow_succ']
    exact (h a (by simp)).mul (ih fun j hj => h j (by simp [hj]))

theorem pow (h : Slides σ u f g) (n : ℕ) : Slides σ (u ^ n) (f ^ n) (g ^ n) := by
  induction n with
  | zero => simpa using (one : Slides σ 1 (1 : End A) (1 : End B))
  | succ n ih => rw [pow_succ', pow_succ', pow_succ']; exact h.mul ih

theorem comp {C' : C} {σ' : B ⟶ C'} {h₀ : End C'} {g : End B} (h : Slides σ u f g)
    (h' : Slides σ' u' g h₀) : Slides (σ ≫ σ') (u * u') f h₀ := by
  simp only [Slides] at *
  rw [← Category.assoc, h, Preadditive.zsmul_comp, Category.assoc, h', Preadditive.comp_zsmul,
    smul_smul, Units.val_mul, Category.assoc]

theorem smul_left {R : Type*} [Semiring R] [Linear R C] (h : Slides σ u f g) (c : R) :
    Slides (c • σ) u f g := by
  simp only [Slides] at *
  rw [Linear.comp_smul, h, Linear.smul_comp, smul_comm]

/-- Commuting with a product of endomorphisms. -/
theorem endMul {σ σ' : End A} {f : End A} (h : Slides σ u f f) (h' : Slides σ' u' f f) :
    Slides (σ * σ') (u * u') f f := by
  rw [End.mul_def, mul_comm u u']; exact h'.comp h

theorem wpσ {D' : ℕ → End A} {f : End A} {ρ : List ℕ} (h : ∀ j ∈ ρ, Slides (D' j) u f f) :
    Slides (Categorification.KLR.KL2.NH.wp D' ρ : End A) (u ^ ρ.length) f f := by
  induction ρ with
  | nil => simp [Slides, End.one_def]
  | cons a ρ ih =>
    rw [Categorification.KLR.KL2.NH.wp_cons, List.length_cons, pow_succ']
    exact (h a (by simp)).endMul (ih fun j hj => h j (by simp [hj]))

theorem powσ {σ f : End A} (h : Slides σ u f f) (n : ℕ) : Slides (σ ^ n) (u ^ n) f f := by
  induction n with
  | zero => simp [Slides, End.one_def]
  | succ n ih => rw [pow_succ', pow_succ']; exact h.endMul ih

theorem wb {DA : ℕ → End A} {DB : ℕ → End B} {s n : ℕ}
    (h : ∀ j, s ≤ j → j + 1 < s + n → Slides σ 1 (DA j) (DB j)) :
    Slides σ 1 (Wb DA s n) (Wb DB s n) :=
  wp fun j hj => by
    obtain ⟨h₁, h₂⟩ := Categorification.KLR.KL2.NH.mem_w0Word_map hj
    exact h j h₁ h₂

end Slides

end Slides

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

theorem zsign_smul_hom {a b : H D Sc} (p : ZMod 2) (f : a ⟶ b) :
    zsign k p • f = ((zunit p : ℤ)) • f := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with h | h <;> simp [zsign, zunit, h]

theorem zunit_mul_self (p : ZMod 2) : zunit p * zunit p = 1 := Int.units_mul_self _

/-! ## Far commutation with its sign -/

@[simp] theorem PG.pos_dot (p : ℕ) : (PG.dot p).pos = p := rfl
@[simp] theorem PG.pos_cross (a : ℕ) : (PG.cross a).pos = a := rfl
@[simp] theorem PG.width_dot (p : ℕ) : (PG.dot p).width = 1 := rfl
@[simp] theorem PG.width_cross (a : ℕ) : (PG.cross a).width = 2 := rfl

/-- The parity of a positioned generator on a word: that of its colours there. -/
def PG.par (t : List I) : PG → ZMod 2
  | .dot p => match t[p]? with
    | some x => D.parity x
    | none => 0
  | .cross a => match t[a]?, t[a + 1]? with
    | some x, some y => D.parity x * D.parity y
    | _, _ => 0

theorem par_ofShape (l r : List I) (s : Shape I) :
    (PG.ofShape s l.length).par D (l ++ s.dom ++ r) = s.parity D := by
  cases s <;> simp [PG.par, PG.ofShape, Shape.dom, Shape.parity]

/-- Two generators at disjoint positions commute up to the product of their parities. -/
theorem far_swap_eq {t₁ t₂ : List I} (g h : PG) (hgh : g.pos + g.width ≤ h.pos)
    (hh : h.pos + h.width ≤ t₁.length) (h₁ : SChain t₁ (pl t₁ [g, h]) t₂)
    (h₂ : SChain t₁ (pl t₁ [h, g]) t₂) :
    cl D Sc t₁ t₂ [g, h] h₁ = zsign k (g.par D t₁ * h.par D t₁) • cl D Sc t₁ t₂ [h, g] h₂ := by
  obtain ⟨l, sg, r, rfl, hsg, hl, hw⟩ := exists_split g 0 t₁ (Nat.zero_le _) (by omega)
  obtain ⟨m, sh, v, rfl, hsh, hm, hw'⟩ := exists_split h (l ++ sg.dom).length r
    (by simp; omega) (by simp at hh ⊢; omega)
  simp only [zero_add] at hsg
  subst hsg hsh
  have e : l ++ sg.dom ++ (m ++ sh.dom ++ v) = l ++ sg.dom ++ m ++ sh.dom ++ v := by
    simp
  have e' : (l ++ sg.dom).length + m.length = (l ++ sg.dom ++ m).length := by simp; omega
  revert h₁ h₂
  rw [e, e']
  intro h₁ h₂
  have ht : tgt (l ++ sg.dom ++ m ++ sh.dom ++ v)
      [PG.ofShape sg l.length, PG.ofShape sh (l ++ sg.dom ++ m).length] =
        l ++ sg.cod ++ m ++ sh.cod ++ v := by
    cases sg <;> cases sh <;>
      simp [PG.act, PG.ofShape, Shape.dom, Shape.cod, List.take_append, List.drop_append]
  obtain rfl : _ = t₂ := ht ▸ tgt_eq h₁
  have p₁ : (PG.ofShape sg l.length).par D (l ++ sg.dom ++ m ++ sh.dom ++ v) = sg.parity D := by
    simpa only [List.append_assoc] using par_ofShape D l (m ++ sh.dom ++ v) sg
  rw [p₁, par_ofShape D (l ++ sg.dom ++ m) v sh]
  exact cl_interchange D Sc l m v sg sh h₁ h₂

/-- Generators at disjoint positions of a word commute in its endomorphism ring, up to the
product of their parities. -/
theorem genE_far {w : List I} {g h : PG} (hgh : g.pos + g.width ≤ h.pos)
    (hh : h.pos + h.width ≤ w.length) (hg : SChain w (pl w [g]) w)
    (hh' : SChain w (pl w [h]) w) :
    Slides (genE D Sc w h) (zunit (g.par D w * h.par D w)) (genE D Sc w g) (genE D Sc w g) := by
  have e := far_swap_eq D Sc g h hgh hh (sChain_append_of hg hh') (sChain_append_of hh' hg)
  rw [Slides, genE_eq D Sc hg, genE_eq D Sc hh', cl_comp, cl_comp, ← zsign_smul_hom]
  exact e

/-- A generator left of a generator `h` from `w` to `w'` passes through it. -/
theorem genE_far_left {w w' : List I} {g h : PG} (hgh : g.pos + g.width ≤ h.pos)
    (hh : h.pos + h.width ≤ w.length) (hg : SChain w (pl w [g]) w)
    (hg' : SChain w' (pl w' [g]) w') (hσ : SChain w (pl w [h]) w') :
    Slides (cl D Sc w w' [h] hσ) (zunit (g.par D w * h.par D w)) (genE D Sc w g)
      (genE D Sc w' g) := by
  have e := far_swap_eq D Sc g h hgh hh (sChain_append_of hg hσ) (sChain_append_of hσ hg')
  rw [Slides, genE_eq D Sc hg, genE_eq D Sc hg', cl_comp, cl_comp, ← zsign_smul_hom]
  exact e

/-- A generator right of a generator `h` from `w` to `w'` passes through it. -/
theorem genE_far_right {w w' : List I} {g h : PG} (hgh : h.pos + h.width ≤ g.pos)
    (hg₁ : g.pos + g.width ≤ w.length) (hg : SChain w (pl w [g]) w)
    (hg' : SChain w' (pl w' [g]) w') (hσ : SChain w (pl w [h]) w') :
    Slides (cl D Sc w w' [h] hσ) (zunit (h.par D w * g.par D w)) (genE D Sc w g)
      (genE D Sc w' g) := by
  have e := far_swap_eq D Sc h g hgh hg₁ (sChain_append_of hσ hg') (sChain_append_of hg hσ)
  rw [eq_zsign_smul_iff] at e
  rw [Slides, genE_eq D Sc hg, genE_eq D Sc hg', cl_comp, cl_comp, ← zsign_smul_hom]
  exact e

/-- A generator at positions disjoint from those of a generator `h` from `w` to `w'` passes
through it. -/
theorem genE_slides {w w' : List I} {g h : PG}
    (hd : g.pos + g.width ≤ h.pos ∨ h.pos + h.width ≤ g.pos)
    (hgl : g.pos + g.width ≤ w.length) (hhl : h.pos + h.width ≤ w.length)
    (hg : SChain w (pl w [g]) w) (hg' : SChain w' (pl w' [g]) w')
    (hσ : SChain w (pl w [h]) w') :
    Slides (cl D Sc w w' [h] hσ) (zunit (g.par D w * h.par D w)) (genE D Sc w g)
      (genE D Sc w' g) := by
  rcases hd with hd | hd
  · exact genE_far_left D Sc hd hhl hg hg' hσ
  · rw [mul_comm]; exact genE_far_right D Sc hd hgl hg hg' hσ

theorem sChain_cross_of {w : List I} {q : ℕ} {x : I} (h₁ : w[q]? = some x)
    (h₂ : w[q + 1]? = some x) : SChain w (pl w [.cross q]) w := by
  have hq : q + 1 < w.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at h₂; simp at h₂
  obtain ⟨l, y, z, r, rfl, rfl⟩ := exists_split_cross hq
  have hy : y = x := by simpa using h₁
  have hz : z = x := by simpa [List.getElem?_append_right] using h₂
  subst hy hz
  exact sChain_cross l r _ rfl rfl

theorem par_dot_of {w : List I} {p : ℕ} {x : I} (h : w[p]? = some x) :
    (PG.dot p).par D w = D.parity x := by simp [PG.par, h]

theorem par_cross_of {w : List I} {q : ℕ} {x y : I} (h₁ : w[q]? = some x)
    (h₂ : w[q + 1]? = some y) : (PG.cross q).par D w = D.parity x * D.parity y := by
  simp [PG.par, h₁, h₂]

open SignedNilHecke in
/-- A Demazure element of a block of colour `x` passes through a generator at disjoint
positions, with no sign. -/
theorem slides_dem_gen {w w' : List I} {h : PG} (hσ : SChain w (pl w [h]) w') {x : I}
    {ε : ℤˣ} {s n q : ℕ} (h₁ : s ≤ q) (h₂ : q + 1 < s + n)
    (hcol : ∀ p, s ≤ p → p < s + n → w[p]? = some x)
    (hcol' : ∀ p, s ≤ p → p < s + n → w'[p]? = some x)
    (hd : s + n ≤ h.pos ∨ h.pos + h.width ≤ s) (hhl : h.pos + h.width ≤ w.length) :
    Slides (cl D Sc w w' [h] hσ) 1 (dem ε s n (dotE D Sc w) (crossE D Sc w) q)
      (dem ε s n (dotE D Sc w') (crossE D Sc w') q) := by
  have hl : s + n ≤ w.length := by
    by_contra hc
    have := hcol (s + n - 1) (by omega) (by omega)
    rw [List.getElem?_eq_none (by omega)] at this
    simp at this
  rw [dem_of h₁ h₂, dem_of h₁ h₂]
  refine Slides.neg (Slides.zsmul ?_ _)
  rw [← zunit_mul_self (D.parity x * h.par D w)]
  have hT := genE_slides D Sc (g := .cross q)
    (by rw [PG.pos_cross, PG.width_cross]; omega) (by rw [PG.pos_cross, PG.width_cross]; omega) hhl
    (sChain_cross_of (hcol q h₁ (by omega)) (hcol (q + 1) (by omega) h₂))
    (sChain_cross_of (hcol' q h₁ (by omega)) (hcol' (q + 1) (by omega) h₂)) hσ
  have hX := genE_slides D Sc (g := .dot (q + 1))
    (by rw [PG.pos_dot, PG.width_dot]; omega) (by rw [PG.pos_dot, PG.width_dot]; omega) hhl
    (sChain_pl w _) (sChain_pl w' _) hσ
  rw [par_cross_of D (hcol q h₁ (by omega)) (hcol (q + 1) (by omega) h₂), parity_sq] at hT
  rw [par_dot_of D (hcol (q + 1) (by omega) h₂)] at hX
  exact hT.mul hX

open SignedNilHecke in
/-- A block idempotent passes through a generator at disjoint positions, with no sign. -/
theorem slides_idem_gen {w w' : List I} {h : PG} (hσ : SChain w (pl w [h]) w') {x : I}
    {ε : ℤˣ} {s n t m : ℕ} (h₁ : s ≤ t) (h₂ : t + m ≤ s + n)
    (hcol : ∀ p, s ≤ p → p < s + n → w[p]? = some x)
    (hcol' : ∀ p, s ≤ p → p < s + n → w'[p]? = some x)
    (hd : s + n ≤ h.pos ∨ h.pos + h.width ≤ s) (hhl : h.pos + h.width ≤ w.length) :
    Slides (cl D Sc w w' [h] hσ) 1 (idem ε s n (dotE D Sc w) (crossE D Sc w) t m)
      (idem ε s n (dotE D Sc w') (crossE D Sc w') t m) :=
  Slides.wb fun q h₁' h₂' => slides_dem_gen D Sc hσ (by omega) (by omega) hcol hcol' hd hhl


end OddMath.QuiverHecke
