/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PositionalRelations
import OddMath.QuiverHecke.SignedNilHecke

/-!
# Same-colour blocks of a word

On a word `w = u ++ i^n ++ v` of the quiver Hecke supercategory, the dots on the strands of the
block `i^n` and the crossings of adjacent strands of the block satisfy the relations of the
nilHecke algebra (odd if `i` is odd), in the endomorphism ring of `w`: this is
`isSignedNilHeckeFamily_block`. Its Demazure idempotents are the divided-power idempotents
`1_u ⊗ e_n ⊗ 1_v` of Brundan–Ellis, arXiv:1701.04133v2, §11, used in Proposition 11.2 and
Lemma 11.6 on the words `i^k j i^{n-k}`.

The same-colour relations (1.7)–(1.9) of BE2 at a position (`cross_cross_eq`, `slide_left_eq`,
`slide_right_eq`, `braid_eq`) hold exactly, not only modulo words with fewer crossings as in
`PositionalRelations`.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LinDiagram
open SKM (zsign)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

theorem cl_nil (t : List I) (h : SChain t (pl t []) t) : cl D Sc t t [] h = 𝟙 _ := by
  rw [cl, ← Presentation.diag_id]
  exact (pres D Sc).diag_eq_of_layers_eq rfl

theorem cl_comp {t t' t'' : List I} (gs hs : List PG) (h₁ : SChain t (pl t gs) t')
    (h₂ : SChain t' (pl t' hs) t'') (h : SChain t (pl t (gs ++ hs)) t'') :
    cl D Sc t t' gs h₁ ≫ cl D Sc t' t'' hs h₂ = cl D Sc t t'' (gs ++ hs) h := by
  have e := tgt_eq h₁
  rw [cl, cl, cl, ← Presentation.diag_comp]
  apply Presentation.diag_eq_of_layers_eq
  simp [mkD, layList, pl_append, e]

theorem sChain_append_self {t : List I} {gs hs : List PG} (h₁ : SChain t (pl t gs) t)
    (h₂ : SChain t (pl t hs) t) : SChain t (pl t (gs ++ hs)) t := by
  have := sChain_pl t (gs ++ hs)
  rwa [tgt_append, tgt_eq h₁, tgt_eq h₂] at this

/-- Products in the endomorphism ring of a word are concatenations, the right factor first. -/
theorem cl_mul {t : List I} (gs hs : List PG) (h₁ : SChain t (pl t gs) t)
    (h₂ : SChain t (pl t hs) t) :
    (show End ((pres D Sc).obj (ob D t)) from cl D Sc t t hs h₂) *
      (show End ((pres D Sc).obj (ob D t)) from cl D Sc t t gs h₁) =
      cl D Sc t t (gs ++ hs) (sChain_append_self h₁ h₂) :=
  cl_comp D Sc gs hs h₁ h₂ _

/-! ## Exact same-colour relations at a position -/

section Rels

variable (l r : List I) (i : I)

/-- (1.7) for equal colours: the square of a crossing vanishes. -/
theorem cross_cross_eq
    (h : SChain (l ++ [i, i] ++ r) (pl _ [.cross l.length, .cross l.length]) (l ++ [i, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross l.length] h = 0 := by
  rw [cl_eq_lin D Sc l r _ (sChain_cross_cross i i) _ h (pl_cross_cross l r i i)]
  exact lin_rel_eq D Sc l r (Rel.quadEq i)

/-- (1.8), left, for equal colours. -/
theorem slide_left_eq
    (h₁ : SChain (l ++ [i, i] ++ r) (pl _ [.dot l.length, .cross l.length]) (l ++ [i, i] ++ r))
    (h₂ : SChain (l ++ [i, i] ++ r) (pl _ [.cross l.length, .dot (l.length + 1)])
      (l ++ [i, i] ++ r)) :
    cl D Sc _ _ [.dot l.length, .cross l.length] h₁ -
        zsign k (D.parity i * D.parity i) •
          cl D Sc _ _ [.cross l.length, .dot (l.length + 1)] h₂ =
      𝟙 _ := by
  have p₁ : SChain [i, i] (dotsL [] i [i] 1 ++ crossL [] i i []) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, i] (crossL [] i i [] ++ dotsL [i] i [] 1) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂
      (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  have hr := lin_rel_eq D Sc l r (Rel.slideLEq i)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, sub_eq_zero] at hr
  rw [hr, lin_whisker_idg, ← Presentation.diag_id]
  exact (pres D Sc).diag_eq_of_layers_eq rfl

/-- (1.8), right, for equal colours. -/
theorem slide_right_eq
    (h₁ : SChain (l ++ [i, i] ++ r) (pl _ [.cross l.length, .dot l.length]) (l ++ [i, i] ++ r))
    (h₂ : SChain (l ++ [i, i] ++ r) (pl _ [.dot (l.length + 1), .cross l.length])
      (l ++ [i, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .dot l.length] h₁ -
        zsign k (D.parity i * D.parity i) •
          cl D Sc _ _ [.dot (l.length + 1), .cross l.length] h₂ =
      𝟙 _ := by
  have p₁ : SChain [i, i] (crossL [] i i [] ++ dotsL [] i [i] 1) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, i] (dotsL [i] i [] 1 ++ crossL [] i i []) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂
      (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  have hr := lin_rel_eq D Sc l r (Rel.slideREq i)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, sub_eq_zero] at hr
  rw [hr, lin_whisker_idg, ← Presentation.diag_id]
  exact (pres D Sc).diag_eq_of_layers_eq rfl

/-- (1.9) for three strands of one colour. -/
theorem braid_eq
    (h₁ : SChain (l ++ [i, i, i] ++ r)
      (pl _ [.cross l.length, .cross (l.length + 1), .cross l.length]) (l ++ [i, i, i] ++ r))
    (h₂ : SChain (l ++ [i, i, i] ++ r)
      (pl _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)])
      (l ++ [i, i, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross (l.length + 1), .cross l.length] h₁ =
      cl D Sc _ _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)] h₂ := by
  have p₁ : SChain [i, i, i] (crossL [] i i [i] ++ crossL [i] i i [] ++ crossL [] i i [i])
      [i, i, i] := by simp [crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, i, i] (crossL [i] i i [] ++ crossL [] i i [i] ++ crossL [i] i i [])
      [i, i, i] := by simp [crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append]),
    cl_eq_lin D Sc l r _ p₂ _ h₂
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append])]
  have hr := lin_rel_eq D Sc l r (Rel.braid i i i (by simp))
  simp only [relation, whisker_sub, Presentation.lin_sub, sub_eq_zero] at hr
  exact hr

end Rels

/-! ## Dots and crossings as endomorphisms -/

/-- The sign `(-1)^p` as a unit of `ℤ`. -/
def zunit (p : ZMod 2) : ℤˣ := if p = 1 then -1 else 1

theorem zsign_smul {a : H D Sc} (p : ZMod 2) (f : End a) :
    zsign k p • f = ((zunit p : ℤ)) • f := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with h | h <;> simp [zsign, zunit, h]

theorem parity_sq (p : ZMod 2) : p * p = p := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with h | h <;> simp [h]

variable (w : List I)

/-- The positioned generator `g` as an endomorphism of the word `w` when it does not change the
word (a dot, or a crossing of two strands of one colour), and `0` otherwise. -/
def genE (g : PG) : End ((pres D Sc).obj (ob D w)) :=
  if h : SChain w (pl w [g]) w then cl D Sc w w [g] h else 0

/-- The dot on strand `a` of the word `w`. -/
abbrev dotE (a : ℕ) : End ((pres D Sc).obj (ob D w)) := genE D Sc w (.dot a)

/-- The crossing of strands `a` and `a + 1` of `w` when they have the same colour, and `0`
otherwise. -/
abbrev crossE (a : ℕ) : End ((pres D Sc).obj (ob D w)) := genE D Sc w (.cross a)

variable {w}

theorem genE_eq {g : PG} (h : SChain w (pl w [g]) w) : genE D Sc w g = cl D Sc w w [g] h :=
  dite_eq_left h

theorem sChain_ofShape (l r : List I) (g : Shape I) (hg : g.cod = g.dom) {t : List I}
    (ht : t = l ++ g.dom ++ r) : SChain t (pl t [PG.ofShape g l.length]) t := by
  subst ht
  have := sChain_pl (l ++ g.dom ++ r) [PG.ofShape g l.length]
  rwa [tgt_cons, tgt_nil, act_ofShape, hg] at this

theorem sChain_dot (l r : List I) (x : I) {t : List I} {p : ℕ} (ht : t = l ++ [x] ++ r)
    (hp : l.length = p) : SChain t (pl t [.dot p]) t :=
  hp ▸ sChain_ofShape l r (.dot x) rfl ht

theorem sChain_cross (l r : List I) (i : I) {t : List I} {p : ℕ} (ht : t = l ++ [i, i] ++ r)
    (hp : l.length = p) : SChain t (pl t [.cross p]) t :=
  hp ▸ sChain_ofShape l r (.cross i i) rfl ht

/-- The super interchange law for two generators at disjoint positions of a word. -/
theorem genE_interchange (l m v : List I) (g h : Shape I) (hg : g.cod = g.dom)
    (hh : h.cod = h.dom) (hw : w = l ++ g.dom ++ m ++ h.dom ++ v) {p q : ℕ} (hp : l.length = p)
    (hq : (l ++ g.dom ++ m).length = q) :
    genE D Sc w (PG.ofShape h q) * genE D Sc w (PG.ofShape g p) =
      zsign k (g.parity D * h.parity D) •
        (genE D Sc w (PG.ofShape g p) * genE D Sc w (PG.ofShape h q)) := by
  subst hw hp hq
  have h₁ := sChain_ofShape l (m ++ h.dom ++ v) g hg (t := l ++ g.dom ++ m ++ h.dom ++ v)
    (by simp)
  have h₂ := sChain_ofShape (l ++ g.dom ++ m) v h hh (t := l ++ g.dom ++ m ++ h.dom ++ v) rfl
  rw [genE_eq D Sc h₁, genE_eq D Sc h₂, cl_mul, cl_mul]
  cases g with
  | dot x =>
    cases h with
    | dot y => exact cl_interchange D Sc l m v _ _ _ _
    | cross y y' =>
      obtain rfl : y = y' := by simp [Shape.cod, Shape.dom] at hh; exact hh.2
      exact cl_interchange D Sc l m v _ _ _ _
  | cross x x' =>
    obtain rfl : x = x' := by simp [Shape.cod, Shape.dom] at hg; exact hg.2
    cases h with
    | dot y => exact cl_interchange D Sc l m v _ _ _ _
    | cross y y' =>
      obtain rfl : y = y' := by simp [Shape.cod, Shape.dom] at hh; exact hh.2
      exact cl_interchange D Sc l m v _ _ _ _

section Block

variable (l r : List I) (i : I) {j : ℕ} (hj : l.length = j)
include hj

theorem crossE_mul_crossE (hw : w = l ++ [i, i] ++ r) : crossE D Sc w j * crossE D Sc w j = 0 := by
  subst hw hj
  simp only [crossE]
  rw [genE_eq D Sc (sChain_cross l r i rfl rfl), cl_mul]
  exact cross_cross_eq D Sc l r i _

theorem crossE_dotE (hw : w = l ++ [i, i] ++ r) :
    crossE D Sc w j * dotE D Sc w j -
        zsign k (D.parity i * D.parity i) • (dotE D Sc w (j + 1) * crossE D Sc w j) = 1 := by
  subst hw hj
  simp only [dotE, crossE]
  rw [genE_eq D Sc (sChain_cross l r i rfl rfl),
    genE_eq D Sc (sChain_dot l (i :: r) i (by simp) rfl),
    genE_eq D Sc (sChain_dot (l ++ [i]) r i (by simp) (by simp)), cl_mul, cl_mul]
  exact slide_left_eq D Sc l r i _ _

theorem dotE_crossE (hw : w = l ++ [i, i] ++ r) :
    dotE D Sc w j * crossE D Sc w j -
        zsign k (D.parity i * D.parity i) • (crossE D Sc w j * dotE D Sc w (j + 1)) = 1 := by
  subst hw hj
  simp only [dotE, crossE]
  rw [genE_eq D Sc (sChain_cross l r i rfl rfl),
    genE_eq D Sc (sChain_dot l (i :: r) i (by simp) rfl),
    genE_eq D Sc (sChain_dot (l ++ [i]) r i (by simp) (by simp)), cl_mul, cl_mul]
  exact slide_right_eq D Sc l r i _ _

theorem crossE_braid (hw : w = l ++ [i, i, i] ++ r) :
    crossE D Sc w j * crossE D Sc w (j + 1) * crossE D Sc w j =
      crossE D Sc w (j + 1) * crossE D Sc w j * crossE D Sc w (j + 1) := by
  subst hw hj
  simp only [crossE]
  rw [genE_eq D Sc (sChain_cross l (i :: r) i (by simp) rfl),
    genE_eq D Sc (sChain_cross (l ++ [i]) r i (by simp) (by simp)), cl_mul, cl_mul, cl_mul, cl_mul]
  exact braid_eq D Sc l r i _ _

end Block

theorem replicate_split₁ (pre post : List I) (i : I) {n : ℕ} (a d : ℕ)
    (h₁ : pre.length ≤ a) (h₂ : a + d ≤ pre.length + n) :
    pre ++ List.replicate n i ++ post =
      (pre ++ List.replicate (a - pre.length) i) ++ List.replicate d i ++
        (List.replicate (pre.length + n - a - d) i ++ post) := by
  have e : n = (a - pre.length) + d + (pre.length + n - a - d) := by omega
  conv_lhs => rw [e]
  simp only [List.replicate_add, List.append_assoc]

theorem replicate_split₂ (pre post : List I) (i : I) {n : ℕ} (a d₁ b d₂ : ℕ)
    (h₁ : pre.length ≤ a) (h₂ : a + d₁ ≤ b) (h₃ : b + d₂ ≤ pre.length + n) :
    pre ++ List.replicate n i ++ post =
      (pre ++ List.replicate (a - pre.length) i) ++ List.replicate d₁ i ++
        List.replicate (b - a - d₁) i ++ List.replicate d₂ i ++
        (List.replicate (pre.length + n - b - d₂) i ++ post) := by
  have e : n = (a - pre.length) + d₁ + (b - a - d₁) + d₂ + (pre.length + n - b - d₂) := by
    omega
  conv_lhs => rw [e]
  simp only [List.replicate_add, List.append_assoc]

open SignedNilHecke in
/-- The dots and crossings on a block `i^n` of a word satisfy the relations of the nilHecke
ring for `i` even and of the odd nilHecke ring for `i` odd, with `ε = (-1)^{|i|}`. -/
theorem isSignedNilHeckeFamily_block (pre post : List I) (i : I) (n : ℕ) :
    IsSignedNilHeckeFamily (zunit (D.parity i)) pre.length n
      (dotE D Sc (pre ++ List.replicate n i ++ post))
      (crossE D Sc (pre ++ List.replicate n i ++ post)) := by
  set w := pre ++ List.replicate n i ++ post with hw
  have dd : ∀ a b, pre.length ≤ a → a < b → b < pre.length + n →
      dotE D Sc w b * dotE D Sc w a =
        (zunit (D.parity i) : ℤ) • (dotE D Sc w a * dotE D Sc w b) := by
    intro a b ha hab hb
    have := genE_interchange D Sc _ _ _ (.dot i) (.dot i) rfl rfl
      (replicate_split₂ pre post i (n := n) a 1 b 1 ha hab hb) (p := a) (q := b)
      (by simp; omega) (by simp [Shape.dom]; omega)
    simpa only [Shape.parity, PG.ofShape, parity_sq, zsign_smul] using this
  have dc : ∀ a j, pre.length ≤ a → a < j → j + 1 < pre.length + n →
      crossE D Sc w j * dotE D Sc w a =
        (zunit (D.parity i) : ℤ) • (dotE D Sc w a * crossE D Sc w j) := by
    intro a j ha haj hj
    have := genE_interchange D Sc _ _ _ (.dot i) (.cross i i) rfl rfl
      (replicate_split₂ pre post i (n := n) a 1 j 2 ha haj hj) (p := a) (q := j)
      (by simp; omega) (by simp [Shape.dom]; omega)
    simpa only [Shape.parity, PG.ofShape, parity_sq, zsign_smul] using this
  have cd : ∀ j a, pre.length ≤ j → j + 1 < a → a < pre.length + n →
      dotE D Sc w a * crossE D Sc w j =
        (zunit (D.parity i) : ℤ) • (crossE D Sc w j * dotE D Sc w a) := by
    intro j a hj hja ha
    have := genE_interchange D Sc _ _ _ (.cross i i) (.dot i) rfl rfl
      (replicate_split₂ pre post i (n := n) j 2 a 1 hj (by omega) ha) (p := j) (q := a)
      (by simp; omega) (by simp [Shape.dom]; omega)
    simpa only [Shape.parity, PG.ofShape, parity_sq, zsign_smul] using this
  have cc : ∀ j l, pre.length ≤ j → j + 1 < l → l + 1 < pre.length + n →
      crossE D Sc w l * crossE D Sc w j =
        (zunit (D.parity i) : ℤ) • (crossE D Sc w j * crossE D Sc w l) := by
    intro j l hj hjl hl
    have := genE_interchange D Sc _ _ _ (.cross i i) (.cross i i) rfl rfl
      (replicate_split₂ pre post i (n := n) j 2 l 2 hj (by omega) (by omega)) (p := j) (q := l)
      (by simp; omega) (by simp [Shape.dom]; omega)
    simpa only [Shape.parity, PG.ofShape, parity_sq, zsign_smul] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha ha' hb hb' hab
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · rw [dd a b ha h hb', eps_smul_eps_smul]
    · exact dd b a hb h ha'
  · intro a j ha ha' hj hj' h₁ h₂
    rcases Nat.lt_or_gt_of_ne h₁ with h | h
    · rw [dc a j ha h hj', eps_smul_eps_smul]
    · exact cd j a hj (by omega) ha'
  · intro j l hj hjl hl
    rw [cc j l hj hjl hl, eps_smul_eps_smul]
  · intro j hj hj'
    exact crossE_mul_crossE D Sc _ (List.replicate (pre.length + n - j - 2) i ++ post) i
      (by simp; omega) (replicate_split₁ pre post i (n := n) j 2 hj (by omega))
  · intro j hj hj'
    exact crossE_braid D Sc _ (List.replicate (pre.length + n - j - 3) i ++ post) i
      (by simp; omega) (replicate_split₁ pre post i (n := n) j 3 hj (by omega))
  · intro j hj hj'
    have := crossE_dotE D Sc (j := j) _ (List.replicate (pre.length + n - j - 2) i ++ post) i
      (by simp; omega) (replicate_split₁ pre post i (n := n) j 2 hj (by omega))
    simpa only [Shape.parity, PG.ofShape, parity_sq, zsign_smul] using this
  · intro j hj hj'
    have := dotE_crossE D Sc (j := j) _ (List.replicate (pre.length + n - j - 2) i ++ post) i
      (by simp; omega) (replicate_split₁ pre post i (n := n) j 2 hj (by omega))
    simpa only [Shape.parity, PG.ofShape, parity_sq, zsign_smul] using this

end OddMath.QuiverHecke
