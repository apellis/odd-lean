/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ColourBlock

/-!
# The relations of `H` between different colours, exactly at a position

The relations (1.7)–(1.9) of the quiver Hecke supercategory (Brundan–Ellis,
arXiv:1701.04133v2, §11) for strands of different colours, whiskered to an arbitrary position of
a word, as exact identities between classes of positioned words (dots sliding through a crossing
of different colours are `slide_left_ne`, `slide_right_ne` in `Centre`): a double crossing of
different colours is a polynomial in the dots (`cross_cross_ne`), and the
braid relation holds exactly except on `i j i`, where it has BE2's correction term
(`braid_ne`, `braid_iji`). Polynomials in dots are written in the endomorphism ring of the word
(`dotE_pow`).

These are the inputs, beyond the same-colour relations of `ColourBlock`, of the Khovanov–Lauda
computation behind Proposition 11.2.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LinDiagram
open SKM (zsign)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

theorem sChain_dot_pow (t : List I) (p n : ℕ) :
    SChain t (pl t (List.replicate n (.dot p))) t := by
  have := sChain_pl t (List.replicate n (.dot p))
  rwa [tgt_dots] at this

theorem dotE_eq (w : List I) (p : ℕ) :
    dotE D Sc w p = cl D Sc w w [.dot p] (sChain_pl w _) :=
  genE_eq D Sc (sChain_pl w [.dot p])

/-- `n` dots on strand `p` are the `n`-th power of the dot. -/
theorem dotE_pow (w : List I) (p n : ℕ) :
    dotE D Sc w p ^ n = cl D Sc w w (List.replicate n (.dot p)) (sChain_dot_pow w p n) := by
  induction n with
  | zero => rw [pow_zero, End.one_def]; exact (cl_nil D Sc w rfl).symm
  | succ n ih =>
    rw [pow_succ, ih, dotE_eq, cl_mul]
    rfl

section Rels

variable (l r : List I)

/-- (1.9) on three strands `i j m` other than `i j i` with `i ≠ j`: exact. -/
theorem braid_ne (i j m : I) (hb : ¬(i = m ∧ i ≠ j))
    (h₁ : SChain (l ++ [i, j, m] ++ r)
      (pl _ [.cross l.length, .cross (l.length + 1), .cross l.length]) (l ++ [m, j, i] ++ r))
    (h₂ : SChain (l ++ [i, j, m] ++ r)
      (pl _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)])
      (l ++ [m, j, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross (l.length + 1), .cross l.length] h₁ =
      cl D Sc _ _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)] h₂ := by
  have p₁ : SChain [i, j, m] (crossL [] i j [m] ++ crossL [j] i m [] ++ crossL [] j m [i])
      [m, j, i] := by simp [crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, j, m] (crossL [i] j m [] ++ crossL [] i m [j] ++ crossL [m] i j [])
      [m, j, i] := by simp [crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append]),
    cl_eq_lin D Sc l r _ p₂ _ h₂
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append])]
  have hr := lin_rel_eq D Sc l r (Rel.braid i j m hb)
  simp only [relation, whisker_sub, Presentation.lin_sub, sub_eq_zero] at hr
  exact hr

theorem lin_dots_left (i j : I) (n : ℕ) :
    (pres D Sc).lin (LinDiagram.whisker (dg (k := k) D (dotsL [] i [j] n) (sChain_dotsL [] i [j] n))
      (ob D l) r (Obj.whiskerOK_of_subsingleton _ _ _)) =
      dotE D Sc (l ++ [i, j] ++ r) l.length ^ n := by
  rw [dotE_pow]
  exact (cl_eq_lin D Sc l r _ _ _ _ (pl_dots_left l r i j n)).symm

theorem lin_dots_right (i j : I) (n : ℕ) :
    (pres D Sc).lin (LinDiagram.whisker (dg (k := k) D (dotsL [i] j [] n) (sChain_dotsL [i] j [] n))
      (ob D l) r (Obj.whiskerOK_of_subsingleton _ _ _)) =
      dotE D Sc (l ++ [i, j] ++ r) (l.length + 1) ^ n := by
  rw [dotE_pow]
  exact (cl_eq_lin D Sc l r _ _ _ _ (pl_dots_right l r i j n)).symm

/-- (1.7) for different colours with `d_ij ≠ 0`: the double crossing is the polynomial
`t_ij x^{d_ij} + t_ji y^{d_ji} + ∑ s_ij^{pq} x^p y^q` in the dots `x`, `y` on its two
strands. -/
theorem cross_cross_ne {i j : I} (hij : i ≠ j) (hd : D.d i j ≠ 0)
    (h : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length, .cross l.length]) (l ++ [i, j] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross l.length] h =
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (dotE D Sc (l ++ [i, j] ++ r) l.length ^ p *
          dotE D Sc (l ++ [i, j] ++ r) (l.length + 1) ^ q) +
      ((Sc.t i j : k) • dotE D Sc (l ++ [i, j] ++ r) l.length ^ D.dn i j +
        (Sc.t j i : k) • dotE D Sc (l ++ [i, j] ++ r) (l.length + 1) ^ D.dn j i) := by
  rw [cl_eq_lin D Sc l r _ (sChain_cross_cross i j) _ h (pl_cross_cross l r i j)]
  have hr := lin_rel_eq D Sc l r (Rel.quadNe i j hij hd)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, lin_whisker_sum, sub_eq_zero] at hr
  rw [sub_sub, sub_eq_iff_eq_add] at hr
  rw [hr, lin_dots_left, lin_dots_right]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [dotE_pow, dotE_pow, cl_mul]
  exact (cl_eq_lin D Sc l r _ _ _ _ (by
    rw [pl_append, tgt_dots, List.map_append]
    exact congrArg₂ (· ++ ·) (pl_dots_right l r i j q) (pl_dots_left l r i j p))).symm

/-- (1.7) for different colours with `d_ij = 0`: the double crossing is `t_ij`. -/
theorem cross_cross_ne_zero {i j : I} (hij : i ≠ j) (hd : D.d i j = 0)
    (h : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length, .cross l.length]) (l ++ [i, j] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross l.length] h = (Sc.t i j : k) • 𝟙 _ := by
  rw [cl_eq_lin D Sc l r _ (sChain_cross_cross i j) _ h (pl_cross_cross l r i j)]
  have hr := lin_rel_eq D Sc l r (Rel.quadZero i j hij hd)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, sub_eq_zero] at hr
  rw [hr, lin_whisker_idg, ← Presentation.diag_id]
  congr 1

/-- (1.9) on `i j i` with `i ≠ j`: the two sides of the braid relation differ by BE2's
correction, a polynomial in the dots `x`, `y`, `z` on the three strands (from the left). -/
theorem braid_iji {i j : I} (hij : i ≠ j)
    (h₁ : SChain (l ++ [i, j, i] ++ r)
      (pl _ [.cross l.length, .cross (l.length + 1), .cross l.length]) (l ++ [i, j, i] ++ r))
    (h₂ : SChain (l ++ [i, j, i] ++ r)
      (pl _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)])
      (l ++ [i, j, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross (l.length + 1), .cross l.length] h₁ -
        cl D Sc _ _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)] h₂ =
      ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
            (dotE D Sc (l ++ [i, j, i] ++ r) l.length ^ (D.dn i j - 1 - s) *
              dotE D Sc (l ++ [i, j, i] ++ r) (l.length + 2) ^ s) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
          ∑ s ∈ Finset.range p, (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
            (dotE D Sc (l ++ [i, j, i] ++ r) l.length ^ (p - 1 - s) *
              dotE D Sc (l ++ [i, j, i] ++ r) (l.length + 1) ^ q *
              dotE D Sc (l ++ [i, j, i] ++ r) (l.length + 2) ^ s) := by
  have p₁ : SChain [i, j, i] (crossL [] i j [i] ++ crossL [j] i i [] ++ crossL [] j i [i])
      [i, j, i] := by simp [crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, j, i] (crossL [i] j i [] ++ crossL [] i i [j] ++ crossL [i] i j [])
      [i, j, i] := by simp [crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append]),
    cl_eq_lin D Sc l r _ p₂ _ h₂
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append])]
  have hr := lin_rel_eq D Sc l r (Rel.braidEq i j hij)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, lin_whisker_sum] at hr
  rw [sub_sub, sub_eq_zero] at hr
  rw [hr]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [dotE_pow, dotE_pow, cl_mul]
    exact (cl_eq_lin D Sc l r _ _ _ _ (by
      rw [pl_append, tgt_dots, List.map_append]
      exact congrArg₂ (· ++ ·) (pl_dotsL l r [i, j] [] i s) (pl_dotsL l r [] [j, i] i _))).symm
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [dotE_pow, dotE_pow, dotE_pow, cl_mul, cl_mul]
    exact (cl_eq_lin D Sc l r _ _ _ _ (by
      rw [pl_append, pl_append, tgt_dots, tgt_dots, List.map_append, List.map_append]
      exact (congrArg₂ (· ++ ·) (pl_dotsL l r [i, j] [] i s)
        (congrArg₂ (· ++ ·) (pl_dotsL l r [i] [i] j q) (pl_dotsL l r [] [j, i] i _))).trans
          (List.append_assoc _ _ _).symm)).symm

end Rels

/-! ## Generators of different words at disjoint positions -/

theorem sChain_comp {t t' t'' : List I} {gs hs : List PG} (h₁ : SChain t (pl t gs) t')
    (h₂ : SChain t' (pl t' hs) t'') : SChain t (pl t (gs ++ hs)) t'' := by
  rw [pl_append, tgt_eq h₁]
  exact h₁.append h₂

/-- `cl_comp` with the composite chain supplied. -/
theorem cl_comp' {t t' t'' : List I} (gs hs : List PG) (h₁ : SChain t (pl t gs) t')
    (h₂ : SChain t' (pl t' hs) t'') :
    cl D Sc t t' gs h₁ ≫ cl D Sc t' t'' hs h₂ = cl D Sc t t'' (gs ++ hs) (sChain_comp h₁ h₂) :=
  cl_comp D Sc gs hs h₁ h₂

theorem sChain_ofShape' (l r : List I) (g : Shape I) {t t' : List I} {p : ℕ}
    (ht : t = l ++ g.dom ++ r) (ht' : t' = l ++ g.cod ++ r) (hp : l.length = p) :
    SChain t (pl t [PG.ofShape g p]) t' := by
  subst ht ht' hp
  have := sChain_pl (l ++ g.dom ++ r) [PG.ofShape g l.length]
  rwa [tgt_cons, tgt_nil, act_ofShape] at this

/-- A generator `g` that does not change the word, to the left of a generator `h`, moves
through `h` by the super interchange law. -/
theorem genE_comp_cl (l m v : List I) (g h : Shape I) (hg : g.cod = g.dom) {w w' : List I}
    (hw : w = l ++ g.dom ++ m ++ h.dom ++ v) (hw' : w' = l ++ g.dom ++ m ++ h.cod ++ v)
    {p q : ℕ} (hp : l.length = p) (hq : (l ++ g.dom ++ m).length = q)
    (hσ : SChain w (pl w [PG.ofShape h q]) w') :
    genE D Sc w (PG.ofShape g p) ≫ cl D Sc w w' [PG.ofShape h q] hσ =
      zsign k (g.parity D * h.parity D) •
        (cl D Sc w w' [PG.ofShape h q] hσ ≫ genE D Sc w' (PG.ofShape g p)) := by
  subst hw hw' hp hq
  have h₁ := sChain_ofShape l (m ++ h.dom ++ v) g hg (t := l ++ g.dom ++ m ++ h.dom ++ v)
    (by simp)
  have h₂ := sChain_ofShape l (m ++ h.cod ++ v) g hg (t := l ++ g.dom ++ m ++ h.cod ++ v)
    (by simp)
  rw [genE_eq D Sc h₁, genE_eq D Sc h₂, cl_comp', cl_comp']
  cases g with
  | dot x => exact cl_interchange D Sc l m v _ _ _ _
  | cross x x' =>
    obtain rfl : x = x' := by simp [Shape.cod, Shape.dom] at hg; exact hg.2
    exact cl_interchange D Sc l m v _ _ _ _

theorem eq_zsign_smul_iff {M : Type*} [AddCommGroup M] [Module k M] (p : ZMod 2) (x y : M) :
    x = zsign k p • y ↔ y = zsign k p • x := by
  constructor <;> rintro rfl <;> rw [smul_smul, zsign_mul_self, one_smul]

/-- A generator `g` that does not change the word, to the right of a generator `h`, moves
through `h` by the super interchange law. -/
theorem genE_comp_cl' (l m v : List I) (h g : Shape I) (hg : g.cod = g.dom) {w w' : List I}
    (hw : w = l ++ h.dom ++ m ++ g.dom ++ v) (hw' : w' = l ++ h.cod ++ m ++ g.dom ++ v)
    {p q : ℕ} (hq : l.length = q) (hp : (l ++ h.dom ++ m).length = p)
    (hp' : (l ++ h.cod ++ m).length = p) (hσ : SChain w (pl w [PG.ofShape h q]) w') :
    genE D Sc w (PG.ofShape g p) ≫ cl D Sc w w' [PG.ofShape h q] hσ =
      zsign k (h.parity D * g.parity D) •
        (cl D Sc w w' [PG.ofShape h q] hσ ≫ genE D Sc w' (PG.ofShape g p)) := by
  subst hw hw' hq hp
  have h₁ := sChain_ofShape (l ++ h.dom ++ m) v g hg (t := l ++ h.dom ++ m ++ g.dom ++ v) rfl
  have h₂ := sChain_ofShape' (l ++ h.cod ++ m) v g (t := l ++ h.cod ++ m ++ g.dom ++ v)
    (t' := l ++ h.cod ++ m ++ g.dom ++ v) rfl (by rw [hg]) hp'
  rw [genE_eq D Sc h₁, genE_eq D Sc h₂, cl_comp', cl_comp']
  rw [eq_zsign_smul_iff]
  cases g with
  | dot x => exact cl_interchange D Sc l m v _ _ _ _
  | cross x x' =>
    obtain rfl : x = x' := by simp [Shape.cod, Shape.dom] at hg; exact hg.2
    exact cl_interchange D Sc l m v _ _ _ _

end OddMath.QuiverHecke
