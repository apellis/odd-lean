/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Positional
import StringDiagrams.Positional

/-!
# The relations of `H` at a position

The defining relations (1.7)–(1.9) of the quiver Hecke supercategory (Brundan–Ellis,
arXiv:1701.04133v2, §11), whiskered to an arbitrary position of a word and written with
positioned generators (`PG`), in the form used by the straightening argument: each says that
a word of generators agrees, up to a sign and up to words with fewer crossings, with another.

`Filt t t' n` is the span of the classes of words with at most `n` crossings from `t` to `t'`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LinDiagram
open SKM (zsign)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

@[simp] theorem drop_length_add {α : Type*} (l : List α) (n : ℕ) : l.drop (l.length + n) = [] :=
  List.drop_eq_nil_of_le (by omega)

@[simp] theorem take_length_add {α : Type*} (l : List α) (n : ℕ) : l.take (l.length + n) = l :=
  List.take_of_length_le (by omega)

/-- Whiskering of layer data by `l` on the left and `r` on the right. -/
def wh (l r : List I) (x : LayerData I) : LayerData I := (l ++ x.1, x.2.1, x.2.2 ++ r)

theorem sChain_wh {t t' : List I} {ls : List (LayerData I)} (h : SChain t ls t') (l r : List I) :
    SChain (l ++ t ++ r) (ls.map (wh l r)) (l ++ t' ++ r) := by
  induction ls generalizing t with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    exact ⟨by simp [wh], by simpa [wh] using ih h⟩

theorem lin_whisker_dg (l r : List I) {t t' : List I} (ls : List (LayerData I))
    (h : SChain t ls t') :
    (pres D Sc).lin (LinDiagram.whisker (dg (k := k) D ls h) (ob D l) r
        (Obj.whiskerOK_of_subsingleton _ _ _)) =
      (pres D Sc).diag (mkD D (ls.map (wh l r)) (sChain_wh h l r)) := by
  rw [dg, whisker_of, Presentation.lin_of]
  apply Presentation.diag_eq_of_layers_eq
  simp [layList, lay, Layer.whisker, wh, ob]

theorem lin_whisker_idg (l r t : List I) :
    (pres D Sc).lin (LinDiagram.whisker (idg (k := k) D t) (ob D l) r
        (Obj.whiskerOK_of_subsingleton _ _ _)) =
      (pres D Sc).diag (mkD D [] (show SChain (l ++ t ++ r) [] (l ++ t ++ r) from rfl)) := by
  rw [idg, whisker_of, Presentation.lin_of]
  apply Presentation.diag_eq_of_layers_eq
  rfl

/-- The span of the classes of words from `t` to `t'` with at most `n` crossings. -/
def Filt (t t' : List I) (n : ℕ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ gs h, crossCount gs ≤ n ∧ cl D Sc t t' gs h = f}

theorem cl_mem_filt {t t' : List I} {gs : List PG} (h : SChain t (pl t gs) t') {n : ℕ}
    (hn : crossCount gs ≤ n) : cl D Sc t t' gs h ∈ Filt D Sc t t' n :=
  Submodule.subset_span ⟨gs, h, hn, rfl⟩

theorem filt_mono {t t' : List I} {m n : ℕ} (h : m ≤ n) :
    Filt D Sc t t' m ≤ Filt D Sc t t' n :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, e⟩ => ⟨gs, hg, hc.trans h, e⟩

/-- The class of a whiskered normal-form list, as a positioned word. -/
theorem diag_mkD_eq_cl {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t')
    (gs : List PG) (e : pl t gs = ls) :
    (pres D Sc).diag (mkD D ls h) = cl D Sc t t' gs (e ▸ h) := by
  subst e; rfl

/-! ## The relations, positioned -/

section Rels

variable (l r : List I)

theorem pl_cross_cross (i j : I) :
    pl (l ++ [i, j] ++ r) [.cross l.length, .cross l.length] =
      (crossL [] i j [] ++ crossL [] j i []).map (wh l r) := by
  simp [pl, PG.ld, PG.act, crossL, wh]

theorem sChain_cross_cross (i j : I) :
    SChain [i, j] (crossL [] i j [] ++ crossL [] j i []) [i, j] := by
  simp [crossL, Shape.dom, Shape.cod]

theorem tgt_dots (t : List I) (p n : ℕ) : tgt t (List.replicate n (.dot p)) = t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, tgt_cons]; exact ih

theorem pl_dots_left (i j : I) (n : ℕ) :
    pl (l ++ [i, j] ++ r) (List.replicate n (.dot l.length)) = (dotsL [] i [j] n).map (wh l r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, pl_cons,
      show (PG.dot l.length).act (l ++ [i, j] ++ r) = l ++ [i, j] ++ r from rfl, ih]
    simp [PG.ld, dotsL, wh, List.replicate_succ]

theorem pl_dots_right (i j : I) (n : ℕ) :
    pl (l ++ [i, j] ++ r) (List.replicate n (.dot (l.length + 1))) =
      (dotsL [i] j [] n).map (wh l r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, pl_cons,
      show (PG.dot (l.length + 1)).act (l ++ [i, j] ++ r) = l ++ [i, j] ++ r from rfl, ih]
    simp [PG.ld, dotsL, wh, List.replicate_succ, List.take_append]

theorem pl_dotsL (u v : List I) (i : I) (n : ℕ) :
    pl (l ++ (u ++ [i] ++ v) ++ r) (List.replicate n (.dot (l.length + u.length))) =
      (dotsL u i v n).map (wh l r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, pl_cons,
      show (PG.dot (l.length + u.length)).act (l ++ (u ++ [i] ++ v) ++ r) =
        l ++ (u ++ [i] ++ v) ++ r from rfl, ih]
    simp [PG.ld, dotsL, wh, List.replicate_succ, List.take_append, List.drop_append]

theorem cl_eq_diag {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t')
    (ls : List (LayerData I)) (h' : SChain t ls t') (e : pl t gs = ls) :
    cl D Sc t t' gs h = (pres D Sc).diag (mkD D ls h') :=
  Presentation.diag_eq_of_layers_eq _ (by simp [mkD, layList, e])

/-- A whiskered word diagram with layers of a positioned word lies in the filtration. -/
theorem lin_whisker_dg_mem {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t')
    (gs : List PG) (e : pl (l ++ t ++ r) gs = ls.map (wh l r)) {n : ℕ} (hn : crossCount gs ≤ n) :
    (pres D Sc).lin (LinDiagram.whisker (dg (k := k) D ls h) (ob D l) r
        (Obj.whiskerOK_of_subsingleton _ _ _)) ∈ Filt D Sc (l ++ t ++ r) (l ++ t' ++ r) n := by
  rw [lin_whisker_dg, ← cl_eq_diag D Sc gs (e ▸ sChain_wh h l r) _ _ e]
  exact cl_mem_filt D Sc _ hn

theorem lin_whisker_idg_mem (t : List I) :
    (pres D Sc).lin (LinDiagram.whisker (idg (k := k) D t) (ob D l) r
        (Obj.whiskerOK_of_subsingleton _ _ _)) ∈ Filt D Sc (l ++ t ++ r) (l ++ t ++ r) 0 := by
  rw [lin_whisker_idg]
  exact cl_mem_filt D Sc (t := l ++ t ++ r) (gs := []) rfl le_rfl

theorem lin_whisker_sum {a b : Obj (sig D)} {ι : Type*} (s : Finset ι)
    (f : ι → LinDiagram k a b) :
    (pres D Sc).lin (LinDiagram.whisker (∑ x ∈ s, f x) (ob D l) r
        (Obj.whiskerOK_of_subsingleton _ _ _)) =
      ∑ x ∈ s, (pres D Sc).lin (LinDiagram.whisker (f x) (ob D l) r
        (Obj.whiskerOK_of_subsingleton _ _ _)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, whisker_add,
      Presentation.lin_add, ih]

/-- (1.7): two crossings at the same position give words without crossings. -/
theorem cross_cross_mem (i j : I)
    (h : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length, .cross l.length]) (l ++ [i, j] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross l.length] h ∈ Filt D Sc _ _ 0 := by
  have hw := Obj.whiskerOK_of_subsingleton (ob D [i, j]) (ob D l) r
  rw [cl_eq_diag D Sc _ h _ (sChain_wh (sChain_cross_cross i j) l r)
    (pl_cross_cross l r i j), ← lin_whisker_dg D Sc l r _ (sChain_cross_cross i j)]
  by_cases hij : i = j
  · subst hij
    have hr := (pres D Sc).lin_rel (Rel.quadEq i) (ob D l) r hw
    change (pres D Sc).lin (LinDiagram.whisker (relation D Sc (Rel.quadEq i)) _ _ _) = 0 at hr
    simp only [relation] at hr
    rw [hr]; exact Submodule.zero_mem _
  by_cases hd : D.d i j = 0
  · have hr := (pres D Sc).lin_rel (Rel.quadZero i j hij hd) (ob D l) r hw
    change (pres D Sc).lin (LinDiagram.whisker (relation D Sc (Rel.quadZero i j hij hd)) _ _ _)
      = 0 at hr
    simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
      Presentation.lin_smul, sub_eq_zero] at hr
    rw [hr]
    exact Submodule.smul_mem _ _ (lin_whisker_idg_mem D Sc l r _)
  · have hr := (pres D Sc).lin_rel (Rel.quadNe i j hij hd) (ob D l) r hw
    change (pres D Sc).lin (LinDiagram.whisker (relation D Sc (Rel.quadNe i j hij hd)) _ _ _)
      = 0 at hr
    simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
      Presentation.lin_smul, lin_whisker_sum, sub_eq_zero] at hr
    rw [sub_sub, sub_eq_iff_eq_add] at hr
    rw [hr]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ ?_) (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_))
    · refine lin_whisker_dg_mem D Sc l r _ _
        (List.replicate q (.dot (l.length + 1)) ++ List.replicate p (.dot l.length)) ?_
        (by simp [crossCount, PG.isCross])
      rw [pl_append, tgt_dots, List.map_append, pl_dots_left, pl_dots_right]
    · exact lin_whisker_dg_mem D Sc l r _ _ _ (pl_dots_left l r i j _)
        (by simp [crossCount, PG.isCross])
    · exact lin_whisker_dg_mem D Sc l r _ _ _ (pl_dots_right l r i j _)
        (by simp [crossCount, PG.isCross])

theorem cl_eq_lin {t t' : List I} (ls : List (LayerData I)) (p : SChain t ls t') (gs : List PG)
    (h : SChain (l ++ t ++ r) (pl _ gs) (l ++ t' ++ r)) (e : pl (l ++ t ++ r) gs = ls.map (wh l r)) :
    cl D Sc _ _ gs h = (pres D Sc).lin (LinDiagram.whisker (dg (k := k) D ls p) (ob D l) r
        (Obj.whiskerOK_of_subsingleton _ _ _)) := by
  rw [lin_whisker_dg]; exact cl_eq_diag D Sc gs h _ _ e

theorem lin_rel_eq (q : Rel D) :
    (pres D Sc).lin (LinDiagram.whisker (relation D Sc q) (ob D l) r
      (Obj.whiskerOK_of_subsingleton _ _ _)) = 0 :=
  (pres D Sc).lin_rel q (ob D l) r _

/-- (1.8), left: a dot below a crossing on its left strand moves above it, on its right
strand, up to the sign `(-1)^{|i||j|}` and a word without crossings. -/
theorem slide_left (i j : I)
    (h₁ : SChain (l ++ [i, j] ++ r) (pl _ [.dot l.length, .cross l.length]) (l ++ [j, i] ++ r))
    (h₂ : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length, .dot (l.length + 1)])
      (l ++ [j, i] ++ r)) :
    cl D Sc _ _ [.dot l.length, .cross l.length] h₁ -
        zsign k (D.parity i * D.parity j) • cl D Sc _ _ [.cross l.length, .dot (l.length + 1)] h₂ ∈
      Filt D Sc _ _ 0 := by
  have p₁ : SChain [i, j] (dotsL [] i [j] 1 ++ crossL [] i j []) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, j] (crossL [] i j [] ++ dotsL [j] i [] 1) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  by_cases hij : i = j
  · subst hij
    have hr := lin_rel_eq D Sc l r (Rel.slideLEq i)
    simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
      Presentation.lin_smul, sub_eq_zero] at hr
    rw [hr]
    exact lin_whisker_idg_mem D Sc l r _
  · have hr := lin_rel_eq D Sc l r (Rel.slideL i j hij)
    simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
      Presentation.lin_smul] at hr
    rw [hr]
    exact Submodule.zero_mem _

/-- (1.8), right: a dot above a crossing on its left strand moves below it, on its right
strand, up to the sign `(-1)^{|i||j|}` and a word without crossings. -/
theorem slide_right (i j : I)
    (h₁ : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length, .dot l.length]) (l ++ [j, i] ++ r))
    (h₂ : SChain (l ++ [i, j] ++ r) (pl _ [.dot (l.length + 1), .cross l.length])
      (l ++ [j, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .dot l.length] h₁ -
        zsign k (D.parity i * D.parity j) • cl D Sc _ _ [.dot (l.length + 1), .cross l.length] h₂ ∈
      Filt D Sc _ _ 0 := by
  have p₁ : SChain [i, j] (crossL [] i j [] ++ dotsL [] j [i] 1) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, j] (dotsL [i] j [] 1 ++ crossL [] i j []) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  by_cases hij : i = j
  · subst hij
    have hr := lin_rel_eq D Sc l r (Rel.slideREq i)
    simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
      Presentation.lin_smul, sub_eq_zero] at hr
    rw [hr]
    exact lin_whisker_idg_mem D Sc l r _
  · have hr := lin_rel_eq D Sc l r (Rel.slideR i j hij)
    simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
      Presentation.lin_smul] at hr
    rw [hr]
    exact Submodule.zero_mem _

/-- (1.9): the two sides of the braid relation agree up to words without crossings. -/
theorem braid_mem (i j m : I)
    (h₁ : SChain (l ++ [i, j, m] ++ r)
      (pl _ [.cross l.length, .cross (l.length + 1), .cross l.length]) (l ++ [m, j, i] ++ r))
    (h₂ : SChain (l ++ [i, j, m] ++ r)
      (pl _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)])
      (l ++ [m, j, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross (l.length + 1), .cross l.length] h₁ -
        cl D Sc _ _ [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)] h₂ ∈
      Filt D Sc _ _ 0 := by
  have p₁ : SChain [i, j, m] (crossL [] i j [m] ++ crossL [j] i m [] ++ crossL [] j m [i])
      [m, j, i] := by simp [crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, j, m] (crossL [i] j m [] ++ crossL [] i m [j] ++ crossL [m] i j [])
      [m, j, i] := by simp [crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append]),
    cl_eq_lin D Sc l r _ p₂ _ h₂
      (by simp [pl, PG.ld, PG.act, crossL, wh, List.take_append, List.drop_append])]
  by_cases hb : i = m ∧ i ≠ j
  · obtain ⟨rfl, hij⟩ := hb
    have hr := lin_rel_eq D Sc l r (Rel.braidEq i j hij)
    simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
      Presentation.lin_smul, lin_whisker_sum] at hr
    rw [sub_sub, sub_eq_zero] at hr
    rw [hr]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => Submodule.sum_mem _
        fun x _ => Submodule.smul_mem _ _ ?_)
    · refine lin_whisker_dg_mem D Sc l r _ _ (List.replicate x (.dot (l.length + 2)) ++
        List.replicate (D.dn i j - 1 - x) (.dot l.length)) ?_ (by simp [crossCount, PG.isCross])
      rw [pl_append, tgt_dots, List.map_append]
      exact congrArg₂ (· ++ ·) (pl_dotsL l r [i, j] [] i x) (pl_dotsL l r [] [j, i] i _)
    · refine lin_whisker_dg_mem D Sc l r _ _ (List.replicate x (.dot (l.length + 2)) ++
        List.replicate q (.dot (l.length + 1)) ++
        List.replicate (p - 1 - x) (.dot l.length)) ?_ (by simp [crossCount, PG.isCross])
      rw [pl_append, pl_append, tgt_append, tgt_dots, tgt_dots, List.map_append,
        List.map_append]
      exact congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (pl_dotsL l r [i, j] [] i x)
        (pl_dotsL l r [i] [i] j q)) (pl_dotsL l r [] [j, i] i _)
  · have hr := lin_rel_eq D Sc l r (Rel.braid i j m hb)
    simp only [relation, whisker_sub, Presentation.lin_sub] at hr
    rw [hr]
    exact Submodule.zero_mem _

end Rels

/-! ## Far commutation -/

/-- The positioned generator of a shape at position `p`. -/
def PG.ofShape (g : Shape I) (p : ℕ) : PG :=
  match g with
  | .dot _ => .dot p
  | .cross _ _ => .cross p

theorem pl_ofShape (l r : List I) (g : Shape I) :
    pl (l ++ g.dom ++ r) [PG.ofShape g l.length] = [(l, g, r)] := by
  cases g <;> simp [PG.ofShape, pl, PG.ld, Shape.dom]

theorem act_ofShape (l r : List I) (g : Shape I) :
    (PG.ofShape g l.length).act (l ++ g.dom ++ r) = l ++ g.cod ++ r := by
  cases g <;> simp [PG.ofShape, PG.act, Shape.dom, Shape.cod]

theorem zsign_parity_mul (g h : Shape I) :
    zsign k (g.parity D * h.parity D) =
      (((if (sig D).odd g && (sig D).odd h then -1 else 1 : ℤ)) : k) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  simp only [sig, zsign]
  rcases hz (g.parity D) with ha | ha <;> rcases hz (h.parity D) with hb | hb <;> simp [ha, hb]

/-- The super interchange law for generators `g` (left) and `h` (right) at disjoint
positions. -/
theorem cl_interchange (l m v : List I) (g h : Shape I)
    (h₁ : SChain (l ++ g.dom ++ m ++ h.dom ++ v)
      (pl _ [PG.ofShape g l.length, PG.ofShape h (l ++ g.dom ++ m).length])
      (l ++ g.cod ++ m ++ h.cod ++ v))
    (h₂ : SChain (l ++ g.dom ++ m ++ h.dom ++ v)
      (pl _ [PG.ofShape h (l ++ g.dom ++ m).length, PG.ofShape g l.length])
      (l ++ g.cod ++ m ++ h.cod ++ v)) :
    cl D Sc _ _ [PG.ofShape g l.length, PG.ofShape h (l ++ g.dom ++ m).length] h₁ =
      zsign k (g.parity D * h.parity D) •
        cl D Sc _ _ [PG.ofShape h (l ++ g.dom ++ m).length, PG.ofShape g l.length] h₂ := by
  have e₁ : pl (l ++ g.dom ++ m ++ h.dom ++ v)
      [PG.ofShape g l.length, PG.ofShape h (l ++ g.dom ++ m).length] =
        [(l, g, m ++ h.dom ++ v), (l ++ g.cod ++ m, h, v)] := by
    cases g <;> cases h <;>
      simp [pl, PG.ld, PG.act, PG.ofShape, Shape.dom, Shape.cod, List.take_append,
        List.drop_append]
  have e₂ : pl (l ++ g.dom ++ m ++ h.dom ++ v)
      [PG.ofShape h (l ++ g.dom ++ m).length, PG.ofShape g l.length] =
        [(l ++ g.dom ++ m, h, v), (l, g, m ++ h.cod ++ v)] := by
    cases g <;> cases h <;>
      simp [pl, PG.ld, PG.act, PG.ofShape, Shape.dom, Shape.cod, List.take_append,
        List.drop_append]
  rw [cl, cl, zsign_parity_mul]
  exact (pres D Sc).diag_interchange_of_layers () l m v g h _ _
    (by simp only [layers_mkD, layList, e₁]; rfl) (by simp only [layers_mkD, layList, e₂]; rfl)



end OddMath.QuiverHecke