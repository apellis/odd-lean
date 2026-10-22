/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Presentation

/-!
# Diagrams of the quiver Hecke supercategory by positions

A diagram in `H` with bottom word `t` is determined by the positions of its generators: a dot on
strand `p`, or a crossing of strands `a` and `a + 1` (`PG`); the colours are read off the word
at that height. `pl t gs` is the list of layers of the generators `gs` (bottom first) on the
word `t`; a generator at a position outside the word is dropped, so `pl t gs` is always a
composable chain from `t` to `tgt t gs` (`sChain_pl`). Every composable chain is of this form
(`exists_pl`).

`cl t t' gs h` is the class of the diagram in the presented category, and composites are
concatenations (`cl_append`). These are the words used for the straightening argument of the
basis theorem of `H_n` (Brundan–Ellis, arXiv:1701.04133v2, §11; Kang–Kashiwara–Tsuchioka,
arXiv:1107.1039v2, Corollary 3.15).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u}

/-- A generator at a position: a dot on strand `p`, or a crossing of strands `a`, `a + 1`. -/
inductive PG
  | dot (p : ℕ)
  | cross (a : ℕ)
  deriving DecidableEq

namespace PG

/-- The word above the generator. -/
def act : PG → List I → List I
  | dot _, t => t
  | cross a, t => match t.drop a with
    | x :: y :: r => t.take a ++ y :: x :: r
    | _ => t

/-- The layer of the generator on the word `t`, or nothing if it does not fit. -/
def ld : PG → List I → List (LayerData I)
  | dot p, t => match t.drop p with
    | x :: r => [(t.take p, Shape.dot x, r)]
    | [] => []
  | cross a, t => match t.drop a with
    | x :: y :: r => [(t.take a, Shape.cross x y, r)]
    | _ => []

/-- The number of crossings (`0` or `1`) of the generator. -/
def isCross : PG → ℕ
  | dot _ => 0
  | cross _ => 1

theorem sChain_ld (g : PG) (t : List I) : SChain t (g.ld t) (g.act t) := by
  cases g with
  | dot p =>
    simp only [ld, act]
    split
    · next x r h =>
      have e : t = List.take p t ++ [x] ++ r := by
        conv_lhs => rw [← List.take_append_drop p t, h]
        simp
      exact ⟨e, e.symm⟩
    · rfl
  | cross a =>
    simp only [ld, act]
    split
    · next x y r h =>
      refine ⟨?_, ?_⟩
      · simp only [Shape.dom]
        conv_lhs => rw [← List.take_append_drop a t, h]
        simp
      · simp [Shape.cod]
    · rfl

end PG

/-- The layers of a list of positioned generators, bottom first. -/
def pl : List I → List PG → List (LayerData I)
  | _, [] => []
  | t, g :: gs => g.ld t ++ pl (g.act t) gs

/-- The word at the top. -/
def tgt : List I → List PG → List I
  | t, [] => t
  | t, g :: gs => tgt (g.act t) gs

theorem sChain_pl (t : List I) (gs : List PG) : SChain t (pl t gs) (tgt t gs) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => exact (g.sChain_ld t).append (ih _)

@[simp] theorem pl_nil (t : List I) : pl t [] = [] := rfl
@[simp] theorem pl_cons (t : List I) (g : PG) (gs : List PG) :
    pl t (g :: gs) = g.ld t ++ pl (g.act t) gs := rfl
@[simp] theorem tgt_nil (t : List I) : tgt t [] = t := rfl
@[simp] theorem tgt_cons (t : List I) (g : PG) (gs : List PG) :
    tgt t (g :: gs) = tgt (g.act t) gs := rfl

theorem pl_append (t : List I) (gs hs : List PG) :
    pl t (gs ++ hs) = pl t gs ++ pl (tgt t gs) hs := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => simp [ih]

theorem tgt_append (t : List I) (gs hs : List PG) :
    tgt t (gs ++ hs) = tgt (tgt t gs) hs := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => simp [ih]

theorem sChain_target {t t' t'' : List I} {ls : List (LayerData I)} (h : SChain t ls t')
    (h' : SChain t ls t'') : t' = t'' := by
  induction ls generalizing t with
  | nil => exact h.symm.trans h'
  | cons x ls ih => exact ih h.2 h'.2

theorem tgt_eq {t t' : List I} {gs : List PG} (h : SChain t (pl t gs) t') : tgt t gs = t' :=
  sChain_target (sChain_pl t gs) h

/-- The positioned generator of a layer. -/
def LayerData.pg (x : LayerData I) : PG :=
  match x.2.1 with
  | .dot _ => .dot x.1.length
  | .cross _ _ => .cross x.1.length

theorem ld_pg {t : List I} {x : LayerData I} (h : t = x.1 ++ x.2.1.dom ++ x.2.2) :
    (LayerData.pg x).ld t = [x] ∧ (LayerData.pg x).act t = x.1 ++ x.2.1.cod ++ x.2.2 := by
  obtain ⟨l, g, r⟩ := x
  subst h
  cases g with
  | dot i => simp [LayerData.pg, PG.ld, PG.act, Shape.dom, Shape.cod]
  | cross i j => simp [LayerData.pg, PG.ld, PG.act, Shape.dom, Shape.cod]

/-- Every composable chain of layers is the chain of its positioned generators. -/
theorem exists_pl {t t' : List I} {ls : List (LayerData I)} (h : SChain t ls t') :
    pl t (ls.map LayerData.pg) = ls := by
  induction ls generalizing t with
  | nil => rfl
  | cons x ls ih =>
    obtain ⟨h₁, h₂⟩ := (ld_pg h.1)
    rw [List.map_cons, pl_cons, h₁, h₂, ih h.2]
    rfl

/-- The number of crossings of a list of positioned generators. -/
def crossCount (gs : List PG) : ℕ := (gs.map PG.isCross).sum

@[simp] theorem crossCount_nil : crossCount [] = 0 := rfl
@[simp] theorem crossCount_cons (g : PG) (gs : List PG) :
    crossCount (g :: gs) = g.isCross + crossCount gs := by simp [crossCount]
@[simp] theorem crossCount_append (gs hs : List PG) :
    crossCount (gs ++ hs) = crossCount gs + crossCount hs := by simp [crossCount]

/-! ## Classes in the presented category -/

variable {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The class of the diagram of `gs` on `t`, with its top word given as `t'`. -/
def cl (t t' : List I) (gs : List PG) (h : SChain t (pl t gs) t') :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') :=
  (pres D Sc).diag (mkD D (pl t gs) h)

theorem cl_append {t t' : List I} (gs hs : List PG) (h : SChain t (pl t (gs ++ hs)) t') :
    cl D Sc t t' (gs ++ hs) h =
      cl D Sc t (tgt t gs) gs (sChain_pl t gs) ≫
        cl D Sc (tgt t gs) t' hs (by
          have := sChain_pl (tgt t gs) hs
          rwa [← tgt_eq (h := h), tgt_append]) := by
  rw [cl, cl, cl, ← Presentation.diag_comp]
  apply Presentation.diag_eq_of_layers_eq
  simp [mkD, layList, pl_append]

theorem cl_congr {t t' : List I} {gs hs : List PG} (h : SChain t (pl t gs) t')
    (h' : SChain t (pl t hs) t') (e : pl t gs = pl t hs) :
    cl D Sc t t' gs h = cl D Sc t t' hs h' := by
  apply Presentation.diag_eq_of_layers_eq
  simp [mkD, layList, e]

end OddMath.QuiverHecke
