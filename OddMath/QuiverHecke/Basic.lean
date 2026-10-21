/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Grading

/-!
# The quiver Hecke signature

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11,
the definition preceding (11.1). Objects are words in `I`; the only generators
are dots and upward crossings. There are no region weights, cups or caps.
We reuse the Cartan data, parameters and symmetrizer of `SKM`.

Words are ordered from left to right and composition from bottom to top.
Thus the paper's strand positions run in the opposite order to list indices.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)

/-- The two types of generators of the quiver Hecke supercategory. -/
inductive Shape (I : Type u)
  | dot (i : I)
  | cross (i j : I)

namespace Shape
/-- Bottom boundary, in left-to-right order. -/
def dom : Shape I → List I
  | .dot i => [i]
  | .cross i j => [i, j]
/-- Top boundary. -/
def cod : Shape I → List I
  | .dot i => [i]
  | .cross i j => [j, i]
/-- Generator parity, as in BE2 §11. -/
def parity : Shape I → ZMod 2
  | .dot i => D.parity i
  | .cross i j => D.parity i * D.parity j
/-- The corresponding upward generator in the SKM signature. -/
def toSKM : Shape I → SKM.Shape I
  | .dot i => .dot i
  | .cross i j => .cross i j
end Shape

/-- Weight-free quiver Hecke signature. -/
def sig : Signature where
  Region := Unit
  Colour := I
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Shape I
  dom := Shape.dom
  cod := Shape.cod
  left _ := ()
  right _ := ()
  odd g := decide (g.parity D = 1)

instance : Subsingleton (sig D).Region := inferInstanceAs (Subsingleton Unit)
instance : Inhabited (sig D).Region := inferInstanceAs (Inhabited Unit)

/-- The object corresponding to a word of colours. -/
def ob (t : List I) : Obj (sig D) := ⟨(), t⟩
/-- A contextual generator. -/
def lay (u : List I) (g : Shape I) (v : List I) : Layer (sig D) := ⟨(), u, g, v⟩
/-- A layer specified by its left context, generator, and right context. -/
abbrev LayerData (I : Type u) := List I × Shape I × List I
/-- Composability of a list of contextual generators. -/
def SChain : List I → List (LayerData I) → List I → Prop
  | t, [], t' => t = t'
  | t, x :: ls, t' => t = x.1 ++ x.2.1.dom ++ x.2.2 ∧
      SChain (x.1 ++ x.2.1.cod ++ x.2.2) ls t'

@[simp] theorem sChain_nil (t t' : List I) : SChain t [] t' ↔ t = t' := Iff.rfl
@[simp] theorem sChain_cons (t t' : List I) (x : LayerData I) (ls : List (LayerData I)) :
    SChain t (x :: ls) t' ↔ t = x.1 ++ x.2.1.dom ++ x.2.2 ∧
      SChain (x.1 ++ x.2.1.cod ++ x.2.2) ls t' := Iff.rfl

theorem SChain.append {t t' t'' : List I} {ls ms : List (LayerData I)}
    (h₁ : SChain t ls t') (h₂ : SChain t' ms t'') : SChain t (ls ++ ms) t'' := by
  induction ls generalizing t with
  | nil => cases h₁; exact h₂
  | cons x ls ih => exact ⟨h₁.1, ih h₁.2⟩

theorem SChain.replicate (n : ℕ) (u : List I) (i : I) (v : List I) :
    SChain (u ++ [i] ++ v) (List.replicate n (u, Shape.dot i, v)) (u ++ [i] ++ v) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨rfl, ih⟩

/-- The layers of a word diagram. -/
def layList (ls : List (LayerData I)) : List (Layer (sig D)) :=
  ls.map fun x => lay D x.1 x.2.1 x.2.2

theorem SChain.chain {t t' : List I} {ls : List (LayerData I)} (h : SChain t ls t') :
    Chain (ob D t) (layList D ls) (ob D t') := by
  induction ls generalizing t with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    exact ⟨Layer.valid_of_subsingleton _, rfl, ih h⟩

/-- A free diagram on the weight-free signature. -/
def mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    ob D t ⟶ ob D t' := Diagram.mk (layList D ls) (h.chain D)

@[simp] theorem layers_mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    Diagram.layers (mkD D ls h) = layList D ls := rfl

theorem parityDeg_sig (g : (sig D).Gen) : Presentation.parityDeg (sig D) g = g.parity D := by
  show (if decide (g.parity D = 1) = true then (1 : ZMod 2) else 0) = g.parity D
  generalize g.parity D = p
  fin_cases p <;> rfl

theorem degree_parity_mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    Diagram.degree (Presentation.parityDeg (sig D)) (mkD D ls h) =
      (ls.map fun x => x.2.1.parity D).sum := by
  simp only [Diagram.degree, layers_mkD, layList, List.map_map]
  congr 1
  exact List.map_congr_left fun _ _ => parityDeg_sig D _

end OddMath.QuiverHecke
