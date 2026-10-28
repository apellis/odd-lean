/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Matrices
import OddMath.SKM.RouquierHomPostPowers

/-! # The image of the upward dot in the swapped action

The image of the generator `x : Eᵢ → Eᵢ` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, in the swapped Hom construction of
`docs/Nondegeneracy/SwappedActionAssembly.md`, §1: it is diagonal in the summand of the strand,
with

* on the probe summand `A` (precomposition by `Eᵢ`), the inherited dot `T.dot i _ ▷ Z`;
* on the reservoir summand `B` (content-shifted postcomposition by `Eᵢ`), the shifted
  postcomposition dot `homContentPostDot` at the probe content of the sector on the left.

`oneLetterDiag` builds the entries of a one-letter generator from its diagonal components;
the entry between paths through different summands is zero. The statement is for paths with
possibly different right sectors `s`, `s'` related by `hs : s = s'`, so that the defining
equations are by pattern matching; `dotImage` specializes it to `hs = rfl`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The entries of a one-letter generator with the given diagonal components (zero between
different summands), for paths whose right sectors are related by `hs`. -/
def oneLetterDiag (l : Letter I) (r : X)
    (f : ∀ (side : Bool) (t : Sector I) (hv : StepValid l side t)
      (Z : P.H (nextSector l side t)), End ((P.step l side t hv).obj Z)) :
    ∀ {t s s' : Sector I} (_p : SPath [⟨l, r⟩] t s) (_p' : SPath [⟨l, r⟩] t s')
      (hs : s = s') (Z : P.H s'), (P.pathFunctor _p).obj (hs ▸ Z) ⟶ (P.pathFunctor _p').obj Z
  | _, _, _, .cons _ σ _ hv (.nil _), .cons _ τ _ _ (.nil _), _, Z =>
    if h : σ = τ then by subst h; exact f σ _ hv Z else 0

theorem oneLetterDiag_self (l : Letter I) (r : X)
    (f : ∀ (side : Bool) (t : Sector I) (hv : StepValid l side t)
      (Z : P.H (nextSector l side t)), End ((P.step l side t hv).obj Z))
    (side : Bool) (t : Sector I) (hv hv' : StepValid l side t)
    (Z : P.H (nextSector l side t)) :
    P.oneLetterDiag l r f (.cons ⟨l, r⟩ side t hv (.nil _)) (.cons ⟨l, r⟩ side t hv' (.nil _))
      rfl Z = f side t hv Z := by
  simp [oneLetterDiag]

/-- The diagonal components of the dot: the inherited dot on the probe summand and the
shifted postcomposition dot on the reservoir summand. -/
def dotDiag (i : I) : ∀ (side : Bool) (t : Sector I) (hv : StepValid (true, i) side t)
    (Z : P.H (nextSector (true, i) side t)), End ((P.step (true, i) side t hv).obj Z)
  | true, _, _, Z => P.T.dot i _ ▷ Z
  | false, t, _, Z => homContentPostDot P.T.obj P.W i t.1 (P.muP t) _ Z

/-- **The image of the upward dot.** -/
def dotImage (i : I) (ν : X) : P.GenImage (.dot i) ν := fun p p' Z =>
  P.oneLetterDiag (true, i) _ (P.dotDiag i) p p' rfl Z

/-- The dot on the probe summand is the inherited dot. -/
@[simp] theorem dotImage_probe (i : I) (ν : X) (t : Sector I)
    (hv hv' : StepValid (true, i) true t) (Z : P.H (nextSector (true, i) true t)) :
    P.dotImage i ν (.cons _ true t hv (.nil _)) (.cons _ true t hv' (.nil _)) Z =
      P.T.dot i _ ▷ Z :=
  P.oneLetterDiag_self _ _ _ true t hv hv' Z

/-- The dot on the reservoir summand is the shifted postcomposition dot. -/
@[simp] theorem dotImage_reservoir (i : I) (ν : X) (t : Sector I)
    (hv hv' : StepValid (true, i) false t) (Z : P.H (nextSector (true, i) false t)) :
    P.dotImage i ν (.cons _ false t hv (.nil _)) (.cons _ false t hv' (.nil _)) Z =
      homContentPostDot P.T.obj P.W i t.1 (P.muP t) _ Z :=
  P.oneLetterDiag_self _ _ _ false t hv hv' Z

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
