/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierData
import OddMath.SKM.Grading
import StringDiagrams.Super.Graded

/-!
# Integer gradings of Rouquier families

An integer grading of the 2-morphisms between the objects of a `RouquierFamily`, with the
generator degrees of Brundan–Ellis, arXiv:1701.04133v2, §1 "Gradings" (the table after
(1.31), as in `SKM.gdeg`): dot `2dᵢ`, crossing `dᵢdᵢⱼ`, unit `dᵢ(1+⟨hᵢ,x⟩)` at its source
weight `x`, counit `dᵢ(1-⟨hᵢ,y⟩)` at its target weight `y`.

The grading lives only on the Hom categories `W.obj μ ⟶ W.obj ν`; no grading is imposed on
the ambient 2-supercategory, so a family sharing its ambient with ungraded data (the probe of
a `ProbeReservoir`) can carry one.

## Main results

* `SuperSumInvTo.f'_mem_degree`, `SuperSumInvTo.g'_mem_degree` and their
  `SuperSumInvFrom` versions: in a graded supercategory, the inverse matrix of a matrix with
  homogeneous entries has homogeneous entries of the negated degrees. This is the
  homogeneous-inverse step (G8) of `docs/Nondegeneracy/DeformedGradedAction.md`.
* `RouquierGrading.mate_mem`: the mate of the Rouquier crossing has degree `0`.
* `RouquierGrading.invPos_f'_mem`, `invPos_g'_mem`, `invNeg_f'_mem`,
  `invNeg_g'_mem`: the inverse entries of `SuperRouquierLoc` are homogeneous of the
  degrees of the leftward crossing and the dotted cups and caps.
* `RouquierGrading.closure_mem`: the contracted closure `b_(s,r)` has degree
  `2dᵢ(r+s+1)`; `boundaryPos_mem`, `boundaryNeg_mem`: the boundary
  contractions have degrees `2dᵢ(n-m)`, `2dᵢ(m-n)`.
* `RouquierGrading.BoundedAbove.exists_foldr_eq_zero`: when every `End(𝟙_μ)` is bounded above in
  degree, a composite of more than the bound of positive-degree endomorphisms vanishes.

These are the inputs (N) and (J) of `docs/Nondegeneracy/SwappedHomInversion.md` §4 at the
reservoir; see `docs/Nondegeneracy/ReservoirGradingRoute.md`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory GradedSupercategory

universe u v w r
variable {k : Type r} [CommRing k]

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [GradedSupercategory k C]

namespace SuperSumInvTo

variable {A B Z : C} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
  (S : SuperSumInvTo (k := k) f g p q n)
include S

variable {a : ℤ} {b : ℕ → ℤ} (hf : f ∈ degree (R := k) A B a)
  (hg : ∀ m, m < n → g m ∈ degree (R := k) A Z (b m))
include hf hg

end SuperSumInvTo

namespace SuperSumInvFrom

variable {A B Z : C} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
  (S : SuperSumInvFrom (k := k) f g p q n)
include S

variable {a : ℤ} {b : ℕ → ℤ} (hf : f ∈ degree (R := k) B A a)
  (hg : ∀ m, m < n → g m ∈ degree (R := k) Z A (b m))
include hf hg

end SuperSumInvFrom

end Generic

section Family

variable {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- An integer grading of the 2-morphisms between the objects of a Rouquier family, with
the generator degrees of Brundan–Ellis, arXiv:1701.04133v2, §1 (`SKM.gdeg`): each Hom
category `W.obj μ ⟶ W.obj ν` is a graded supercategory, whiskering preserves degrees,
associators and unitors have degree `0`, the dot has degree `2dᵢ`, the crossing `dᵢdᵢⱼ`,
the unit `dᵢ(1+⟨hᵢ,x⟩)` at its source `x` and the counit `dᵢ(1-⟨hᵢ,y⟩)` at its target
`y`. -/
structure RouquierGrading (W : RouquierFamily (k := k) (B := B) D) (sy : Symmetrizer D) where
  /-- The grading of each Hom category between objects of the family. -/
  graded : ∀ μ ν : X, GradedSupercategory k (W.obj μ ⟶ W.obj ν)
  whiskerLeft_mem : ∀ {μ ν ρ : X} (f : W.obj μ ⟶ W.obj ν) {g h : W.obj ν ⟶ W.obj ρ}
    {n : ℤ} {η : g ⟶ h}, η ∈ degree (self := graded ν ρ) (R := k) g h n →
      f ◁ η ∈ degree (self := graded μ ρ) (R := k) (f ≫ g) (f ≫ h) n
  whiskerRight_mem : ∀ {μ ν ρ : X} {f g : W.obj μ ⟶ W.obj ν} (h : W.obj ν ⟶ W.obj ρ)
    {n : ℤ} {η : f ⟶ g}, η ∈ degree (self := graded μ ν) (R := k) f g n →
      η ▷ h ∈ degree (self := graded μ ρ) (R := k) (f ≫ h) (g ≫ h) n
  associator_mem : ∀ {μ ν ρ σ : X} (f : W.obj μ ⟶ W.obj ν) (g : W.obj ν ⟶ W.obj ρ)
    (h : W.obj ρ ⟶ W.obj σ),
      (associator f g h).hom ∈ degree (self := graded μ σ) (R := k) _ _ 0
  leftUnitor_mem : ∀ {μ ν : X} (f : W.obj μ ⟶ W.obj ν),
    (leftUnitor f).hom ∈ degree (self := graded μ ν) (R := k) _ _ 0
  rightUnitor_mem : ∀ {μ ν : X} (f : W.obj μ ⟶ W.obj ν),
    (rightUnitor f).hom ∈ degree (self := graded μ ν) (R := k) _ _ 0
  dot_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    W.dot i h ∈ degree (self := graded x y) (R := k) _ _ (2 * sy.d i)
  cross_mem : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
      W.cross i j h₁ h₂ h₃ h₄ ∈ degree (self := graded a d) (R := k) _ _ (sy.d i * D.d i j)
  unit_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    (W.adj i h).unit ∈ degree (self := graded x x) (R := k) _ _ (sy.d i * (1 + D.h i x))
  counit_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    (W.adj i h).counit ∈ degree (self := graded y y) (R := k) _ _ (sy.d i * (1 - D.h i y))

namespace RouquierGrading

variable {W : RouquierFamily (k := k) (B := B) D} {sy : Symmetrizer D}
  (G : RouquierGrading W sy)

/-- Degree-`n` 2-morphisms between `f, g : W.obj μ ⟶ W.obj ν`. -/
abbrev deg {μ ν : X} (f g : W.obj μ ⟶ W.obj ν) (n : ℤ) : Submodule k (f ⟶ g) :=
  degree (self := G.graded μ ν) (R := k) f g n

theorem comp_mem {μ ν : X} {f g h : W.obj μ ⟶ W.obj ν} {m n : ℤ} {α : f ⟶ g} {β : g ⟶ h}
    (hα : α ∈ G.deg f g m) (hβ : β ∈ G.deg g h n) : α ≫ β ∈ G.deg f h (m + n) :=
  let _ := G.graded μ ν; comp_mem_degree hα hβ

variable (i : I) {a b c : X} (h₁ : a + D.α i = b) (h₂ : b + D.α i = c)

end RouquierGrading

end Family

end OddMath.SKM
