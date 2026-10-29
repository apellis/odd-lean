/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.Dot
import OddMath.SKM.RouquierFTriangle

/-! # The images of the rightward cup and cap in the swapped action

The images of the generators `η : 1 → Fᵢ Eᵢ` and `ε : Eᵢ Fᵢ → 1` of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, in the swapped Hom
construction of `docs/Nondegeneracy/SwappedActionAssembly.md`, (A3). Both are diagonal in the
summands of the two strands:

* on two probe letters, the unit and counit of `homContentPreAdjunction` for the
  inverse-defined left adjunctions `T.leftAdjoints` of the factor;
* on two reservoir letters, the unit and counit of `homContentPostAdjunction`;

and zero on paths through different summands. The adjunction is taken at the left sector of
the cup (for the cap: at the sector between the two strands of its input, whose left sector is
the left sector of the cap); the inner strand is then identified with the left adjoint along the
equality of the right sector with the left sector (`preE_obj_heq`, `postE_obj_heq`,
`preF_obj_heq`, `postF_obj_heq`), which holds only propositionally since contents are
subtracted and added back.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-! ## Transport of a strand along an equality of sectors -/

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem preE_obj_heq (i : I) {s s' : Sector I} (hs : s = s') {x : X}
    (h : -x + D.α i = -P.muP s) (h' : -x + D.α i = -P.muP s') (Z : P.H s') :
    HEq ((homContentPreE P.T P.W.obj i (P.muM s) h).obj (hs ▸ Z : P.H s))
      ((homContentPreE P.T P.W.obj i (P.muM s') h').obj Z) := by
  subst hs; rfl

theorem preF_obj_heq (i : I) {s s' : Sector I} (hs : s = s') {x : X}
    (h : -P.muP s + D.α i = -x) (h' : -P.muP s' + D.α i = -x) (Z : P.H s') :
    HEq ((homContentPreF P.T P.W.obj i (P.muM s) h).obj (hs ▸ Z : P.H s))
      ((homContentPreF P.T P.W.obj i (P.muM s') h').obj Z) := by
  subst hs; rfl

theorem postE_obj_heq (i : I) (β : I →₀ ℕ) {s s' : Sector I} (hs : s = s') {x : X}
    (h : P.muM s + D.α i = x) (h' : P.muM s' + D.α i = x) (Z : P.H s') :
    HEq ((homContentPostE P.T.obj P.W i β (P.muP s) h).obj (hs ▸ Z : P.H s))
      ((homContentPostE P.T.obj P.W i β (P.muP s') h').obj Z) := by
  subst hs; rfl

theorem postF_obj_heq (i : I) (β : I →₀ ℕ) {s s' : Sector I} (hs : s = s') {x : X}
    (h : x + D.α i = P.muM s) (h' : x + D.α i = P.muM s') (Z : P.H s') :
    HEq ((homContentPostF P.T.obj P.W i β (P.muP s) h).obj (hs ▸ Z : P.H s))
      ((homContentPostF P.T.obj P.W i β (P.muP s') h').obj Z) := by
  subst hs; rfl

/-! ## The cup -/

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The weight equation of a probe `Fᵢ` at a sector. -/
theorem muP_preF (i : I) {t : Sector I} (hv : StepValid (false, i) true t) :
    -P.muP (nextSector (false, i) true t) + D.α i = -P.muP t := by
  change -P.muP (t.1 - Finsupp.single i 1, t.2) + D.α i = -P.muP t
  simp only [muP]; rw [← contentWeight_sub_single (D := D) hv]; abel

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The weight equation of a probe `Eᵢ` at a sector. -/
theorem muP_preE (i : I) (t : Sector I) :
    -P.muP t + D.α i = -P.muP (nextSector (true, i) true t) := by
  change -P.muP t + D.α i = -P.muP (t.1 + Finsupp.single i 1, t.2)
  simp only [muP, contentWeight_add_single]; abel

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The weight equation of a reservoir `Fᵢ` at a sector. -/
theorem muM_postF (i : I) (t : Sector I) :
    P.muM t + D.α i = P.muM (nextSector (false, i) false t) := by
  change P.muM t + D.α i = P.muM (t.1, t.2 + Finsupp.single i 1)
  simp only [muM, contentWeight_add_single]; abel

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The weight equation of a reservoir `Eᵢ` at a sector. -/
theorem muM_postE (i : I) {t : Sector I} (hv : StepValid (true, i) false t) :
    P.muM (nextSector (true, i) false t) + D.α i = P.muM t := by
  change P.muM (t.1, t.2 - Finsupp.single i 1) + D.α i = P.muM t
  simp only [muM]; rw [add_assoc, contentWeight_sub_single hv]

/-- The adjunction of a probe strand at the sector on its right: `Eᵢ` from the sector
`nextSector (false, i) true t` to `t`... -/
def preAdjAt (i : I) {t : Sector I} (hv : StepValid (false, i) true t) :=
  homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t) (P.muP_preF i hv)

/-- The cup on two probe letters: the unit of the content-shifted precomposition adjunction
at the left sector. -/
def preCup (i : I) (t : Sector I) (hv : StepValid (false, i) true t)
    (hw : StepValid (true, i) true (nextSector (false, i) true t))
    (hs : t = nextSector (true, i) true (nextSector (false, i) true t))
    (Z : P.H (nextSector (true, i) true (nextSector (false, i) true t))) :
    (hs ▸ Z : P.H t) ⟶
      (P.step (false, i) true t hv).obj ((P.step (true, i) true _ hw).obj Z) :=
  (P.preAdjAt i hv).unit.app (hs ▸ Z) ≫
    (P.step (false, i) true t hv).map (eqToHom (eq_of_heq (P.preE_obj_heq i hs _ _ Z)))

/-- The cup on two reservoir letters: the unit of the content-shifted postcomposition
adjunction at the left sector. -/
def postCup (i : I) (t : Sector I) (hv : StepValid (false, i) false t)
    (hw : StepValid (true, i) false (nextSector (false, i) false t))
    (hs : t = nextSector (true, i) false (nextSector (false, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (false, i) false t))) :
    (hs ▸ Z : P.H t) ⟶
      (P.step (false, i) false t hv).obj ((P.step (true, i) false _ hw).obj Z) :=
  (homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).unit.app (hs ▸ Z) ≫
    (P.step (false, i) false t hv).map (eqToHom (eq_of_heq (P.postE_obj_heq i t.1 hs _ _ Z)))

/-- The cap on two probe letters: the counit of the content-shifted precomposition
adjunction at the left sector. -/
def preCap (i : I) (t : Sector I) (hv : StepValid (true, i) true t)
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (hs : t = nextSector (false, i) true (nextSector (true, i) true t))
    (Z : P.H (nextSector (false, i) true (nextSector (true, i) true t))) :
    (P.step (true, i) true t hv).obj ((P.step (false, i) true _ hw).obj Z) ⟶ (hs ▸ Z : P.H t) :=
  (P.step (true, i) true t hv).map (eqToHom (eq_of_heq (P.preF_obj_heq i hs _ _ Z).symm)) ≫
    (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t)
      (P.muP_preE i t)).counit.app (hs ▸ Z)

/-- The cap on two reservoir letters: the counit of the content-shifted postcomposition
adjunction at the left sector. -/
def postCap (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (false, i) false (nextSector (true, i) false t))
    (hs : t = nextSector (false, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (false, i) false (nextSector (true, i) false t))) :
    (P.step (true, i) false t hv).obj ((P.step (false, i) false _ hw).obj Z) ⟶ (hs ▸ Z : P.H t) :=
  (P.step (true, i) false t hv).map
      (eqToHom (eq_of_heq (P.postF_obj_heq i t.1 hs _ _ Z).symm)) ≫
    (homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).counit.app (hs ▸ Z)

/-! ## Two-letter matrices

A path of a two-letter word is a choice of summand for each letter. The helpers below split the
paths of the boundaries of a generator into these choices, keeping the sectors in the form
`nextSector l σ t` with `σ` a variable, and leave the entries to a function of the choices. -/

/-- Entries from the empty word to a two-letter word. -/
def zeroTwo (d₁ d₂ : Col I X)
    (f : ∀ (t : Sector I) (τ₁ τ₂ : Bool) (hw₁ : StepValid d₁.l τ₁ t)
      (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (hs : t = nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (Z : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))),
      (hs ▸ Z : P.H t) ⟶ (P.step d₁.l τ₁ t hw₁).obj ((P.step d₂.l τ₂ _ hw₂).obj Z)) :
    ∀ {t s s' : Sector I} (_p : SPath [] t s) (_p' : SPath [d₁, d₂] t s') (hs : s = s')
      (Z : P.H s'), (P.pathFunctor _p).obj (hs ▸ Z) ⟶ (P.pathFunctor _p').obj Z
  | t, _, _, .nil _, .cons _ τ₁ _ hw₁ (.cons _ τ₂ _ hw₂ (.nil _)), hs, Z =>
    f t τ₁ τ₂ hw₁ hw₂ hs Z

/-- Entries from a two-letter word to the empty word. The right sector of the source path is
related to that of the target path by `hs`. -/
def twoZero (c₁ c₂ : Col I X)
    (f : ∀ (t : Sector I) (σ₁ σ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
      (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t))
      (hs : t = nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t))
      (Z : P.H (nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t))),
      (P.step c₁.l σ₁ t hv₁).obj ((P.step c₂.l σ₂ _ hv₂).obj Z) ⟶ (hs ▸ Z : P.H t)) :
    ∀ {t s s' : Sector I} (_p : SPath [c₁, c₂] t s) (_p' : SPath [] t s') (hs : s' = s)
      (Z : P.H s), (P.pathFunctor _p).obj Z ⟶ (P.pathFunctor _p').obj (hs ▸ Z)
  | t, _, _, .cons _ σ₁ _ hv₁ (.cons _ σ₂ _ hv₂ (.nil _)), .nil _, hs, Z =>
    f t σ₁ σ₂ hv₁ hv₂ hs Z

/-- Entries between two two-letter words. -/
def twoTwo (c₁ c₂ d₁ d₂ : Col I X)
    (f : ∀ (t : Sector I) (σ₁ σ₂ τ₁ τ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
      (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t)) (hw₁ : StepValid d₁.l τ₁ t)
      (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (hs : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) =
        nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (Z : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))),
      (P.step c₁.l σ₁ t hv₁).obj ((P.step c₂.l σ₂ _ hv₂).obj (hs ▸ Z)) ⟶
        (P.step d₁.l τ₁ t hw₁).obj ((P.step d₂.l τ₂ _ hw₂).obj Z)) :
    ∀ {t s s' : Sector I} (_p : SPath [c₁, c₂] t s) (_p' : SPath [d₁, d₂] t s')
      (hs : s = s') (Z : P.H s'), (P.pathFunctor _p).obj (hs ▸ Z) ⟶ (P.pathFunctor _p').obj Z
  | t, _, _, .cons _ σ₁ _ hv₁ (.cons _ σ₂ _ hv₂ (.nil _)),
      .cons _ τ₁ _ hw₁ (.cons _ τ₂ _ hw₂ (.nil _)), hs, Z =>
    f t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ hs Z

/-! ## The cup and the cap -/

/-- The entries of the cup, by the summands of its two letters. -/
def cupEntry (i : I) (r₁ r₂ : X) : ∀ (t : Sector I) (τ₁ τ₂ : Bool)
    (hw₁ : StepValid (⟨(false, i), r₁⟩ : Col I X).l τ₁ t)
    (hw₂ : StepValid (⟨(true, i), r₂⟩ : Col I X).l τ₂
      (nextSector (⟨(false, i), r₁⟩ : Col I X).l τ₁ t))
    (hs : t = nextSector (⟨(true, i), r₂⟩ : Col I X).l τ₂
      (nextSector (⟨(false, i), r₁⟩ : Col I X).l τ₁ t))
    (Z : P.H (nextSector (⟨(true, i), r₂⟩ : Col I X).l τ₂
      (nextSector (⟨(false, i), r₁⟩ : Col I X).l τ₁ t))),
    (hs ▸ Z : P.H t) ⟶ (P.step (⟨(false, i), r₁⟩ : Col I X).l τ₁ t hw₁).obj
      ((P.step (⟨(true, i), r₂⟩ : Col I X).l τ₂ _ hw₂).obj Z)
  | t, true, true, hw₁, hw₂, hs, Z => P.preCup i t hw₁ hw₂ hs Z
  | t, false, false, hw₁, hw₂, hs, Z => P.postCup i t hw₁ hw₂ hs Z
  | _, true, false, _, _, _, _ => 0
  | _, false, true, _, _, _, _ => 0

/-- The entries of the cap, by the summands of its two letters. -/
def capEntry (i : I) (r₁ r₂ : X) : ∀ (t : Sector I) (σ₁ σ₂ : Bool)
    (hv₁ : StepValid (⟨(true, i), r₁⟩ : Col I X).l σ₁ t)
    (hv₂ : StepValid (⟨(false, i), r₂⟩ : Col I X).l σ₂
      (nextSector (⟨(true, i), r₁⟩ : Col I X).l σ₁ t))
    (hs : t = nextSector (⟨(false, i), r₂⟩ : Col I X).l σ₂
      (nextSector (⟨(true, i), r₁⟩ : Col I X).l σ₁ t))
    (Z : P.H (nextSector (⟨(false, i), r₂⟩ : Col I X).l σ₂
      (nextSector (⟨(true, i), r₁⟩ : Col I X).l σ₁ t))),
    (P.step (⟨(true, i), r₁⟩ : Col I X).l σ₁ t hv₁).obj
      ((P.step (⟨(false, i), r₂⟩ : Col I X).l σ₂ _ hv₂).obj Z) ⟶ (hs ▸ Z : P.H t)
  | t, true, true, hv₁, hv₂, hs, Z => P.preCap i t hv₁ hv₂ hs Z
  | t, false, false, hv₁, hv₂, hs, Z => P.postCap i t hv₁ hv₂ hs Z
  | _, true, false, _, _, _, _ => 0
  | _, false, true, _, _, _, _ => 0

/-- **The image of the rightward cup.** -/
def cupImage (i : I) (ν : X) : P.GenImage (.cup i) ν := fun p p' Z =>
  P.zeroTwo _ _ (P.cupEntry i _ _) p p' rfl Z

/-- **The image of the rightward cap.** -/
def capImage (i : I) (ν : X) : P.GenImage (.cap i) ν := fun p p' Z =>
  P.twoZero _ _ (P.capEntry i _ _) p p' rfl Z

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
