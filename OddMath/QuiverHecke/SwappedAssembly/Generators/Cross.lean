/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.CupCap
import OddMath.SKM.RouquierHomPostCrossingSlide
import OddMath.SKM.RouquierHomMixedInterchange

/-! # The image of the upward crossing in the swapped action

The image of the generator `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, Definition 1.5, in the swapped Hom construction of
`docs/Nondegeneracy/SwappedActionAssembly.md`. A path of a two-letter word is a choice of
summand, `P` (probe) or `R` (reservoir), for each letter, left letter first.

For `i ≠ j` (§2 there):

* `(P,P) → (P,P)`: the reassociated factor crossing `T.cross j i ▷ Z` (the bicategorical
  composite of the word `Eᵢ Eⱼ` is `T.E i ≫ T.E j`), without sign;
* `(R,R) → (R,R)`: `Z ◁ W.cross i j`, conjugated by the even comparison of the two parity
  shifts (`postPairIso`);
* `(P,R) → (R,P)`: the mixed interchange `J` (`mixedJ`);
* `(R,P) → (P,R)`: `J⁻¹` followed by the parameter polynomial `Q` of the target, in the
  probe dot `x` of its left letter and the reservoir dot `y` of its right letter
  (`mixedQ`): `t x^{d} + t' y^{d'} + Σ s^{pq} y^q x^p`, the right-hand side of the relation
  `quadNe`, or `t` if the colours are orthogonal (`quadZero`).

The right sectors of `(P,P)` and `(R,R)` paths of the two words are equal only
propositionally; the target strand is transported along this equality (`preE_obj_heq`,
`postE_obj_heq`).

For `i = j` ((A6) there), with `q = (-1)^{p_i}`:

* `(P,P) → (P,P)`: `-q` times the reassociated factor crossing;
* `(R,R) → (R,R)`: the content-shifted postcomposition crossing `homContentPostCrossingApp`;
* the mixed block, with a coefficient `a ∈ End(F_R(F_P Z))` on the path `(R,P)`:
  `(R,P) → (R,P)`: `a`; `(P,R) → (R,P)`: `J`; `(R,P) → (P,R)`: `-(a ≫ a ≫ J⁻¹)`;
  `(P,R) → (P,R)`: `-(J ≫ a ≫ J⁻¹)`.

The coefficient `a` is data (`CrossCoeff`): it is `(y - x)⁻¹` at even colours and
`(x - y)(x² - y²)⁻¹` at odd colours, `x` the probe dot and `y` the reservoir dot on the path
`(R,P)`. Its characterizing identities are `CrossCoeff.IsInverse`; its existence is a separate
statement.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The type of the entries between two two-letter words, by the summands of their letters
(the argument of `twoTwo`). -/
abbrev TwoEntry (c₁ c₂ d₁ d₂ : Col I X) : Type (max u v w) :=
  ∀ (t : Sector I) (σ₁ σ₂ τ₁ τ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
    (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t)) (hw₁ : StepValid d₁.l τ₁ t)
    (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
    (hs : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) =
      nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))
    (Z : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))),
    (P.step c₁.l σ₁ t hv₁).obj ((P.step c₂.l σ₂ _ hv₂).obj (hs ▸ Z)) ⟶
      (P.step d₁.l τ₁ t hw₁).obj ((P.step d₂.l τ₂ _ hw₂).obj Z)

/-! ## The mixed paths -/

/-- The object of the path `(P,R)` of `Eᵢ Eⱼ` at the left sector `t`. -/
abbrev prObj (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) : P.H t :=
  (P.step (true, i) true t trivial).obj ((P.step (true, j) false _ hR).obj Z)

/-- The object of the path `(R,P)` of `Eᵢ Eⱼ` at the left sector `t`. -/
abbrev rpObj (i j : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, j) true (nextSector (true, i) false t))) : P.H t :=
  (P.step (true, i) false t hv).obj ((P.step (true, j) true _ trivial).obj Z)

/-- The mixed interchange `J` from the path `(P,R)` of `Eᵢ Eⱼ` to the path `(R,P)` of
`Eⱼ Eᵢ`, with the content shifts of the inner and outer reservoir letters at their own
sectors. -/
def mixedJ (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    P.prObj i j t hR Z ≅ P.rpObj j i t hR Z :=
  homMixedInterchange (k := k) (P.T.E i (P.muP_preE i t)) (P.W.E j (P.muM_postE j hR))
    (homContentShift D j (t.1 + Finsupp.single i 1)) (homContentShift D j t.1) Z

/-- The probe dot on the left letter of the path `(P,R)`. -/
def prPreDot (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    End (P.prObj i j t hR Z) :=
  P.T.dot i (P.muP_preE i t) ▷ (P.step (true, j) false _ hR).obj Z

/-- The reservoir dot on the right letter of the path `(P,R)`. -/
def prPostDot (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    End (P.prObj i j t hR Z) :=
  (P.step (true, i) true t trivial).map
    (homContentPostDot P.T.obj P.W j (nextSector (true, i) true t).1
      (P.muP (nextSector (true, i) true t)) (P.muM_postE j hR) Z)

/-- The parameter polynomial `Q_ij(x, y)` on the path `(P,R)` of `Eᵢ Eⱼ`, with `x` the probe
dot of the left letter and `y` the reservoir dot of the right letter: the right-hand side of
the relation `quadNe` (dots on the right strand first), and `t_ij` when `d_ij = 0`
(`quadZero`). -/
def mixedQ (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    End (P.prObj i j t hR Z) :=
  if D.d i j = 0 then (Sc.t i j : k) • (1 : End (P.prObj i j t hR Z)) else
    (Sc.t i j : k) • P.prPreDot i j t hR Z ^ D.dn i j +
      (Sc.t j i : k) • P.prPostDot i j t hR Z ^ D.dn j i +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (P.prPreDot i j t hR Z ^ p * P.prPostDot i j t hR Z ^ q)

/-! ## The distinct-colour crossing -/

/-- The comparison of the two parity shifts of a reservoir/reservoir path `Eᵢ Eⱼ` with a
single shift of the postcomposite: `Π^a (Π^b (Z ≫ Eⱼ) ≫ Eᵢ) ≅ Π^{b+a} ((Z ≫ Eⱼ) ≫ Eᵢ)`,
by the even `β` comparison and the even `ξ` comparison. -/
def postPairIso {x a b c : B} (Ei : b ⟶ c) (Z : x ⟶ a) (Ej : a ⟶ b) (κi κj : ZMod 2) :
    (homParityShift (k := k) κi).obj ((homParityShift (k := k) κj).obj (Z ≫ Ej) ≫ Ei) ≅
      (homParityShift (k := k) (κj + κi)).obj ((Z ≫ Ej) ≫ Ei) :=
  (homParityShift (k := k) κi).mapIso
      ((homParityShiftCommute (k := k) (homPost (k := k) Ei) κj).app (Z ≫ Ej)).symm ≪≫
    (homParityShiftAdd (k := k) κj κi).app ((Z ≫ Ej) ≫ Ei)

/-- The `(P,P)` entry for distinct colours: the reassociated factor crossing, followed by the
transport of the target strand along the equality of right sectors. -/
def preCrossNe (i j : I) (t : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, j) true t))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true t))) :
    (P.step (true, i) true t trivial).obj ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ⟶
      (P.step (true, j) true t trivial).obj ((P.step (true, i) true _ trivial).obj Z) :=
  have h₄ : -P.muP (nextSector (true, j) true t) + D.α i =
      -P.muP (nextSector (true, j) true (nextSector (true, i) true t)) := by
    rw [hs]; exact P.muP_preE i _
  let Z₀ : P.H (nextSector (true, j) true (nextSector (true, i) true t)) := hs ▸ Z
  (associator (P.T.E i (P.muP_preE i t)) (P.T.E j (P.muP_preE j _)) Z₀).inv ≫
    P.T.cross j i (P.muP_preE i t) (P.muP_preE j _) (P.muP_preE j t) h₄ ▷ Z₀ ≫
    (associator (P.T.E j (P.muP_preE j t)) (P.T.E i h₄) Z₀).hom ≫
    (P.step (true, j) true t trivial).map
      (eqToHom (eq_of_heq (P.preE_obj_heq i hs h₄ (P.muP_preE i _) Z)))

/-- The `(R,R)` entry for distinct colours: `Z ◁ W.cross i j` conjugated by the comparisons of
the parity shifts (`postPairIso`), followed by the transport of the target strand along the
equality of right sectors. -/
def postCrossNe (i j : I) (t : Sector I) (hv₁ : StepValid (true, i) false t)
    (hv₂ : StepValid (true, j) false (nextSector (true, i) false t))
    (hw₁ : StepValid (true, j) false t)
    (hw₂ : StepValid (true, i) false (nextSector (true, j) false t))
    (hs : nextSector (true, j) false (nextSector (true, i) false t) =
      nextSector (true, i) false (nextSector (true, j) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false t))) :
    (P.step (true, i) false t hv₁).obj ((P.step (true, j) false _ hv₂).obj (hs ▸ Z)) ⟶
      (P.step (true, j) false t hw₁).obj ((P.step (true, i) false _ hw₂).obj Z) :=
  have h₃ : P.muM (nextSector (true, j) false (nextSector (true, i) false t)) + D.α i =
      P.muM (nextSector (true, j) false t) := by
    rw [hs]; exact P.muM_postE i hw₂
  let Z₀ : P.H (nextSector (true, j) false (nextSector (true, i) false t)) := hs ▸ Z
  (postPairIso (P.W.E i (P.muM_postE i hv₁)) Z₀ (P.W.E j (P.muM_postE j hv₂))
      (homContentShift D i t.1) (homContentShift D j t.1)).hom ≫
    (homParityShift (k := k) (homContentShift D j t.1 + homContentShift D i t.1)).map
      ((associator Z₀ (P.W.E j (P.muM_postE j hv₂)) (P.W.E i (P.muM_postE i hv₁))).hom ≫
        Z₀ ◁ P.W.cross i j (P.muM_postE j hv₂) (P.muM_postE i hv₁) h₃
          (P.muM_postE j hw₁) ≫
        (associator Z₀ (P.W.E i h₃) (P.W.E j (P.muM_postE j hw₁))).inv) ≫
    eqToHom (by rw [add_comm]) ≫
    (postPairIso (P.W.E j (P.muM_postE j hw₁)) Z₀ (P.W.E i h₃)
      (homContentShift D j t.1) (homContentShift D i t.1)).inv ≫
    (P.step (true, j) false t hw₁).map
      (eqToHom (eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z)))

/-- The entries of the upward crossing for distinct colours, by the summands of the letters. -/
def crossNeEntry (i j : I) (r₁ r₂ r₁' r₂' : X) :
    P.TwoEntry ⟨(true, i), r₁⟩ ⟨(true, j), r₂⟩ ⟨(true, j), r₁'⟩ ⟨(true, i), r₂'⟩
  | t, true, true, true, true, _, _, _, _, hs, Z => P.preCrossNe i j t hs Z
  | t, false, false, false, false, hv₁, hv₂, hw₁, hw₂, hs, Z =>
    P.postCrossNe i j t hv₁ hv₂ hw₁ hw₂ hs Z
  | t, true, false, false, true, _, hv₂, _, _, _, Z => (P.mixedJ i j t hv₂ Z).hom
  | t, false, true, true, false, _, _, _, hw₂, _, Z =>
    (P.mixedJ j i t hw₂ Z).inv ≫ P.mixedQ j i t hw₂ Z
  | _, _, _, _, _, _, _, _, _, _, _ => 0

/-! ## The same-colour crossing -/

variable (Sc) in
/-- The coefficient `a` of the mixed block of the same-colour crossing, on the path `(R,P)`. -/
structure CrossCoeff where
  /-- The `(R,P) → (R,P)` entry. -/
  a : ∀ (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))),
    End (P.rpObj i i t hv Z)

/-- The probe dot on the inner letter of the path `(R,P)` of `Eᵢ Eᵢ`. -/
def rpPreDot (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    End (P.rpObj i i t hv Z) :=
  (P.step (true, i) false t hv).map (P.T.dot i _ ▷ Z)

/-- The reservoir dot on the outer letter of the path `(R,P)` of `Eᵢ Eᵢ`. -/
def rpPostDot (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    End (P.rpObj i i t hv Z) :=
  homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)
    ((P.step (true, i) true _ trivial).obj Z)

/-- The characterizing identities of the coefficient: `a = (y - x)⁻¹` at even colours and
`a (x² - y²) = x - y = (x² - y²) a` at odd colours. -/
structure CrossCoeff.IsInverse (c : P.CrossCoeff) : Prop where
  even : ∀ (i : I), D.parity i = 0 → ∀ t hv Z,
    c.a i t hv Z ≫ (P.rpPostDot i t hv Z - P.rpPreDot i t hv Z) = 𝟙 _ ∧
      (P.rpPostDot i t hv Z - P.rpPreDot i t hv Z) ≫ c.a i t hv Z = 𝟙 _
  odd : ∀ (i : I), D.parity i = 1 → ∀ t hv Z,
    c.a i t hv Z ≫ (P.rpPreDot i t hv Z ≫ P.rpPreDot i t hv Z -
        P.rpPostDot i t hv Z ≫ P.rpPostDot i t hv Z) =
      P.rpPreDot i t hv Z - P.rpPostDot i t hv Z ∧
    (P.rpPreDot i t hv Z ≫ P.rpPreDot i t hv Z -
        P.rpPostDot i t hv Z ≫ P.rpPostDot i t hv Z) ≫ c.a i t hv Z =
      P.rpPreDot i t hv Z - P.rpPostDot i t hv Z

/-- The `(P,P)` entry for equal colours: `-q` times the reassociated factor crossing. -/
def preCrossSame (i : I) (t : Sector I)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) true t))) :
    End ((P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj Z)) :=
  (-koszulSign (D.parity i) (D.parity i)) •
    ((associator (P.T.E i (P.muP_preE i t)) (P.T.E i (P.muP_preE i _)) Z).inv ≫
      P.T.cross i i (P.muP_preE i t) (P.muP_preE i _) (P.muP_preE i t) (P.muP_preE i _) ▷ Z ≫
      (associator (P.T.E i (P.muP_preE i t)) (P.T.E i (P.muP_preE i _)) Z).hom)

/-- The `(R,R)` entry for equal colours: the content-shifted postcomposition crossing. -/
def postCrossSame (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false t))) :
    End ((P.step (true, i) false t hv).obj ((P.step (true, i) false _ hw).obj Z)) :=
  homContentPostCrossingApp P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hw)
    (P.muM_postE i hv) Z

/-- The entries of the upward crossing for equal colours, by the summands of the letters. -/
def crossSameEntry (c : P.CrossCoeff) (i : I) (r₁ r₂ r₁' r₂' : X) :
    P.TwoEntry ⟨(true, i), r₁⟩ ⟨(true, i), r₂⟩ ⟨(true, i), r₁'⟩ ⟨(true, i), r₂'⟩
  | t, true, true, true, true, _, _, _, _, _, Z => P.preCrossSame i t Z
  | t, false, false, false, false, hv₁, hv₂, _, _, _, Z => P.postCrossSame i t hv₁ hv₂ Z
  | t, false, true, false, true, hv₁, _, _, _, _, Z => c.a i t hv₁ Z
  | t, true, false, false, true, _, hv₂, _, _, _, Z => (P.mixedJ i i t hv₂ Z).hom
  | t, false, true, true, false, hv₁, _, _, hw₂, _, Z =>
    -(c.a i t hv₁ Z ≫ c.a i t hv₁ Z ≫ (P.mixedJ i i t hw₂ Z).inv)
  | t, true, false, true, false, _, hv₂, _, _, _, Z =>
    -((P.mixedJ i i t hv₂ Z).hom ≫ c.a i t hv₂ Z ≫ (P.mixedJ i i t hv₂ Z).inv)
  | _, _, _, _, _, _, _, _, _, _, _ => 0

/-! ## The image -/

open Classical in
/-- **The image of the upward crossing**, for a coefficient `c` of the same-colour mixed
block. -/
def crossImage (c : P.CrossCoeff) (i j : I) (ν : X) : P.GenImage (.cross i j) ν :=
  if h : i = j then by
    subst h
    exact fun p p' Z => P.twoTwo _ _ _ _ (P.crossSameEntry c i _ _ _ _) p p' rfl Z
  else fun p p' Z => P.twoTwo _ _ _ _ (P.crossNeEntry i j _ _ _ _) p p' rfl Z

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
