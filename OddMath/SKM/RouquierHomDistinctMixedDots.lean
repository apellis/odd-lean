import OddMath.SKM.RouquierHomDistinctMixedPre
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The dotted distinct-colour mixed mate `V` and its inverse

Formalizes `docs/Nondegeneracy/SwappedDistinctMixedMates.md` (13)–(15) for the
mixed block `V_ij` of `SwappedActionAssembly.md` (A14), in the following form.
The mate of `J` followed by an endomorphism `Φ` of the target `(E ≫ Z) ≫ E'`
(the action of the polynomial `Q_ij`) is `homDistinctMixedPreMateDot`; it only
depends on `Φ` through `Φ ≫ ε ▷ E'`.

* `homDistinctMixedPreMateDot_eq_comp`: if `J ≫ S_u(Φ) = E ◁ g ≫ J` for an
  endomorphism `g` of the source, the dotted mate is `g ≫ V₀`. This is (13):
  the polynomial coordinate moves to the source side of the dotless mate.
* `MixedTransport`: the transport relation; it is closed under composition,
  sums and scalars, and holds for the post dot `(E ≫ Z) ◁ y`
  (`mixedTransport_post`, with `g = S_t(Z ◁ y)`) and for the even
  middle maps `(E ◁ f) ▷ E'` (`mixedTransport_middle`, `g = S_t(f ▷ E')`).
* The pre dot `x ▷ Z` does not transport by itself; it is the cup–dot–cap
  word (10) after the counit: `homPreDotConj` is the conjugate of
  `x ▷ (-)` along the precomposition adjunction, and
  `homPreDotConj_counit` says `(x ▷ Z) ≫ ε = E ◁ c(x) ≫ ε`. The conjugate is
  multiplicative (`homPreDotConj_comp`), and is invertible when `x` has an even
  inverse (`homPreDotConj_inv`), which is the unit statement (11) for even dots.
* `homDistinctMixedPreMate_inv_products`: `V₀` has the explicit inverse (15),
  and `homDistinctMixedPreMateDot_isIso` gives the inverse of `V` from one of `g`.
* `homDistinctMixedPreMateDot_monomial`: (13) for one supported monomial
  `Y^n Z^m`, with `g = S_t(Z ◁ y) ≫ S_t(c(x) ▷ E')`.
* `isIso_add_of_isNilpotent`: the inverse (14) of `G = A + N` with `A`
  invertible and `N` nilpotent commuting with `A`, as a statement in `End X`.

Only even dots are treated: conjugation along an adjunction needs a natural
transformation, and an odd dot whisker `x ▷ (-)` is only supernatural. The
supported monomials of (12) have even powers, so this covers them.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Interchange
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B}

/-- `J` is natural in its middle object for even maps. -/
theorem homMixedInterchange_naturality_even (E : a ⟶ b) (E' : c ⟶ d) (κ τ : ZMod 2)
    {Z Z' : b ⟶ c} {f : Z ⟶ Z'} (hf : f ∈ parity (R := k) Z Z' 0) :
    E ◁ (homParityShift (k := k) κ).map (f ▷ E') ≫
        (homMixedInterchange (k := k) E E' κ τ Z').hom =
      (homMixedInterchange (k := k) E E' κ τ Z).hom ≫
        (homParityShift (k := k) τ).map ((E ◁ f) ▷ E') := by
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    homPre, Category.assoc]
  rw [← Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k),
    (homParityShiftDatum (k := k) κ).hom_naturality_even
      (TwoSupercategory.whiskerRight_mem E' hf),
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
    TwoSupercategory.associator_inv_naturality_middle_assoc (R := k)]
  have hn := (homParityShiftDatum (k := k) τ).inv_naturality
    (TwoSupercategory.whiskerRight_mem E' (TwoSupercategory.whiskerLeft_mem E hf))
  rw [mul_zero, sign_zero, one_smul] at hn
  rw [hn]

end Interchange

section Dots
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} {F : b ⟶ a} (E : a ⟶ b) (E' : c ⟶ d) {σ : ZMod 2} (t u : ZMod 2)
  (adjd : homPre (k := k) (c := d) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ)
  (adjc : homPre (k := k) (c := c) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ)

/-- The mate `V = M(J ≫ S_u(Φ))` of `J` followed by an endomorphism `Φ` of the target. -/
def homDistinctMixedPreMateDot (H : a ⟶ c)
    (Φ : (E ≫ (homParityShift (k := k) σ).obj (F ≫ H)) ≫ E' ⟶
      (E ≫ (homParityShift (k := k) σ).obj (F ≫ H)) ≫ E') :
    (homParityShift (k := k) t).obj ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E') ⟶
      (homParityShift (k := k) σ).obj (F ≫ (homParityShift (k := k) u).obj (H ≫ E')) :=
  adjd.unit.app ((homParityShift (k := k) t).obj
      ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E')) ≫
    (homPre (k := k) F ⋙ homParityShift (k := k) σ).map
      ((homMixedInterchange (k := k) E E' t u
          ((homParityShift (k := k) σ).obj (F ≫ H))).hom ≫
        (homParityShift (k := k) u).map (Φ ≫ adjc.counit.app H ▷ E'))

variable {E E' t u}

/-- The transport relation `J ≫ S_u(Φ) = E ◁ g ≫ J`. -/
def MixedTransport {Z : b ⟶ c}
    (g : (homParityShift (k := k) t).obj (Z ≫ E') ⟶ (homParityShift (k := k) t).obj (Z ≫ E'))
    (Φ : (E ≫ Z) ≫ E' ⟶ (E ≫ Z) ≫ E') : Prop :=
  (homMixedInterchange (k := k) E E' t u Z).hom ≫ (homParityShift (k := k) u).map Φ =
    E ◁ g ≫ (homMixedInterchange (k := k) E E' t u Z).hom

theorem MixedTransport.comp {Z : b ⟶ c} {g g' Φ Φ'} (h : MixedTransport (k := k) (E := E)
    (E' := E') (t := t) (u := u) (Z := Z) g Φ)
    (h' : MixedTransport (k := k) (t := t) (u := u) g' Φ') :
    MixedTransport (k := k) (t := t) (u := u) (g ≫ g') (Φ ≫ Φ') := by
  unfold MixedTransport at *
  rw [Functor.map_comp, reassoc_of% h, h', TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc]

theorem MixedTransport.add {Z : b ⟶ c} {g g' Φ Φ'} (h : MixedTransport (k := k) (E := E)
    (E' := E') (t := t) (u := u) (Z := Z) g Φ)
    (h' : MixedTransport (k := k) (t := t) (u := u) g' Φ') :
    MixedTransport (k := k) (t := t) (u := u) (g + g') (Φ + Φ') := by
  unfold MixedTransport at *
  rw [Functor.map_add, Preadditive.comp_add, h, h', TwoSupercategory.whiskerLeft_add (R := k),
    Preadditive.add_comp]

theorem MixedTransport.smul {Z : b ⟶ c} {g Φ} (h : MixedTransport (k := k) (E := E)
    (E' := E') (t := t) (u := u) (Z := Z) g Φ) (s : k) :
    MixedTransport (k := k) (t := t) (u := u) (s • g) (s • Φ) := by
  unfold MixedTransport at *
  rw [Functor.map_smul, Linear.comp_smul, h, TwoSupercategory.whiskerLeft_smul (R := k),
    Linear.smul_comp]

variable {adjd adjc}

end Dots

section Conjugate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c : B} {E : a ⟶ b}

/-- An even dot on `E`, whiskered on the right, as a natural endomorphism of `homPre E`. -/
def homPreDot (c : B) (x : E ⟶ E) (hx : x ∈ parity (R := k) E E 0) :
    homPre (k := k) (c := c) E ⟶ homPre (k := k) (c := c) E where
  app H := x ▷ H
  naturality _ _ g := (TwoSupercategory.whisker_exchange_of_even_left (R := k) hx g).symm

variable {F : b ⟶ a} {σ : ZMod 2}
  (adj : homPre (k := k) (c := c) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ)

/-- The conjugate `c(x)` of the dot `x ▷ (-)`: the cup–dot–cap word (10). -/
def homPreDotConj (x : E ⟶ E) (hx : x ∈ parity (R := k) E E 0) :
    homPre (k := k) (c := c) F ⋙ homParityShift (k := k) σ ⟶
      homPre (k := k) (c := c) F ⋙ homParityShift (k := k) σ :=
  conjugateEquiv adj adj (homPreDot c x hx)

end Conjugate

section Inverse
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} {F : b ⟶ a} {σ : ZMod 2} (t u : ZMod 2) (H : a ⟶ c) (E' : c ⟶ d)

/-- The explicit inverse (15) of the coordinate word of `V₀`. -/
def homDistinctMixedPreMateInv :
    (homParityShift (k := k) σ).obj (F ≫ (homParityShift (k := k) u).obj (H ≫ E')) ⟶
      (homParityShift (k := k) t).obj ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E') :=
  sign k (σ * u) •
    (((homParityShiftDatum (k := k) σ).iso
        (F ≫ (homParityShift (k := k) u).obj (H ≫ E'))).hom ≫
      F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).hom ≫
      (associator F H E').inv ≫
      ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).inv ▷ E' ≫
      ((homParityShiftDatum (k := k) t).iso
        ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E')).inv)

/-- Both inverse products of the coordinate word of `V₀` are adjacent cancellations. -/
theorem homDistinctMixedPreMateWord_inv_products :
    (sign k (σ * u) •
      (((homParityShiftDatum (k := k) t).iso
          ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E')).hom ≫
        ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ▷ E' ≫
        (associator F H E').hom ≫
        F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv ≫
        ((homParityShiftDatum (k := k) σ).iso
          (F ≫ (homParityShift (k := k) u).obj (H ≫ E'))).inv)) ≫
        homDistinctMixedPreMateInv t u H E' = 𝟙 _ ∧
    homDistinctMixedPreMateInv t u H E' ≫
      (sign k (σ * u) •
        (((homParityShiftDatum (k := k) t).iso
            ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E')).hom ≫
          ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ▷ E' ≫
          (associator F H E').hom ≫
          F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv ≫
          ((homParityShiftDatum (k := k) σ).iso
            (F ≫ (homParityShift (k := k) u).obj (H ≫ E'))).inv)) = 𝟙 _ := by
  have hb1 : ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ▷ E' ≫
      ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).inv ▷ E' = 𝟙 _ := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), Iso.hom_inv_id,
      TwoSupercategory.id_whiskerRight (R := k)]
  have hb2 : ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).inv ▷ E' ≫
      ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ▷ E' = 𝟙 _ := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), Iso.inv_hom_id,
      TwoSupercategory.id_whiskerRight (R := k)]
  have hc1 : F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv ≫
      F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).hom = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), Iso.inv_hom_id,
      TwoSupercategory.whiskerLeft_id (R := k)]
  have hc2 : F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).hom ≫
      F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), Iso.hom_inv_id,
      TwoSupercategory.whiskerLeft_id (R := k)]
  unfold homDistinctMixedPreMateInv
  constructor
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, reassoc_of% hc1, Iso.hom_inv_id_assoc, reassoc_of% hb1,
      Iso.hom_inv_id]
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, reassoc_of% hb2, Iso.inv_hom_id_assoc, reassoc_of% hc2,
      Iso.hom_inv_id]

end Inverse

section MateInverse
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} {F : b ⟶ a} {E : a ⟶ b} {E' : c ⟶ d} {σ : ZMod 2} {t u : ZMod 2}
  {adjd : homPre (k := k) (c := d) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ}
  {adjc : homPre (k := k) (c := c) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ}

/-- (15) for `V₀`: under the normalized unit and counit words, `V₀` is invertible with
the explicit inverse `homDistinctMixedPreMateInv`. -/
theorem homDistinctMixedPreMate_inv_products (A : ShiftedSuperAdjunction (k := k) F E σ)
    (hunit : ∀ Y : b ⟶ d, adjd.unit.app Y = (leftUnitor Y).inv ≫ A.unit ▷ Y ≫
      (associator F E Y).hom ≫ ((homParityShiftDatum (k := k) σ).iso (F ≫ E ≫ Y)).inv)
    (hcounit : ∀ H : a ⟶ c, adjc.counit.app H = koszulSign σ σ •
      (E ◁ ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ≫
        (associator E F H).inv ≫ A.counit ▷ H ≫ (leftUnitor H).hom))
    (H : a ⟶ c) :
    homDistinctMixedPreMate E E' t u adjd adjc H ≫ homDistinctMixedPreMateInv t u H E' = 𝟙 _ ∧
      homDistinctMixedPreMateInv t u H E' ≫ homDistinctMixedPreMate E E' t u adjd adjc H =
        𝟙 _ := by
  rw [homDistinctMixedPreMate_eq A hunit hcounit H]
  exact homDistinctMixedPreMateWord_inv_products t u H E'

end MateInverse

section Monomial
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} {F : b ⟶ a} {E : a ⟶ b} {E' : c ⟶ d} {σ : ZMod 2} {t u : ZMod 2}
  {adjd : homPre (k := k) (c := d) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ}
  {adjc : homPre (k := k) (c := c) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ}

end Monomial

section Unit
variable {C : Type*} [Category C] [Preadditive C]

end Unit
end OddMath.SKM
