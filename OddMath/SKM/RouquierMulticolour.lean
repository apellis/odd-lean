import OddMath.SKM.RouquierData
import OddMath.SKM.Presentation

/-!
# Multicolour relations of a super Rouquier family

`RouquierFamily` records the generators of a factor action together with the
same-colour relations of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5: (1.7) for `i = j`, the equal-colour
slides of (1.8), the equal-colour braid relation (1.9), the right adjunction
(1.10) and the local inversions (1.13)–(1.14).

`RouquierMulticolour T Sc` supplies the remaining relations of
`OddMath.SKM.Rel`, transcribed into the bicategorical composition order:

* (1.7) for `i ≠ j`, with the parameters `Sc` (`quadZero`, `quadNe`);
* (1.8) for `i ≠ j` (`slideLeft`, `slideRight`);
* (1.9) for every triple except `i = k ≠ j`, and its corrected form for
  `i = k ≠ j` (`braid`, `braidEq`);
* (1.12): for `i ≠ j` the sideways crossing `σ`, the ordered
  cup–crossing–cap mate `crossMate`, is invertible (`invNe`).

A word `[up i, up j]` with rightmost region `a` is the composite
`E j ≫ E i` out of `obj a`; `cross i j` is the image of the crossing
`crossL [] i j []`. Dots on the rightmost letter of a word act on the first
factor of the composite.

Together with `RouquierFamily` these are the relations of `Presentation.Rel`
that a factor 2-representation must satisfy (input F1 of
`docs/Nondegeneracy/SwappedActionAssembly.md`). The structure is an interface:
nothing here constructs a factor.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory

universe u v w r
variable {k : Type r} [CommRing k]
variable {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The ordered cup–crossing–cap mate of a crossing `t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄`
along right adjunctions `E₁ ⊣ F₁` and `E₂ ⊣ F₂`: insert the unit of `A₂` on
the right, apply `t`, and close with the counit of `A₁` on the left. For a
crossing `cross i j` this is the sideways crossing `σ` of (1.11). -/
def crossMate {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : d ⟶ c} {F₂ : c ⟶ d}
    {E₃ : a ⟶ d} {E₄ : b ⟶ c}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) : F₁ ≫ E₃ ⟶ E₄ ≫ F₂ :=
  (rightUnitor (F₁ ≫ E₃)).inv ≫ (F₁ ≫ E₃) ◁ A₂.unit ≫
  (associator F₁ E₃ (E₂ ≫ F₂)).hom ≫
  F₁ ◁ (associator E₃ E₂ F₂).inv ≫ F₁ ◁ (t ▷ F₂) ≫
  (associator F₁ (E₁ ≫ E₄) F₂).inv ≫
  (associator F₁ E₁ E₄).inv ▷ F₂ ≫
  (A₁.counit ▷ E₄) ▷ F₂ ≫ (leftUnitor E₄).hom ▷ F₂

omit [TwoSupercategory k B] in
/-- On equal colours the mate is the existing `rouquierMate`. -/
theorem crossMate_eq_rouquierMate {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : crossMate A₁ A₂ t = rouquierMate A₁ A₂ t := rfl

variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- The multicolour relations of Definition 1.5 on a super Rouquier family
(see the module docstring for the dictionary of conventions). -/
structure RouquierMulticolour (T : RouquierFamily (k := k) (B := B) D)
    (Sc : Scalars D k) : Prop where
  /-- (1.7), disconnected distinct colours. -/
  quadZero : ∀ (i j : I), i ≠ j → D.d i j = 0 → ∀ {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    T.cross i j h₁ h₂ h₃ h₄ ≫ T.cross j i h₃ h₄ h₁ h₂ = (Sc.t i j : k) • 𝟙 _
  /-- (1.7), connected distinct colours. -/
  quadNe : ∀ (i j : I), i ≠ j → D.d i j ≠ 0 → ∀ {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    T.cross i j h₁ h₂ h₃ h₄ ≫ T.cross j i h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • (T.E j h₁ ◁ rouquierPower (T.dot i h₂) (D.dn i j)) +
      (Sc.t j i : k) • (rouquierPower (T.dot j h₁) (D.dn j i) ▷ T.E i h₂) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (rouquierPower (T.dot j h₁) q ▷ T.E i h₂ ≫
          T.E j h₁ ◁ rouquierPower (T.dot i h₂) p)
  /-- (1.8), the left slide for distinct colours. -/
  slideLeft : ∀ (i j : I), i ≠ j → ∀ {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    T.E j h₁ ◁ T.dot i h₂ ≫ T.cross i j h₁ h₂ h₃ h₄ =
      zsign k (D.parity i * D.parity j) • (T.cross i j h₁ h₂ h₃ h₄ ≫ T.dot i h₃ ▷ T.E j h₄)
  /-- (1.8), the right slide for distinct colours. -/
  slideRight : ∀ (i j : I), i ≠ j → ∀ {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    T.cross i j h₁ h₂ h₃ h₄ ≫ T.E i h₃ ◁ T.dot j h₄ =
      zsign k (D.parity i * D.parity j) • (T.dot j h₁ ▷ T.E i h₂ ≫ T.cross i j h₁ h₂ h₃ h₄)
  /-- (1.9) on the word `[up i, up j, up k]`, outside the case `i = k ≠ j`. -/
  braid : ∀ (i j l : I), ¬(i = l ∧ i ≠ j) → ∀ {a bl bj bi clj cli cji d : X}
    (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
    (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
    (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
    (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d),
    T.E l hal ◁ T.cross i j hlj hd₁ hli hd₂ ≫
        (associator (T.E l hal) (T.E i hli) (T.E j hd₂)).inv ≫
        T.cross i l hal hli hai hil ▷ T.E j hd₂ ≫
        (associator (T.E i hai) (T.E l hil) (T.E j hd₂)).hom ≫
        T.E i hai ◁ T.cross j l hil hd₂ hij hd₃ =
      (associator (T.E l hal) (T.E j hlj) (T.E i hd₁)).inv ≫
        T.cross j l hal hlj haj hjl ▷ T.E i hd₁ ≫
        (associator (T.E j haj) (T.E l hjl) (T.E i hd₁)).hom ≫
        T.E j haj ◁ T.cross i l hjl hd₁ hji hd₃ ≫
        (associator (T.E j haj) (T.E i hji) (T.E l hd₃)).inv ≫
        T.cross i j haj hji hai hij ▷ T.E l hd₃ ≫
        (associator (T.E i hai) (T.E j hij) (T.E l hd₃)).hom
  /-- (1.9) on the word `[up i, up j, up i]` with `i ≠ j`, with its dotted
  correction terms. -/
  braidEq : ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
    (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
    (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
    (hed : e + D.α j = d),
    T.E i hab ◁ T.cross i j hbc hcd hbe hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).inv ≫
        T.cross i i hab hbe hab hbe ▷ T.E j hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).hom ≫
        T.E i hab ◁ T.cross j i hbe hed hbc hcd -
      ((associator (T.E i hab) (T.E j hbc) (T.E i hcd)).inv ≫
        T.cross j i hab hbc haf hfc ▷ T.E i hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).hom ≫
        T.E j haf ◁ T.cross i i hfc hcd hfc hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).inv ≫
        T.cross i j haf hfc hab hbc ▷ T.E i hcd ≫
        (associator (T.E i hab) (T.E j hbc) (T.E i hcd)).hom) =
      ∑ s ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ rouquierPower (T.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ (rouquierPower (T.dot j hbc) q ▷ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ rouquierPower (T.dot i hcd) (p - 1 - s))
  /-- (1.12): for distinct colours the sideways crossing
  `σ : F i ≫ E j ⟶ E j ≫ F i` is invertible. Its inverse is the leftward
  crossing of the presentation. -/
  invNe : ∀ (i j : I), i ≠ j → ∀ {x ν c d : X}
    (h₁ : x + D.α j = d) (h₂ : d + D.α i = c) (h₃ : x + D.α i = ν) (h₄ : ν + D.α j = c),
    IsIso (crossMate (T.adj i h₃) (T.adj i h₂) (T.cross i j h₁ h₂ h₃ h₄))

end OddMath.SKM
