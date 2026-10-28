/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierData

/-!
# Rouquier families satisfying the multicolour relations

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5,
relations (1.7)–(1.9) and (1.12) at distinct colours, in the generator form of
`OddMath.SKM.RouquierData`. A `RouquierFamily` already carries the right adjunctions
(1.10), the same-colour quadratic and braid relations, the same-colour dot slides and the
same-colour inversions (1.13)–(1.14) (field `loc`). `RouquierAction D Sc` adds the remaining
relations of `OddMath.SKM.Presentation.Rel`:

* `slideL`, `slideR` for `i ≠ j` (`slide_left_ne`, `slide_right_ne`);
* `quadZero`, `quadNe` (`quad_zero`, `quad_ne`), with the action parameters `Sc`;
* `braid` for `i ≠ k` (`braid_ne`; the case `i = j = k` is `RouquierFamily.braid`) and
  `braidEq` (`braid_eq`);
* `invNe₁`, `invNe₂`: a two-sided inverse `mixedInv` of the mixed mate
  `rouquierMixedMate` (`(1.11)` at distinct colours, built from the given adjunction and
  crossing, not chosen independently).

Each relation is transcribed from `OddMath.SKM.relation`: a layer list read bottom to top
is a composite `≫`, the rightmost letter of a word is the first 1-morphism of a composite,
and `dotsL u i v n` places `rouquierPower` of the dot on the letter `i`.

This is the interface supplied by the deformed cyclotomic factor models
(`docs/Nondegeneracy/SwappedActionAssembly.md`, F1) and consumed by the swapped Hom
assembly. No instance is constructed in this file.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory

universe u v w r
variable {k : Type r} [CommRing k]
variable {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The cup–crossing–cap mate `F ≫ G ⟶ G' ≫ F'` of a crossing `G ≫ E' ⟶ E ≫ G'`,
for right adjunctions `E ⊣ F` and `E' ⊣ F'`. At equal colours it is `rouquierMate`
(`rouquierMixedMate_eq_rouquierMate`). -/
def rouquierMixedMate {p q r s : B} {E : p ⟶ q} {F : q ⟶ p} {E' : r ⟶ s} {F' : s ⟶ r}
    {G : p ⟶ r} {G' : q ⟶ s}
    (A : SuperAdjunction (k := k) E F) (A' : SuperAdjunction (k := k) E' F')
    (t : G ≫ E' ⟶ E ≫ G') : F ≫ G ⟶ G' ≫ F' :=
  (rightUnitor (F ≫ G)).inv ≫ (F ≫ G) ◁ A'.unit ≫
  (associator F G (E' ≫ F')).hom ≫
  F ◁ (associator G E' F').inv ≫ F ◁ (t ▷ F') ≫
  (associator F (E ≫ G') F').inv ≫
  (associator F E G').inv ▷ F' ≫
  (A.counit ▷ G') ▷ F' ≫ (leftUnitor G').hom ▷ F'

omit [TwoSupercategory k B] in
theorem rouquierMixedMate_eq_rouquierMate {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    rouquierMixedMate A₁ A₂ t = rouquierMate A₁ A₂ t := rfl

variable {I X : Type*} [AddCommGroup X] (D : Datum I X)

/-- A Rouquier family satisfying every relation of Definition 1.5 with the parameters `Sc`.
Weights are free variables joined by the displayed edge equations, so that both sides of
each relation are 2-morphisms between the same 1-morphisms. -/
structure RouquierAction (Sc : Scalars D k) extends RouquierFamily (k := k) (B := B) D where
  /-- (1.8), left slide, `i ≠ j`. -/
  slide_left_ne : ∀ (i j : I), i ≠ j → ∀ {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    E j h₁ ◁ dot i h₂ ≫ cross i j h₁ h₂ h₃ h₄ =
      koszulSign (D.parity i) (D.parity j) • (cross i j h₁ h₂ h₃ h₄ ≫ dot i h₃ ▷ E j h₄)
  /-- (1.8), right slide, `i ≠ j`. -/
  slide_right_ne : ∀ (i j : I), i ≠ j → ∀ {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    cross i j h₁ h₂ h₃ h₄ ≫ E i h₃ ◁ dot j h₄ =
      koszulSign (D.parity i) (D.parity j) • (dot j h₁ ▷ E i h₂ ≫ cross i j h₁ h₂ h₃ h₄)
  /-- (1.7) at distinct disconnected colours. -/
  quad_zero : ∀ (i j : I), i ≠ j → D.d i j = 0 → ∀ {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    cross i j h₁ h₂ h₃ h₄ ≫ cross j i h₃ h₄ h₁ h₂ = (Sc.t i j : k) • 𝟙 _
  /-- (1.7) at distinct connected colours. -/
  quad_ne : ∀ (i j : I), i ≠ j → D.d i j ≠ 0 → ∀ {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    cross i j h₁ h₂ h₃ h₄ ≫ cross j i h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • (E j h₁ ◁ rouquierPower (dot i h₂) (D.dn i j)) +
      (Sc.t j i : k) • (rouquierPower (dot j h₁) (D.dn j i) ▷ E i h₂) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (rouquierPower (dot j h₁) q ▷ E i h₂ ≫
          E j h₁ ◁ rouquierPower (dot i h₂) p)
  /-- (1.9) on `Eᵢ Eⱼ Eₖ` for `i ≠ k`. The case `i = j = k` is `RouquierFamily.braid`.
  The weight `a` is the rightmost region; `vₓ` adds the roots in the subscript. -/
  braid_ne : ∀ (i j l : I), i ≠ l → ∀ {a vi vj vl vij vil vjl t : X}
    (hai : a + D.α i = vi) (haj : a + D.α j = vj) (hal : a + D.α l = vl)
    (hij : vi + D.α j = vij) (hji : vj + D.α i = vij)
    (hil : vi + D.α l = vil) (hli : vl + D.α i = vil)
    (hjl : vj + D.α l = vjl) (hlj : vl + D.α j = vjl)
    (hijl : vij + D.α l = t) (hilj : vil + D.α j = t) (hjli : vjl + D.α i = t),
    -- left side: cross the left pair, then the outer pair, then the new left pair
    (associator (E l hal) (E j hlj) (E i hjli)).hom ≫
      E l hal ◁ cross i j hlj hjli hli hilj ≫
      (associator (E l hal) (E i hli) (E j hilj)).inv ≫
      cross i l hal hli hai hil ▷ E j hilj ≫
      (associator (E i hai) (E l hil) (E j hilj)).hom ≫
      E i hai ◁ cross j l hil hilj hij hijl ≫
      (associator (E i hai) (E j hij) (E l hijl)).inv =
    -- right side: cross the right pair, then the outer pair, then the new right pair
    cross j l hal hlj haj hjl ▷ E i hjli ≫
      (associator (E j haj) (E l hjl) (E i hjli)).hom ≫
      E j haj ◁ cross i l hjl hjli hji hijl ≫
      (associator (E j haj) (E i hji) (E l hijl)).inv ≫
      cross i j haj hji hai hij ▷ E l hijl
  /-- (1.9) on `Eᵢ Eⱼ Eᵢ` for `i ≠ j`, with its correction terms. -/
  braid_eq : ∀ (i j : I), i ≠ j → ∀ {a vi vj vii vij t : X}
    (hai : a + D.α i = vi) (haj : a + D.α j = vj)
    (hii : vi + D.α i = vii) (hij : vi + D.α j = vij) (hji : vj + D.α i = vij)
    (hiji : vij + D.α i = t) (hiij : vii + D.α j = t),
    (associator (E i hai) (E j hij) (E i hiji)).hom ≫
      E i hai ◁ cross i j hij hiji hii hiij ≫
      (associator (E i hai) (E i hii) (E j hiij)).inv ≫
      cross i i hai hii hai hii ▷ E j hiij ≫
      (associator (E i hai) (E i hii) (E j hiij)).hom ≫
      E i hai ◁ cross j i hii hiij hij hiji ≫
      (associator (E i hai) (E j hij) (E i hiji)).inv -
    (cross j i hai hij haj hji ▷ E i hiji ≫
      (associator (E j haj) (E i hji) (E i hiji)).hom ≫
      E j haj ◁ cross i i hji hiji hji hiji ≫
      (associator (E j haj) (E i hji) (E i hiji)).inv ≫
      cross i j haj hji hai hij ▷ E i hiji) =
    ∑ s ∈ Finset.range (D.dn i j),
      (((koszulSign (D.parity i) (D.parity j + s) : ℤ) : k) * (Sc.t i j : k)) •
        (rouquierPower (dot i hai) s ▷ E j hij ▷ E i hiji ≫
          (E i hai ≫ E j hij) ◁ rouquierPower (dot i hiji) (D.dn i j - 1 - s)) +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
      (((koszulSign (D.parity i) (D.parity j + s) : ℤ) : k) * Sc.s i j p q) •
        (rouquierPower (dot i hai) s ▷ E j hij ▷ E i hiji ≫
          (E i hai ◁ rouquierPower (dot j hij) q) ▷ E i hiji ≫
          (E i hai ≫ E j hij) ◁ rouquierPower (dot i hiji) (p - 1 - s))
  /-- (1.12): the inverse of the mixed mate `σ : Eⱼ Fᵢ 1 → Fᵢ Eⱼ 1`, `i ≠ j`. -/
  mixedInv : ∀ (i j : I), i ≠ j → ∀ {a b c d : X} (h₁ : a + D.α i = b)
    (h₂ : a + D.α j = c) (h₃ : c + D.α i = d) (h₄ : b + D.α j = d),
    E j h₄ ≫ F i h₃ ⟶ F i h₁ ≫ E j h₂
  mixed_inv_left : ∀ (i j : I) (hij : i ≠ j) {a b c d : X} (h₁ : a + D.α i = b)
    (h₂ : a + D.α j = c) (h₃ : c + D.α i = d) (h₄ : b + D.α j = d),
    rouquierMixedMate (adj i h₁) (adj i h₃) (cross i j h₂ h₃ h₁ h₄) ≫
      mixedInv i j hij h₁ h₂ h₃ h₄ = 𝟙 _
  mixed_inv_right : ∀ (i j : I) (hij : i ≠ j) {a b c d : X} (h₁ : a + D.α i = b)
    (h₂ : a + D.α j = c) (h₃ : c + D.α i = d) (h₄ : b + D.α j = d),
    mixedInv i j hij h₁ h₂ h₃ h₄ ≫
      rouquierMixedMate (adj i h₁) (adj i h₃) (cross i j h₂ h₃ h₁ h₄) = 𝟙 _

end OddMath.SKM
