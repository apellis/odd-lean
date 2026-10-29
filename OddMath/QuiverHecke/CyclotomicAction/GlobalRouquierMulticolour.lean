/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierFamily
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightMixedSlides
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightMixedQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import OddMath.SKM.RouquierMulticolour

/-!
# Distinct-colour relations of the cyclotomic factor family

Brundan–Ellis, *Super Kac–Moody 2-categories* (arXiv:1701.04133v2), Definition 1.5, for the
family `globalRouquierFamily D (parameterTwist D Sc)` on cyclotomic weight spaces with the
2-category scalars `Sc` (the scalars of the factor are those of `parameterTwist D Sc`, and
`parameterTwist_involutive` brings them back to `Sc`).

* `globalRouquierFamily_quadZero`, `globalRouquierFamily_quadNe`: relation (1.7), `i ≠ j`;
* `globalRouquierFamily_slideLeft`, `globalRouquierFamily_slideRight`: relation (1.8), `i ≠ j`;
* `globalRouquierFamily_multicolour`: `SKM.RouquierMulticolour` for this family, from the three
  remaining fields `braid`, `braidEq` (relation (1.9)) and `invNe` (relation (1.12)), which are
  hypotheses here. `invNe` needs the distinct-colour Mackey isomorphism for the global factors,
  which is not formalized.

The family is given as `T` with an equation `hT`, so that the bound weight variables of the
fields do not clash with the cyclotomic polynomials `a`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.SKM (zsign rouquierPower crossMate)
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (Λ : X)
  (hdeg : CyclotomicDegreeMatch D a Λ)
  (L : ∀ (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂),
    GlobalLocalInversion D (parameterTwist D Sc) a ha Λ i h₁ h₂)
  {T : SKM.RouquierFamily (k := k) (B := cyclotomicActionTarget (k := k)) D}
  (hT : T = globalRouquierFamily D (parameterTwist D Sc) a ha Λ hdeg L)
include hT

/-- Relation (1.7) for disconnected distinct colours on the cyclotomic factor family, with
the scalars `Sc`. -/
theorem globalRouquierFamily_quadZero (i j : I) (hij : i ≠ j) (hd : D.d i j = 0)
    {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
    (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃) :
    T.cross i j h₁ h₂ h₃ h₄ ≫ T.cross j i h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • 𝟙 _ := by
  subst hT
  have h :=
    globalActionSignedCross_square_zero D (parameterTwist D Sc) a ha hij Λ h₁ h₂ h₃ h₄ hd
  rw [parameterTwist_involutive] at h
  exact h

/-- Relation (1.7) for connected distinct colours on the cyclotomic factor family, with the
scalars `Sc`. -/
theorem globalRouquierFamily_quadNe (i j : I) (hij : i ≠ j) (hd : D.d i j ≠ 0)
    {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
    (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃) :
    T.cross i j h₁ h₂ h₃ h₄ ≫ T.cross j i h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • (T.E j h₁ ◁ rouquierPower (T.dot i h₂) (D.dn i j)) +
      (Sc.t j i : k) • (rouquierPower (T.dot j h₁) (D.dn j i) ▷ T.E i h₂) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (rouquierPower (T.dot j h₁) q ▷ T.E i h₂ ≫
          T.E j h₁ ◁ rouquierPower (T.dot i h₂) p) := by
  subst hT
  have h :=
    globalActionSignedCross_square_ne D (parameterTwist D Sc) a ha hij Λ h₁ h₂ h₃ h₄ hd
  rw [parameterTwist_involutive] at h
  exact h

/-- Relation (1.8), the left slide for distinct colours, on the cyclotomic factor family. -/
theorem globalRouquierFamily_slideLeft (i j : I) (hij : i ≠ j) {x₀ x₁ x₂ x₃ : X}
    (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂)
    (h₄ : x₂ + D.α j = x₃) :
    T.E j h₁ ◁ T.dot i h₂ ≫ T.cross i j h₁ h₂ h₃ h₄ =
      zsign k (D.parity i * D.parity j) •
        (T.cross i j h₁ h₂ h₃ h₄ ≫ T.dot i h₃ ▷ T.E j h₄) := by
  subst hT
  exact
    globalActionSignedCross_slide_left_ne D (parameterTwist D Sc) a ha hij Λ h₁ h₂ h₃ h₄

/-- Relation (1.8), the right slide for distinct colours, on the cyclotomic factor family. -/
theorem globalRouquierFamily_slideRight (i j : I) (hij : i ≠ j) {x₀ x₁ x₂ x₃ : X}
    (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂)
    (h₄ : x₂ + D.α j = x₃) :
    T.cross i j h₁ h₂ h₃ h₄ ≫ T.E i h₃ ◁ T.dot j h₄ =
      zsign k (D.parity i * D.parity j) •
        (T.dot j h₁ ▷ T.E i h₂ ≫ T.cross i j h₁ h₂ h₃ h₄) := by
  subst hT
  exact
    globalActionSignedCross_slide_right_ne D (parameterTwist D Sc) a ha hij Λ h₁ h₂ h₃ h₄

/-- **The multicolour relations of Definition 1.5 for the cyclotomic factor family**, with the
scalars `Sc`, relative to the remaining fields: the braid relations (1.9) and the invertibility
(1.12) are hypotheses (intermediate statement; the distinct-colour Mackey isomorphism needed
for `invNe` is not formalized). -/
theorem globalRouquierFamily_multicolour
    (hBraid :
      ∀ (i j l : I), ¬(i = l ∧ i ≠ j) → ∀ {a bl bj bi clj cli cji d : X}
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
            (associator (T.E i hai) (T.E j hij) (T.E l hd₃)).hom)
    (hBraidEq :
      ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
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
          ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
            ∑ s ∈ Finset.range p,
            (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
              (rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
                T.E i hab ◁ (rouquierPower (T.dot j hbc) q ▷ T.E i hcd) ≫
                T.E i hab ◁ T.E j hbc ◁ rouquierPower (T.dot i hcd) (p - 1 - s)))
    (hInvNe :
      ∀ (i j : I), i ≠ j → ∀ {x ν c d : X}
        (h₁ : x + D.α j = d) (h₂ : d + D.α i = c) (h₃ : x + D.α i = ν)
        (h₄ : ν + D.α j = c),
        IsIso (crossMate (T.adj i h₃) (T.adj i h₂) (T.cross i j h₁ h₂ h₃ h₄))) :
    SKM.RouquierMulticolour T Sc where
  quadZero i j hij hd _ _ _ _ h₁ h₂ h₃ h₄ :=
    globalRouquierFamily_quadZero D Sc a ha Λ hdeg L hT i j hij hd h₁ h₂ h₃ h₄
  quadNe i j hij hd _ _ _ _ h₁ h₂ h₃ h₄ :=
    globalRouquierFamily_quadNe D Sc a ha Λ hdeg L hT i j hij hd h₁ h₂ h₃ h₄
  slideLeft i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    globalRouquierFamily_slideLeft D Sc a ha Λ hdeg L hT i j hij h₁ h₂ h₃ h₄
  slideRight i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    globalRouquierFamily_slideRight D Sc a ha Λ hdeg L hT i j hij h₁ h₂ h₃ h₄
  braid := hBraid
  braidEq := hBraidEq
  invNe := hInvNe

end OddMath.QuiverHecke.CyclotomicAction
