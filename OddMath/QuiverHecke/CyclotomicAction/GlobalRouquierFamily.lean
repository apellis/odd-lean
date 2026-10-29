/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightSlides

/-!
# The cyclotomic factor family on weight spaces, relative to local inversion

Assembles the fields of `SKM.RouquierFamily` for the cyclotomic weight spaces: weight-space
induction `E_i`, restriction `F_i`, the even adjunction `globalActionAdjunction`, the dot, the
signed crossing `-ψ` (`globalRouquierData`), square zero (`globalRouquierData_square`), the
same-colour braid (`globalRouquierData_braid`) and the two dot slides
(`globalActionSignedCross_slide_left/right`).

The remaining fields of `SKM.SuperRouquierLoc` are the two finite inverses of the Rouquier
mate (KKO I, arXiv:1206.5933v2, the local inversion of Theorem 8.5 / KK Theorem 5.2 in the
even case). They are not proved here: `GlobalLocalInversion` packages exactly these two
inverses at one pair of adjacent weight steps, and `globalRouquierFamily` takes a family of
them as an explicit hypothesis. No other field is assumed. The family also records the degree
hypothesis `CyclotomicDegreeMatch` (each `a i` monic of degree `⟨h_i, Λ⟩`), under which local
inversion is expected to hold; for arbitrary `a` it can fail.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (Λ : X)

/-- The cyclotomic polynomials match the highest weight: each `a i` is monic of degree
`⟨h_i, Λ⟩`. This is the standing assumption of KKO I and of the local-inversion route; without
it `GlobalLocalInversion` can fail: for `a i = 1` and `⟨h_i, Λ⟩ = 5`, at the middle weight
`x₁ = -Λ` the composites through the mate vanish while the five dotted-unit columns have nonzero
source, so `invNeg` has no inverse. -/
def CyclotomicDegreeMatch : Prop :=
  ∀ i, (a i).Monic ∧ ((a i).natDegree : ℤ) = D.h i Λ

/-- The two finite inverses of the Rouquier mate `F_i E_i ⟶ E_i F_i` at the weight steps
`x₀ → x₁ → x₂`, with the dotted counits (positive height `D.h i x₁`) and the dotted units
(negative height) as the extra columns: the `invPos`/`invNeg` fields of
`SKM.SuperRouquierLoc`. This is the local inversion statement, kept as data. -/
structure GlobalLocalInversion (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁)
    (h₂ : x₁ + D.α i = x₂) where
  invPos : 0 ≤ D.h i x₁ → SKM.SuperSumInvTo (k := k)
    (SKM.rouquierMate (globalActionAdjunction D Sc a ha i Λ h₁)
      (globalActionAdjunction D Sc a ha i Λ h₂)
      (globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂))
    (fun n => globalActionF D Sc a ha i Λ h₁ ◁
        SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₁) n ≫
      (globalActionAdjunction D Sc a ha i Λ h₁).counit)
    (D.parity i) (fun n => n * D.parity i) (D.h i x₁).toNat
  invNeg : D.h i x₁ ≤ 0 → SKM.SuperSumInvFrom (k := k)
    (SKM.rouquierMate (globalActionAdjunction D Sc a ha i Λ h₁)
      (globalActionAdjunction D Sc a ha i Λ h₂)
      (globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂))
    (fun n => (globalActionAdjunction D Sc a ha i Λ h₂).unit ≫
      SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) n ▷ globalActionF D Sc a ha i Λ h₂)
    (D.parity i) (fun n => n * D.parity i) (-D.h i x₁).toNat

/-- Rouquier's local data on weight spaces from local inversion: the dots and crossing with
their parities, and the two slides, are proved; the inverses are those of `L`. -/
def globalSuperRouquierLoc (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁)
    (h₂ : x₁ + D.α i = x₂) (L : GlobalLocalInversion D Sc a ha Λ i h₁ h₂) :
    SKM.SuperRouquierLoc (k := k) (globalActionAdjunction D Sc a ha i Λ h₁)
      (globalActionAdjunction D Sc a ha i Λ h₂) (globalActionDot D Sc a ha i Λ h₁)
      (globalActionDot D Sc a ha i Λ h₂) (globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂)
      (D.parity i) (D.h i x₁) where
  dot₁_mem := globalActionDot_mem D Sc a ha i Λ h₁
  dot₂_mem := globalActionDot_mem D Sc a ha i Λ h₂
  cross_mem := globalActionSignedCross_mem_same D Sc a ha i Λ h₁ h₂
  slide_left := globalActionSignedCross_slide_left D Sc a ha i Λ h₁ h₂
  slide_right := globalActionSignedCross_slide_right D Sc a ha i Λ h₁ h₂
  invPos := L.invPos
  invNeg := L.invNeg

/-- **The cyclotomic factor family on weight spaces**, relative to local inversion: every field
of `SKM.RouquierFamily` except the two inverses of the Rouquier mate is proved; those are the
hypothesis `L` (KKO local inversion, not yet formalized), stated under the degree hypothesis
`CyclotomicDegreeMatch`, without which `L` can fail. -/
def globalRouquierFamily (_hdeg : CyclotomicDegreeMatch D a Λ)
    (L : ∀ (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂),
      GlobalLocalInversion D Sc a ha Λ i h₁ h₂) :
    SKM.RouquierFamily (k := k) (B := cyclotomicActionTarget (k := k)) D where
  toRouquierData := globalRouquierData D Sc a ha Λ
  F i _ _ h := globalActionF D Sc a ha i Λ h
  adj i _ _ h := globalActionAdjunction D Sc a ha i Λ h
  square i _ _ _ h₁ h₂ := globalRouquierData_square D Sc a ha Λ i h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := globalRouquierData_braid D Sc a ha i Λ h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := globalSuperRouquierLoc D Sc a ha Λ i h₁ h₂ (L i h₁ h₂)

end OddMath.QuiverHecke.CyclotomicAction
