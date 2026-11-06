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

end OddMath.QuiverHecke.CyclotomicAction
