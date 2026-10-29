/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedConditionalNondegeneracy
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces

/-!
# The Nondegeneracy Conjecture from the cyclotomic factor actions (conditional)

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8. This file instantiates the probe and
reservoir factors of `nondegeneracy_of_swapped_vacuum_observations` by the cyclotomic factor
actions on weight spaces (`SwappedActionAssembly.md` §1, F1–F2), in the target `Π-𝔖ℭ𝔞𝔱`.

* `globalProbeReservoir`: the probe and reservoir are `globalPiRouquierFamily` at the
  cyclotomic parameters `aP`, `aR` and highest weights `ΛP`, `ΛR`. The probe's shifted left
  adjunctions are `RouquierFamily.leftAdjoints` (proved for every super Rouquier family). The
  inputs are the local inversions (`GlobalLocalInversion`) and the multicolour relations
  (`SKM.RouquierMulticolour`) of the two families in `𝔖ℭ𝔞𝔱`.
* `nondegeneracy_of_global_factor_observations`: the conditional theorem with these factors.
  Local inversion is taken under the hypothesis `CyclotomicDegreeMatch` (each `aᵢ` monic of
  degree `⟨hᵢ, Λ⟩`), without which `GlobalLocalInversion` is false (for instance `aᵢ = 1` and
  `⟨hᵢ, Λ⟩ = 5`).

The remaining hypotheses are: local inversion under the degree condition, the multicolour
relations of the two factor families, and the swapped vacuum observations with these factors
(crossing coefficient, leftward data, relation identities, vacuum, bubble series, corner
evaluation and weight bound).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SwappedAssembly CyclotomicAction
universe u

variable {I X k : Type u} [AddCommGroup X] (D : SKM.Datum I X)

/-- The morphism supercategories of `Π-𝔖ℭ𝔞𝔱` are Π-supercategories. -/
local instance piSCatHomPi [CommRing k] (A C : PiSCat.{u, u, u + 1} k) :
    PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

section Ring
variable [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]

/-- **The probe and reservoir from the cyclotomic factor actions**, relative to local
inversion and the multicolour relations of the two families. -/
def globalProbeReservoir
    (aP : I → _root_.Polynomial k) (haP : CyclotomicPolynomialParity D aP) (ΛP : X)
    (hdegP : CyclotomicDegreeMatch D aP ΛP)
    (LP : ∀ (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂),
      GlobalLocalInversion D Sc aP haP ΛP i h₁ h₂)
    (aR : I → _root_.Polynomial k) (haR : CyclotomicPolynomialParity D aR) (ΛR : X)
    (hdegR : CyclotomicDegreeMatch D aR ΛR)
    (LR : ∀ (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂),
      GlobalLocalInversion D Sc aR haR ΛR i h₁ h₂)
    (hP : SKM.RouquierMulticolour (globalRouquierFamily D Sc aP haP ΛP hdegP LP) Sc)
    (hR : SKM.RouquierMulticolour (globalRouquierFamily D Sc aR haR ΛR hdegR LR) Sc) :
    ProbeReservoir k (PiSCat.{u, u, u + 1} k) D Sc where
  T := globalPiRouquierFamily D Sc aP haP ΛP hdegP LP
  W := globalPiRouquierFamily D Sc aR haR ΛR hdegR LR
  leftAdj := (globalPiRouquierFamily D Sc aP haP ΛP hdegP LP).leftAdjoints
  probeRel := hP.toPiSCat _
  reservoirRel := hR.toPiSCat _
  ΛP := ΛP
  ΛR := ΛR

end Ring

section Field
variable {k : Type u} [Field k] (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)
  [Fintype I] [DecidableEq I]

/-- **Conditional field theorem from the cyclotomic factor actions.** Fix cyclotomic
parameters `aP`, `aR` satisfying the degree condition at `ΛP`, `ΛR`. Given local inversion for
every parameter satisfying the degree condition, the multicolour relations of the two factor
families, and swapped vacuum observations whose probe and reservoir are these factors at every
equal-weight upward word pair, external weight and degree bound, the Nondegeneracy Conjecture
holds. -/
theorem nondegeneracy_of_global_factor_observations
    (aP : I → _root_.Polynomial k) (haP : CyclotomicPolynomialParity D aP) (ΛP : X)
    (hdegP : CyclotomicDegreeMatch D aP ΛP)
    (LP : CyclotomicDegreeMatch D aP ΛP → ∀ (i : I) {x₀ x₁ x₂ : X}
      (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂),
      GlobalLocalInversion D Sc aP haP ΛP i h₁ h₂)
    (aR : I → _root_.Polynomial k) (haR : CyclotomicPolynomialParity D aR) (ΛR : X)
    (hdegR : CyclotomicDegreeMatch D aR ΛR)
    (LR : CyclotomicDegreeMatch D aR ΛR → ∀ (i : I) {x₀ x₁ x₂ : X}
      (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂),
      GlobalLocalInversion D Sc aR haR ΛR i h₁ h₂)
    (hP : SKM.RouquierMulticolour (globalRouquierFamily D Sc aP haP ΛP hdegP (LP hdegP)) Sc)
    (hR : SKM.RouquierMulticolour (globalRouquierFamily D Sc aR haR ΛR hdegR (LR hdegR)) Sc)
    (h : ∀ (t t' : List I), SKM.wt D 0 (SKM.ups t) = SKM.wt D 0 (SKM.ups t') →
      ∀ (μ : X) (d : ℕ), ∃ O : SwappedVacuumObservation (PiSCat.{u, u, u + 1} k) D Sc cs μ t t' d,
        O.P = globalProbeReservoir D Sc aP haP ΛP hdegP (LP hdegP) aR haR ΛR hdegR (LR hdegR)
          hP hR) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_swapped_vacuum_observations (PiSCat.{u, u, u + 1} k) D Sc cs
    fun t t' hw μ d => (h t t' hw μ d).elim fun O _ => ⟨O⟩

end Field

end OddMath.QuiverHecke
