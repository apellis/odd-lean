/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PairingExtensionPBW
import OddMath.QuiverHecke.SwappedVacuumRecovery

/-! # Recovery in the pairing extension implies recovery for the original datum

`SwappedNondegeneracy.md` §2 builds the swapped action for the pairing
extension `Dₑ` of a Brundan–Ellis datum `D` and pulls it back to `D`. This
module records a shorter consumer: the full-coefficient upward evaluation of
`D` at `μ`, followed by the exact presentation map, equals the upward
evaluation of `Dₑ` at `(μ, 0)` after the coefficient-Hom equivalence. Hence
injectivity at `(μ, 0)` in the extension implies injectivity at `μ`, and
vacuum evaluations for `Dₑ` at the original weights suffice for the
conditional theorem for `D`. No observation quotient needs to be transported back to `D`.
-/
noncomputable section
namespace OddMath.QuiverHecke.PairingExtension
open CategoryTheory StringDiagrams
open scoped TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc
local notation "csₑ" => ReservoirWeights.pairingExtensionCScalars D cs

/-- The upward coefficient evaluation commutes with the pairing extension. -/
theorem homMap_upwardCoefficientMap (μ : X) (t t' : List I)
    (F : coefficientObj (k := k) D Sc t ⟶ coefficientObj (k := k) D Sc t') :
    SKM.PairingExtension.homMap D Sc μ (upWord t) (upWord t')
        (upwardCoefficientMap D Sc cs μ t t' F) =
      upwardCoefficientMap Dₑ Scₑ csₑ (μ, 0) t t' (coefficientHomEquiv D Sc t t' F) := by
  obtain ⟨x, rfl⟩ := (sourceTensorEquiv D Sc t t').surjective F
  induction x using TensorProduct.inductionOn with
  | tmul a f =>
    rw [sourceTensorEquiv_tmul, upwardCoefficientMap_source, coefficientHomEquiv_source,
      upwardCoefficientMap_source, SKM.PairingExtension.homMap_comp,
      SKM.PairingExtension.homMap_bubAt_betaSYM, alpha_map]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Injectivity of the extended upward evaluation at `(μ, 0)` gives it at `μ`. -/
theorem upwardCoefficientMap_injective_of_pairingExtension (μ : X) (t t' : List I)
    (h : Function.Injective (upwardCoefficientMap Dₑ Scₑ csₑ (μ, 0) t t')) :
    Function.Injective (upwardCoefficientMap D Sc cs μ t t') := by
  intro F G hFG
  apply (coefficientHomEquiv D Sc t t').injective
  apply h
  rw [← homMap_upwardCoefficientMap, ← homMap_upwardCoefficientMap, hFG]

end OddMath.QuiverHecke.PairingExtension

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **Conditional theorem through the pairing extension.** Vacuum
evaluations of the swapped action of the pairing extension, at the original
external weights `(μ, 0)`, imply the conjecture for the original datum. -/
theorem nondegeneracy_of_pairingExtension_vacuum_evaluations
    (h : ∀ (t t' : List I), SKM.wt D 0 (SKM.ups t) = SKM.wt D 0 (SKM.ups t') →
      ∀ (μ : X) (d : ℕ), Nonempty (SwappedVacuumEvaluation
        (ReservoirWeights.pairingExtension D) (ReservoirWeights.pairingExtensionScalars D Sc)
        (ReservoirWeights.pairingExtensionCScalars D cs) (μ, 0) t t' d)) :
    SKM.NondegeneracyConjecture cs := by
  apply SKM.nondegeneracy_of_upward_independence cs
  apply upward_independence_of_coefficientMap D Sc cs
  intro t t' hw μ
  exact PairingExtension.upwardCoefficientMap_injective_of_pairingExtension D Sc cs μ t t'
    (upwardCoefficientMap_injective_of_vacuum_evaluations (μ, 0) t t' (h t t' hw μ))

end OddMath.QuiverHecke
