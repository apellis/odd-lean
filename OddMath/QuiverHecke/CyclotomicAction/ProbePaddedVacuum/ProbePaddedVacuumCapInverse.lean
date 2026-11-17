import Mathlib.Tactic.Abel
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier.GlobalWeightCross
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.CapWindows
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWordSeries
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseBubbleEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCupInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseRightBubbleEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumCapInverseWindow
import OddMath.SKM.RouquierHomWeightCoordinates

/-!
# Probe padded vacuum

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The chosen vacuum cap inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At formal content zero and positive height, the actual positive augmented factor
matrix of the supported vacuum sector has a cap-window inverse
(`SupportedSectors.vacuumCapInverseData`). This file transports that inverse,
entry by entry, to the native chart of the regular vacuum probe: its principal map
becomes the evaluated A6 bend `evaluatedMixedBend` (odd colour, through
`paddedVacuumDx_odd`) and its windows become the native rows `x ^ n ≫ v`
(`paddedVacuumCap_eq`). The result `vacuumCapInverse_odd` is a cap
inverse of exactly the window used by `tensorVacuumCapInverse_odd_moments`.

The transport uses only additive evaluation (`IsCapInverse.map`), the corner
charts (`IsCapInverse.coordinates`) and a change of the common window target
(`IsCapInverse.target`). No inverse, moment or bubble value is assumed.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.SwappedAssembly

namespace ProbeWindow

variable {C : Type*} [Category C] [Preadditive C]
  {X Y O O' : C} {n : ℕ} {s : X ⟶ Y} {v : Fin n → (X ⟶ O)}
  {j : Y ⟶ X} {A : Fin n → (O ⟶ X)}

/-- An isomorphism of the common window target transports a cap inverse. -/
theorem IsCapInverse.target (H : IsCapInverse s v j A) (c : O ≅ O') :
    IsCapInverse s (fun r => v r ≫ c.hom) j (fun r => c.inv ≫ A r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, fun r => ?_, fun r => ?_, fun r t => ?_, ?_⟩
  · rw [Category.assoc, h2 r, Limits.comp_zero]
  · rw [← Category.assoc, h3 r, Limits.zero_comp]
  · rw [Category.assoc, reassoc_of% (h4 r t)]
    split_ifs <;> simp
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h5

end ProbeWindow

namespace ProbeReservoir

open OddMath.SKM Classical
open scoped ZeroObject

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
variable (P : ProbeReservoir k B D Sc)
variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  {C' : Type*} [Category C'] [Preadditive C'] [Limits.HasZeroObject C']

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly

namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance paddedVacuumCapInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedVacuumCapInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
  (hwin : SupportedSectors.ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hcP hcR) (i : I)

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
