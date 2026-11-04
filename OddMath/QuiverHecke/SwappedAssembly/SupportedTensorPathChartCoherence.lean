import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorUnitObservation
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorContextChartCoherence

/-! # Supported path charts and the global tensor word chart

SwappedVacuumCoordinates §§2–7: the original reservoir-weight path chart
is the global chart after its proved endpoint transport. It agrees with
the prescribed local dot and pair charts in every outer tensor context.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP

private theorem globalChart_word_heq {ν ρ : List I} (h : ν = ρ) :
    HEq (TensorVacuumWords.chart D Tw m cutoff L ΛP ΛR ν).hom
      (TensorVacuumWords.chart D Tw m cutoff L ΛP ΛR ρ).hom := by
  cases h
  rfl

/-- Only the literal label equality is needed to compare a supported path
with a prescribed dot chart in an arbitrary outer context. -/
theorem tensorPathValueChart_dot_heq {l : List (Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hup : ∀ a ∈ l, a.l.1 = true)
    (ν η : List I) (i : I) (hword : (l.map (fun a => a.l.2)).reverse = (ν ++ [i]) ++ η) :
    HEq (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom
      (TensorHomContexts.dotChart D Tw m cutoff L ΛP ΛR ν η i).hom :=
  (tensorPathValueChart_global_heq D Sc m cutoff ΛP ΛR L p hup).trans
    ((globalChart_word_heq D Sc m cutoff ΛP ΛR L hword).trans
      (TensorVacuumWords.dotContextChart_global_heq D Tw m cutoff L ΛP ΛR ν η i).symm)

/-- Supported path and local pair charts agree in every outer context,
for arbitrary colours and original intermediate weights. -/
theorem tensorPathValueChart_pair_heq {l : List (Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hup : ∀ a ∈ l, a.l.1 = true)
    (ν η : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (hword : (l.map (fun a => a.l.2)).reverse = ((ν ++ [j]) ++ [i]) ++ η) :
    HEq (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom
      (TensorHomContexts.pairChart D Tw m cutoff L ΛP ΛR ν η i j h₁ h₂).hom :=
  (tensorPathValueChart_global_heq D Sc m cutoff ΛP ΛR L p hup).trans
    ((globalChart_word_heq D Sc m cutoff ΛP ΛR L hword).trans
      (TensorVacuumWords.pairContextChart_global_heq D Tw m cutoff L ΛP ΛR ν η i j h₁ h₂).symm)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
