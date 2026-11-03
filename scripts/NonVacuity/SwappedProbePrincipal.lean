import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbePrincipal
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
open CyclotomicCrossingTensor
namespace NonVacuity.SwappedProbePrincipal

local instance homPi (A B : PiSCat.{0, 0, 1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private def highest : Bool → ℤ := fun _ => 20
private theorem cutoff_pairing : ∀ i, (cutoff i : ℤ) = D.h i highest := by
  intro i
  rfl
private def factor := elvRouquierFamily D Sc cutoff bound highest cutoff_pairing

/-- Both factors, their shifted left adjunctions and their multicolour
relations are constructed from the prescribed positive-level ELV family. -/
private def P : ProbeReservoir ℚ (PiSCat.{0, 0, 1} ℚ) D originalSc where
  T := factor
  W := factor
  leftAdj := factor.leftAdjoints
  probeRel := elvRouquierMulticolour D originalSc cutoff bound highest cutoff_pairing
  reservoirRel := elvRouquierMulticolour D originalSc cutoff bound highest cutoff_pairing
  ΛP := highest
  ΛR := highest


private def content : Bool →₀ ℕ := Finsupp.single false 1 + Finsupp.single true 1
private abbrev sector : Sector Bool := (content, content)
private theorem content_weight : contentWeight D content = D.α false + D.α true := by
  rw [content, map_add]
  simp [contentWeight, Finsupp.weight_apply]
private def identityHom : P.H sector := by
  change factor.obj (-(highest - contentWeight D content)) ⟶
    factor.obj (-highest + contentWeight D content)
  have h : -(highest - contentWeight D content) = -highest + contentWeight D content := by abel
  rw [h]
  exact 𝟙 _
private def coeff : P.CrossCoeff where
  a _ _ _ _ := 0
private theorem cup_valid (i : Bool) : StepValid (false, i) true sector := by
  cases i <;> simp [StepValid, content]

/-- The literal probe principal entry uses the constructed left adjunction,
including the prescribed negative crossing, at both odd colours. -/
example (i : Bool) := P.sigmaEntry_probe_mate coeff i 0 sector (cup_valid i) identityHom
example (i : Bool) := P.sigmaEntry_probe_coordinates coeff i 0 sector (cup_valid i) identityHom

example (i : Bool) : homPreGamma (D.parity i) 0 = -1 := by
  cases i <;> decide


/-- Mixed formal contents on the exceptional zero-height slice. -/
private def zeroContent (i : Bool) : Bool →₀ ℕ :=
  Finsupp.single i (if i then 12 else 11) + Finsupp.single (!i) 1
private def zeroSector (i : Bool) : Sector Bool := (zeroContent i, zeroContent i)
private theorem zero_valid (i : Bool) : StepValid (false, i) true (zeroSector i) := by
  cases i <;> simp [StepValid, zeroSector, zeroContent]
private def zeroHom (i : Bool) : P.H (zeroSector i) := by
  change factor.obj (-(highest - contentWeight D (zeroContent i))) ⟶
    factor.obj (-highest + contentWeight D (zeroContent i))
  have h : -(highest - contentWeight D (zeroContent i)) =
      -highest + contentWeight D (zeroContent i) := by abel
  rw [h]
  exact 𝟙 _
private theorem zero_height (i : Bool) : D.h i (-P.muP (zeroSector i)) = 0 := by
  have hw : contentWeight D (zeroContent i) =
      (if i then 12 else 11) • D.α i + D.α (!i) := by
    simp [zeroContent, contentWeight, map_add, Finsupp.weight_single]
  change D.h i (-(highest - contentWeight D (zeroContent i))) = 0
  rw [hw]
  cases i <;> norm_num [D, SKM.Datum.α, AsymmetricParameters.datum, highest]


example (i : Bool) := P.sigmaEntry_probe_coordinates coeff i 0 (zeroSector i)
  (zero_valid i) (zeroHom i)
/-- The exceptional odd sign is retained on the same concrete zero-height sector. -/
example (i : Bool) : homPreGamma (D.parity i) (D.h i (-P.muP (zeroSector i))) = -1 := by
  rw [zero_height]
  cases i <;> decide

private abbrev ν : List Bool := [false, true]
private abbrev σ : List Bool := ν.reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev target := powerWordModule D Sc cutoff L ν
private theorem powers_high (j : Bool × ℕ) : 16 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 16 ≤ 10 * (2 * (j.2 + 1))
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private theorem coordinate_ne_zero : (show target.obj (⟨ν⟩ : C) from
    powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val) ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

/-- This is an actual input object to the identity Hom used in both rows,
with every formal content block retained. -/
private def input : ELVWeightProduct D Sc cutoff bound highest (-highest + contentWeight D content) :=
  PowerWordWeight.wordFamily D Sc cutoff L highest (-highest + contentWeight D content) ν
private def block : WeightBlocks D highest (-highest + contentWeight D content) := by
  refine ⟨(ν : Multiset Bool), ?_⟩
  change (D.α false + (D.α true + 0)) - highest = -highest + contentWeight D content
  rw [content_weight]
  abel
private def wordObject : ContentCategory D Sc cutoff bound (ν : Multiset Bool) := ⟨⟨ν⟩, rfl⟩
private def vector : (input block).obj wordObject :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
example : vector ≠ 0 := coordinate_ne_zero
private theorem input_weight :
    -(highest - contentWeight D content) = -highest + contentWeight D content := by abel
private def actualInput : P.T.obj (-P.muP sector) := input_weight.symm ▸ input
/-- The Hom is tested on the same actual occupied input, transported
only along the computed source-weight identity. -/
example : HEq actualInput input := eqRec_heq _ _
example := identityHom.obj actualInput

end NonVacuity.SwappedProbePrincipal
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbePrincipal
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
