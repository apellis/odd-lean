import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientAction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
open SupportedSectors
namespace NonVacuity.SupportedTensorCoefficientAction
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 20
private def m (i : Bool) : ℕ := if i then 2 else 1
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev Λ : Bool → ℤ := 0
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev Tw := parameterTwist D Sc
private abbrev Z := tensorVacuum D Sc m cutoff L Λ Λ
private abbrev action := tensorVacuumCoefficientAction D Sc m cutoff L Λ Λ
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 10 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private def elementaryClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.e D ℚ i 0)

private theorem window_ne_zero {d : ℕ} (hd : d < 4) (a : SKM.SYM D ℚ)
    (ha : a ∈ SKM.SYM.CoefficientAtMost D ℚ d) (h0 : a ≠ 0) :
    coefficientPowerQuotientMap D cutoff L a ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L d 4 hd large powers_high
  have he := hi (a₁ := ⟨a, ha⟩) (a₂ := 0)
    (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  exact h0 (congrArg Subtype.val he)

private abbrev OddColour := {i : Bool // D.parity i = 1}
private def i₀ : OddColour := ⟨false, rfl⟩
private def i₁ : OddColour := ⟨true, rfl⟩

private theorem exterior_product_ne_zero :
    SKM.SYM.oddExteriorBasis D ℚ {i₀} * SKM.SYM.oddExteriorBasis D ℚ {i₁} ≠ 0 := by
  classical
  let : LinearOrder OddColour := WellOrderingRel.isWellOrder.linearOrder
  let ss := Set.powersetCard.ofCard (Finset.card_singleton i₀)
  let tt := Set.powersetCard.ofCard (Finset.card_singleton i₁)
  have hd : Disjoint ss.val tt.val := by
    change Disjoint ({i₀} : Finset OddColour) {i₁}
    simp only [Finset.disjoint_singleton]
    intro he
    have := congrArg Subtype.val he
    cases this
  have he := ExteriorAlgebra.basis_mul_of_disjoint
    (Finsupp.basisSingleOne : Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)) ss tt hd
  have hb := (Finsupp.basisSingleOne :
    Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra.ne_zero
      (Set.powersetCard.disjUnion hd)
  intro hz
  change (Finsupp.basisSingleOne :
      Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra ss *
    (Finsupp.basisSingleOne :
      Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra tt = 0 at hz
  have hh := he.symm.trans hz
  rw [Units.smul_def] at hh
  exact hb ((Units.isUnit (Set.powersetCard.permOfDisjoint hd).sign).smul_eq_zero.mp hh)

private theorem source_product_ne_zero :
    SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ≠ 0 := by
  intro hz
  have he := congrArg (SKM.SYM.exteriorProjection D ℚ) hz
  simp only [map_mul, SKM.SYM.exteriorProjection_delta, map_zero] at he
  apply exterior_product_ne_zero
  simpa only [SKM.SYM.oddExteriorBasis_singleton] using he

private theorem product_ne_zero : deltaClass false * deltaClass true ≠ 0 := by
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₀) *
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁) ≠ 0
  rw [← map_mul]
  have hm : SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ∈
      SKM.SYM.CoefficientAtMost D ℚ 2 :=
    SKM.SYM.coefficientAtMost_mul D ℚ (m := 1) (n := 1)
      (x := SKM.SYM.delta D ℚ i₀) (y := SKM.SYM.delta D ℚ i₁)
      (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀) (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  exact window_ne_zero (by decide : 2 < 4) _ hm source_product_ne_zero


private abbrev rawZ := WeightTensorVacuum.selectedHom D Tw m cutoff Λ Λ L
private abbrev P₀ := WeightTensorVacuum.regularProbe D Tw m Λ
private abbrev W := ReservoirWordValue.initialValue D Λ Tw cutoff L
private abbrev E := coefficientPowerVacuumEmptyEquiv D Tw cutoff L
private abbrev empty : OldCategory D Tw cutoff := ⟨[]⟩
private def β : WeightBlocks D Λ (ReservoirWord.weight D Λ 0) := ⟨0, by simp [ReservoirWord.weight]⟩
private def star : ContentCategory D Tw cutoff N (0 : Multiset Bool) := ⟨⟨[]⟩, rfl⟩
private def tensorOdd : ((rawZ.obj P₀) β).obj star :=
  WeightTensorVacuum.tensorVector D Tw m cutoff N Λ Λ W β star (E (deltaClass true))
private def rawActed : ((rawZ.obj P₀) β).obj star :=
  (((VacuumTensorCoefficientMaps.sourceCoefficientAction D Tw m cutoff L Λ Λ
    (SYM.delta D ℚ i₀)).total P₀) β).total star tensorOdd
private theorem rawActed_ne_zero : rawActed ≠ 0 := by
  have h : ((WeightTensorVacuum.selectedIso D Tw m cutoff Λ Λ L).hom β).total star rawActed =
      E (deltaClass false * deltaClass true) := by
    rw [rawActed, tensorOdd, VacuumTensorCoefficientMaps.sourceCoefficientAction_tensorVector]
    change (vacuumCoefficientAction D Tw cutoff L (deltaClass false)).total empty
      (E (deltaClass true)) = E (deltaClass false * deltaClass true)
    exact vacuumCoefficientAction_empty D Tw cutoff L _ _
  intro hz
  rw [hz, map_zero] at h
  exact product_ne_zero (E.injective (h.symm.trans E.map_zero.symm))

/-- The literal supported tensor vacuum carries a nonzero odd coefficient action,
certified by applying it to a vector containing the other odd colour. -/
example : action (SYM.delta D ℚ i₀) ≠ 0 := by
  apply tensorVacuumCoefficientAction_ne_zero D Sc m cutoff L Λ Λ
  intro hz
  have h := congrArg (fun f => moduleFamilyEndEvaluation rawZ P₀ β star f tensorOdd) hz
  rw [map_zero, LinearMap.zero_apply] at h
  exact rawActed_ne_zero h

example : SYM D ℚ →ₐ[ℚ] End Z := action
example (a b : SYM D ℚ) : action (a * b) = action a * action b := map_mul _ a b
example : action (SYM.delta D ℚ i₀ * SYM.delta D ℚ i₁) =
    -action (SYM.delta D ℚ i₁ * SYM.delta D ℚ i₀) := by
  rw [SYM.delta_anticommute, map_neg]
example (s : List Bool) : SYM D ℚ →ₐ[ℚ] End (tensorSourceObject D Sc m cutoff Λ Λ L s) :=
  tensorSourceCoefficientAction D Sc m cutoff L Λ Λ s

example {l : List (Col Bool (Bool → ℤ))} {s : Sector Bool}
    (p : SPath l s (0,0)) (G : H D Tw m cutoff N Λ Λ s)
    (a : SYM D ℚ) (f : G ⟶ (pathFunctor D Tw m cutoff N Λ Λ p).obj Z) :
    tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G a f =
      f ≫ tensorPathCoefficientAction D Sc m cutoff L Λ Λ p a :=
  tensorWordHomCoefficientAction_apply D Sc m cutoff L Λ Λ p G a f

/-- The induced word-Hom action preserves the original multiplication,
including products of independent odd source coefficients. -/
example {l : List (Col Bool (Bool → ℤ))} {s : Sector Bool}
    (p : SPath l s (0,0)) (G : H D Tw m cutoff N Λ Λ s) (a b : SYM D ℚ) :
    tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G (a * b) =
      tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G a *
        tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G b := map_mul _ a b
example {l : List (Col Bool (Bool → ℤ))} {s t : Sector Bool}
    (p : SPath l s t) (sourceWord : List Bool) (a : SYM D ℚ)
    (f : tensorSourceFamily D Sc m cutoff Λ Λ L sourceWord s ⟶
      (pathFunctor D Tw m cutoff N Λ Λ p).obj (tensorTargetFamily D Sc m cutoff Λ Λ L t)) :
    tensorFamilyWordHomCoefficientAction D Sc m cutoff L Λ Λ p sourceWord a f =
      f ≫ tensorFamilyPathCoefficientAction D Sc m cutoff L Λ Λ p a :=
  tensorFamilyWordHomCoefficientAction_apply D Sc m cutoff L Λ Λ p sourceWord a f

end NonVacuity.SupportedTensorCoefficientAction
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientAction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
