import OddMath.SKM.PolynomialExteriorSupercomm
import OddMath.SKM.BubbleCoefficientGenerators

/-! Full exterior coefficients satisfy the homogeneous commutation law, and
its odd/odd sign is detected by a nonzero product of two different generators. -/
noncomputable section
open OddMath
namespace NonVacuity.PolynomialExteriorSupercomm

private def D : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -4
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -4)
    split
    · exact ⟨1, rfl⟩
    · exact ⟨-2, rfl⟩

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


private def δ (i : OddColour) := SKM.SYM.polynomialExteriorEquiv D ℚ (SKM.SYM.delta D ℚ i)

/-- Both odd coefficients remain in the full algebra and anticommute. -/
example : δ i₀ * δ i₁ = (-1 : ℚ) • (δ i₁ * δ i₀) := by
  have h := SKM.SYM.polynomialExteriorParity_supercomm D
    (SKM.SYM.polynomialExterior_delta_mem_odd D ℚ i₀)
    (SKM.SYM.polynomialExterior_delta_mem_odd D ℚ i₁)
  rw [show SKM.zsign ℚ (1 * 1) = (-1 : ℚ) from rfl] at h
  exact h

/-- The sign test is occupied: the odd/odd product is nonzero. -/
example : δ i₀ * δ i₁ ≠ 0 := by
  intro hz
  apply source_product_ne_zero
  apply (SKM.SYM.polynomialExteriorEquiv D ℚ).injective
  simpa only [map_mul, map_zero, δ] using hz

/-- An even coefficient commutes with an arbitrary odd homogeneous coefficient. -/
example (b : SKM.SYM.PolynomialExterior D ℚ)
    (hb : b ∈ SKM.SYM.polynomialExteriorParity D ℚ 1) :
    SKM.SYM.polynomialExteriorEquiv D ℚ (SKM.SYM.e D ℚ false 1) * b =
      b * SKM.SYM.polynomialExteriorEquiv D ℚ (SKM.SYM.e D ℚ false 1) := by
  simpa [SKM.zsign] using
    SKM.SYM.polynomialExteriorParity_supercomm D
      (SKM.SYM.polynomialExterior_e_mem_even D ℚ false 1) hb

end NonVacuity.PolynomialExteriorSupercomm

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.PolynomialExteriorSupercomm
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
