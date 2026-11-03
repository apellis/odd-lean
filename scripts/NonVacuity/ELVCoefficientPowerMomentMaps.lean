import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerMomentMaps
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
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

/-- The entire closed even series is checked as actual endomorphisms,
including all inhomogeneous coefficient vectors, at both cutoff parities. -/
example (i : Bool) (r : ℕ) :
    momentMap D Sc cutoff L i (positive i) (cutoff i - 1 + 2 * r) =
      LinearMap.mulLeft ℚ (completeCoefficient D cutoff L i r) :=
  momentMap_even D Sc cutoff L i rfl (positive i) r

example (i : Bool) (r : ℕ) :
    momentMap D Sc cutoff L i (positive i) (cutoff i - 1 + (2 * r + 1)) =
      LinearMap.mulLeft ℚ ((-1 : ℚ) ^ (cutoff i + 1) •
        (deltaClass i * completeCoefficient D cutoff L i r)) :=
  momentMap_odd D Sc cutoff L i rfl (positive i) r

/-- The first higher map is odd for each cutoff, even though the two
cutoff parities give opposite exterior normalization scalars. -/
example (i : Bool) : momentMap D Sc cutoff L i (positive i) (cutoff i) ∈
    parity (R := ℚ) (coefficientPowerSpace D cutoff L) (coefficientPowerSpace D cutoff L) 1 := by
  have h := momentMap_mem D Sc cutoff L i (positive i) (cutoff i)
  have hp : (cutoff i + (cutoff i - 1)) • D.parity i = (1 : ZMod 2) := by
    cases i <;> decide
  simpa only [hp] using h

private theorem first_false (z : AQ) :
    momentMap D Sc cutoff L false (positive false) 4 z = -(deltaClass false * z) := by
  have h := LinearMap.congr_fun (momentMap_first_odd D Sc cutoff L false rfl (positive false)) z
  change momentMap D Sc cutoff L false (positive false) 4 z =
    (((-1 : ℚ) ^ 5) • deltaClass false) * z at h
  rw [show (-1 : ℚ) ^ 5 = -1 by norm_num, smul_mul_assoc] at h
  exact h.trans (neg_one_smul ℚ (deltaClass false * z))

private theorem first_true (z : AQ) :
    momentMap D Sc cutoff L true (positive true) 5 z = deltaClass true * z := by
  have h := LinearMap.congr_fun (momentMap_first_odd D Sc cutoff L true rfl (positive true)) z
  change momentMap D Sc cutoff L true (positive true) 5 z =
    (((-1 : ℚ) ^ 6) • deltaClass true) * z at h
  rw [show (-1 : ℚ) ^ 6 = 1 by norm_num, one_smul] at h
  exact h

private theorem anti : deltaClass true * deltaClass false = -(deltaClass false * deltaClass true) := by
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁) *
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₀) = _
  rw [← map_mul, SKM.SYM.delta_anticommute, map_neg, map_mul]
  rfl

/-- An odd input in a different exterior direction detects the original
left multiplication order; its value is proved nonzero. -/
example : momentMap D Sc cutoff L false (positive false) 4 (deltaClass true) =
    -(deltaClass false * deltaClass true) := first_false _

example : momentMap D Sc cutoff L false (positive false) 4 (deltaClass true) ≠ 0 := by
  rw [first_false, neg_ne_zero]
  exact product_ne_zero

example : momentMap D Sc cutoff L true (positive true) 5 (deltaClass false) =
    -(deltaClass false * deltaClass true) := by
  rw [first_true, anti]

/-- The operator identity also acts on inhomogeneous inputs;
no homogeneous-vector premise is added to the full moment theorem. -/
example : momentMap D Sc cutoff L false (positive false) 4 (1 + deltaClass true) =
    -deltaClass false - deltaClass false * deltaClass true := by
  rw [first_false]
  noncomm_ring

example : momentMap D Sc cutoff L true (positive true) 5 (1 + deltaClass false) =
    deltaClass true - deltaClass false * deltaClass true := by
  rw [first_true, mul_add, mul_one, anti, sub_eq_add_neg]

private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { D with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => D.even_of_odd i j rfl }
private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

/-- The all-vector identity also retains the even moving-colour case in
an actual mixed datum, at every exponent and every coefficient vector. -/
example (n : ℕ) (z : CoefficientPowerQuotient (k := ℚ) mixedDatum cutoff L) :
    momentMap mixedDatum mixedScalars cutoff L false (positive false) n z =
      signedMoment mixedDatum mixedScalars cutoff L false (positive false) n * z :=
  momentMap_apply mixedDatum mixedScalars cutoff L false (positive false) n z

end NonVacuity.ELVCoefficientPowerMomentMaps

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMomentMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
