import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordMorphisms
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! The actual A/T word Hom chart retains arbitrary coefficient vectors.
The odd component acts on a second exterior colour with its required sign. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVPowerWordMorphisms
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private def ν : List Bool := [false, true]
private abbrev C := OldCategory D Sc cutoff
private abbrev v : C := ⟨[]⟩
private abbrev M := coefficientPowerVacuumObject D Sc cutoff L
private abbrev E := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
private def delta (i : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private abbrev Q := (coefficientPowerIdeal D cutoff
  (elementaryCoefficients (k := ℚ) D cutoff) L).ringCon.mkₐ ℚ

example (s t : List Bool) (g : (⟨t⟩ : C) ⟶ ⟨s⟩) (p : ZMod 2) (w : C)
    (h : (⟨s⟩ : C) ⟶ w) (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  PowerWordMorphisms.fromArrow_tensor D Sc cutoff L s t g p w h a
example (s t : List Bool) (g : (⟨t⟩ : C) ⟶ ⟨s⟩) (p : ZMod 2)
    (hg : g ∈ parity (R := ℚ) (⟨t⟩ : C) ⟨s⟩ p) :=
  PowerWordMorphisms.fromArrow_eq_transform D Sc cutoff L s t g hg
example (g f : (⟨ν⟩ : C) ⟶ ⟨ν⟩) (p : ZMod 2) :=
  PowerWordMorphisms.composition_generator D Sc cutoff L ν ν ν g f p

private theorem delta_mem (i : Bool) : delta i ∈ SKM.SYM.elvCoefficientParity D cutoff 1 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_delta_mem_odd D (k := ℚ) ⟨i, rfl⟩)
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, delta] using h

private theorem m_odd (i : Bool) : E (Q (delta i)) ∈ (M.obj.obj v).part 1 :=
  coefficientPowerVacuumEmptyEquiv_mem D Sc cutoff L
    (coefficientPowerQuotient_mem D cutoff L (delta_mem i))

private theorem vacuum_action (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff)
    (b : CoefficientPowerQuotient (k := ℚ) D cutoff L) :
    M.obj.map (coefficientEndomorphism D Sc cutoff [] a) (E b) = E (Q a * b) := by
  let J := powerCoefficientEmbedding D Sc cutoff
  let R := (liftedPowerRegular (k := ℚ) D cutoff L).toFunctor
  let f : powerCoefficientStar D cutoff ⟶ powerCoefficientStar D cutoff := a
  change BalancedInduction.postcompose J R (J.map f)
    (BalancedInduction.tensor J R (powerCoefficientStar D cutoff)
      (𝟙 (J.obj (powerCoefficientStar D cutoff))) b) =
    BalancedInduction.tensor J R (powerCoefficientStar D cutoff)
      (𝟙 (J.obj (powerCoefficientStar D cutoff))) (Q a * b)
  rw [BalancedInduction.postcompose_tensor, Category.id_comp]
  have hb := BalancedInduction.balance J R f (𝟙 (J.obj (powerCoefficientStar D cutoff))) b
  rw [Category.comp_id] at hb
  exact hb

private abbrev OddColour := {i : Bool // D.parity i = 1}
private def i₀ : OddColour := ⟨true, rfl⟩
private def i₁ : OddColour := ⟨false, rfl⟩

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

private theorem powers_high (j : Bool × ℕ) : 4 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 4 ≤ 4 * (2 * (j.2 + 1))
  omega

private theorem power_product_ne_zero : Q (delta true) * Q (delta false) ≠ 0 := by
  have hm := SKM.SYM.coefficientAtMost_mul D ℚ
    (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀)
    (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  intro hz
  have he : coefficientPowerQuotientMap (k := ℚ) D cutoff L
      (SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁) = 0 := by
    simpa only [coefficientPowerQuotientMap, AlgHom.comp_apply, map_mul, delta, i₀, i₁] using hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 2 4 (by decide)
    (fun _ => by rfl) powers_high
  have hh := hi (a₁ := ⟨_, hm⟩) (a₂ := 0) he
  exact source_product_ne_zero (congrArg Subtype.val hh)

/-- The extra odd coefficient contributes its sign even though h is even. -/
private theorem odd_chart :
    (PowerWordYoneda.fromElement D Sc cutoff L [] M (E (Q (delta false)))).app 1 v
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff [])
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        (𝟙 v) (Q (delta true))) =
      (-1 : ℚ) • E (Q (delta true) * Q (delta false)) := by
  rw [PowerWordYoneda.fromElement_tensor, Category.comp_id,
    twist_of_mem 1 (coefficientEndomorphism_mem D Sc cutoff [] (delta_mem true)),
    one_mul, sign_one]
  change M.obj.map ((-1 : ℚ) • coefficientEndomorphism D Sc cutoff [] (delta true))
    ((M.obj.obj v).proj 1 (E (Q (delta false)))) = _
  rw [SVec.proj_apply_of_mem_part _ (m_odd false), ite_eq_left rfl]
  simp only [Superfunctor.map, Functor.map_smul, SVec.smul_apply]
  exact congrArg (fun x => (-1 : ℚ) • x) (vacuum_action (delta true) (Q (delta false)))

/-- The sign test is occupied: the two exterior colours survive all old
and literal power relations in the actual target module. -/
example :
    (PowerWordYoneda.fromElement D Sc cutoff L [] M (E (Q (delta false)))).app 1 v
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff [])
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        (𝟙 v) (Q (delta true))) ≠ 0 := by
  rw [odd_chart]
  intro hz
  have he : E (Q (delta true) * Q (delta false)) = 0 :=
    (smul_eq_zero.mp hz).resolve_left (by norm_num)
  exact power_product_ne_zero (E.injective (he.trans E.map_zero.symm))


private theorem native_delta_chart (i : Bool) :
    PowerWordMorphisms.fromArrow D Sc cutoff L [] []
      (coefficientEndomorphism D Sc cutoff [] (delta i)) =
    PowerWordYoneda.fromElement D Sc cutoff L [] M (E (Q (delta i))) := by
  unfold PowerWordMorphisms.fromArrow
  have he := PowerWordYoneda.tensor_eq_generator D Sc cutoff L [] v (𝟙 v) (delta i)
  rw [Category.comp_id] at he
  change E (Q (delta i)) = powerWordGenerator D Sc cutoff L [] v
    (coefficientEndomorphism D Sc cutoff [] (delta i)) at he
  rw [← he]
  rfl

/-- The literal induced native odd coefficient map has the occupied
super-opposite sign on the second exterior colour. -/
example :
    (PowerWordMorphisms.fromArrow D Sc cutoff L [] []
      (coefficientEndomorphism D Sc cutoff [] (delta false))).app 1 v
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff [])
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        (𝟙 v) (Q (delta true))) =
      (-1 : ℚ) • E (Q (delta true) * Q (delta false)) := by
  rw [native_delta_chart]
  exact odd_chart

example :
    (PowerWordMorphisms.fromArrow D Sc cutoff L [] []
      (coefficientEndomorphism D Sc cutoff [] (delta false))).app 1 v
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff [])
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        (𝟙 v) (Q (delta true))) ≠ 0 := by
  rw [native_delta_chart]
  intro hz
  have hz' : (-1 : ℚ) • E (Q (delta true) * Q (delta false)) = 0 := odd_chart.symm.trans hz
  have he : E (Q (delta true) * Q (delta false)) = 0 :=
    (smul_eq_zero.mp hz').resolve_left (by norm_num)
  exact power_product_ne_zero (E.injective (he.trans E.map_zero.symm))

end NonVacuity.ELVPowerWordMorphisms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordMorphisms | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
