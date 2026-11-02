import OddMath.QuiverHecke.HalfTurn.Homogeneous
import OddMath.QuiverHecke.HalfTurn.QuotientEquivalence

/-! The actual contextual half-turn and quotient equivalence at two odd colours
with a nonzero interior mixed-quadratic/corrected-braid coefficient s(2,2).
The full exterior factor is retained, and contributes to composition signs.
-/
noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurnHomogeneous
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke

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

private def sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ p q => if p = 2 ∧ q = 2 then 2 else 0
  s_symm := by intros; simp only [and_comm]
  s_eq_zero := by
    intro i j p q hp
    split_ifs with h
    · obtain ⟨rfl, _⟩ := h
      have hz : (2 : ZMod 2) * D.parity i = 0 := rfl
      exact False.elim (zero_ne_one (hz.symm.trans hp))
    · rfl
  two_isUnit := by intro _; norm_num

private theorem dn_false_true : D.dn false true = 4 := by
  norm_num [SKM.Datum.dn, SKM.Datum.d, D, SKM.Datum.h, SKM.Datum.α]

/-- The interior term is occupied in both directions; leading terms do not
subsume this correction. -/
example : 0 < 2 ∧ 2 < D.dn false true ∧ 0 < 2 ∧ 2 < D.dn true false ∧
    sc.s false true 2 2 = (2 : ℚ) := by
  norm_num [SKM.Datum.dn, SKM.Datum.d, D, SKM.Datum.h, SKM.Datum.α, sc]

/-- The target parameter is different, as prescribed by signed reversal. -/
example : (parameterTwist D sc).s false true 2 2 = (-2 : ℚ) := by
  rw [parameterTwist_s]
  norm_num [parameterSignExponent, D, sc, SKM.zsign]

example : (mirrorLin D sc).map ((pres D sc).rel (.quadNe false true (by decide) (by decide))) = 0 :=
  mirror_rel_quadNe D sc false true (by decide) (by decide)

example := mirror_rel_braidEq D sc false true (by decide)
example := flip_rel_braidEq D sc false true (by decide)

/-- This is the descended functor through the entire contextual presentation
ideal, not a map that assumes local relation compatibility. -/
example : (pres D sc).Presented ⥤ SOp ℚ (pres D (parameterTwist D sc)).Presented :=
  halfTurnFunctor D sc

example (u v : List Bool) := halfTurn_cross D sc u false false v

private def δ (i : Bool) : SKM.SYM D ℚ := SKM.SYM.delta D ℚ ⟨i, rfl⟩
private theorem hδ (i : Bool) : CoefParity D 1 (δ i) := coefParity_delta D ⟨i, rfl⟩

/-- Two odd full coefficients on even identities give the super-opposite minus
sign; affine-only parity would incorrectly give a plus. -/
example (s : List Bool) :
    htCoef D sc s s
      (sourceCoefficientHom D sc (δ false) (𝟙 _) ≫
        sourceCoefficientHom D sc (δ true) (𝟙 _)) =
      (-1 : ℚ) • (htCoef D sc s s (sourceCoefficientHom D sc (δ true) (𝟙 _)) ≫
        htCoef D sc s s (sourceCoefficientHom D sc (δ false) (𝟙 _))) := by
  have hm (i : Bool) : sourceCoefficientHom D sc (δ i) (𝟙 ((pres D sc).obj (ob D s))) ∈
      parity (R := ℚ) _ _ 1 := by
    simpa only [add_zero] using sourceCoefficientHom_mem_parity D sc (hδ i) (id_mem _)
  have h := htCoef_comp D sc (hm false) (hm true)
  rw [show SKM.zsign ℚ (1 * 1) = (-1 : ℚ) from rfl] at h
  exact h

example {s t : List Bool} {p : ZMod 2}
    {x : coefficientObj D sc s ⟶ coefficientObj D sc t}
    (hx : x ∈ parity (R := ℚ) _ _ p) := htCoef_mem_parity D sc hx

private def T : Set (SKM.SYM D ℚ) := {SKM.SYM.e D ℚ false 1, δ true}
private theorem hT : ∀ a ∈ T, ∃ p, CoefParity D p a := by
  rintro a (rfl | rfl)
  · exact ⟨0, coefParity_e D false 1⟩
  · exact ⟨1, hδ true⟩

/-- The literal boundary quotient equivalence also keeps an odd specified
coefficient generator. Source and target have their distinct boundary ideals. -/
example := halfTurnQuotientEquiv D sc (fun _ => 4) T hT [false, true, false] [false, true, false]

example (x : coefficientObj D sc [false, true] ⟶ coefficientObj D sc [false, true]) :=
  halfTurnQuotientEquiv_mk D sc (fun _ => 4) T hT [false, true] [false, true] x

end NonVacuity.QuiverHeckeHalfTurnHomogeneous

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.HalfTurn.Mirror,
    `OddMath.QuiverHecke.HalfTurn.SuperFlip, `OddMath.QuiverHecke.HalfTurn.Composite,
    `OddMath.QuiverHecke.HalfTurn.CornerIdeal, `OddMath.QuiverHecke.HalfTurn.Involution,
    `OddMath.QuiverHecke.HalfTurn.IdealIdentification,
    `OddMath.QuiverHecke.HalfTurn.CoefficientGenerators,
    `OddMath.QuiverHecke.HalfTurn.Homogeneous,
    `OddMath.QuiverHecke.HalfTurn.QuotientEquivalence]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty owned declaration inventory for {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} owned declarations in {owner}, including private/generated"
