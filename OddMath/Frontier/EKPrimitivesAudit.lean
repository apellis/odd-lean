import OddMath.Frontier.EKPrimitives
import OddMath.Frontier.EKPrimitivesControls

/-! Audit of EK1107.5610v2 §3.2 p25 Proposition 3.3.

* exact exported types on actual `Q`, actual `quotientCoproduct`, actual `mBasis`;
* the pre-production controls are consumed and CLOSED here against production
  (`m4PrimitiveTarget`, fixed before production, is discharged by production);
* negative controls: `m_(3)` (EK's `p_3`) is NOT primitive; `h_2` is not primitive;
* every owned declaration (production, controls, audit, incl. compiler-named
  helpers) is checked to depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct BigOperators
open OddMath.Frontier EKRadicalQuotient EKCoideal EKElementaryQuotient EKDualBases
  EKIntegralBases DegreeShapes EKPrimitives
namespace OddMath.Frontier.EKPrimitivesAudit

-- Exact carrier and predicate: no substituted algebra, no assumed coproduct law.
example : Q = (CompleteElementary.A ⧸ EKRadicalQuotient.radical) := rfl
example (x : Q) : IsPrimitive x ↔
    quotientCoproduct x = (1 : Q) ⊗ₜ[ℤ] x + x ⊗ₜ[ℤ] (1 : Q) := Iff.rfl
example (x : Q) : IsPrimitive x ↔ EKPrimitivesControls.IsPrim x := Iff.rfl
example (n : ℕ) : mRow n = mBasis n (rowShape n) := rfl
example (n : ℕ) (hn : 0 < n) : (rowShape n).val.rowLens = [n] := rowShape_rows hn

-- The exact frozen statement.
example (n : ℕ) (hpos : 1 ≤ n) (x : degreePiece n) :
    ((n = 1 ∨ Even n) → (IsPrimitive x.val ↔ x ∈ ℤ ∙ mBasis n (rowShape n))) ∧
    ((Odd n ∧ 3 ≤ n) → (IsPrimitive x.val ↔ x = 0)) := proposition_3_3 n hpos x

-- I² ∩ Λ_n, all three regimes.
example (x : degreePiece 1) : x.val ∈ posIdealSq ↔ x = 0 := sq_degree_one_iff x
example (x : degreePiece 1) (c : ℤ) (hc : c ≠ 0) (hx : c • x.val ∈ posIdealSq) : x = 0 :=
  sq_degree_one x c hc hx
example (n : ℕ) (hpos : 0 < n) (he : Even n) (x : degreePiece n) :
    x.val ∈ posIdealSq ↔ x ∈ Submodule.span ℤ (degreeHBasis n '' {μ | μ ≠ rowShape n}) :=
  sq_even_iff n hpos he x
example (n : ℕ) (hpos : 0 < n) (he : Even n) (x : degreePiece n) :
    (∃ c : ℤ, c ≠ 0 ∧ c • x.val ∈ posIdealSq) ↔ x ∈ nonRowSpan n :=
  sq_even_saturated_iff n hpos he x
example (n : ℕ) (hodd : Odd n) (h3 : 3 ≤ n) (x : degreePiece n) :
    (2 : ℤ) • x.val ∈ posIdealSq := sq_odd_two_smul n hodd h3 x

/-! ### Closing the pre-production controls against production -/

theorem row4_eq : EKPrimitivesControls.row4 = rowShape 4 := rfl

/-- The degree-4 target fixed BEFORE production, discharged by production. -/
theorem m4_primitive_closed : EKPrimitivesControls.m4PrimitiveTarget := by
  unfold EKPrimitivesControls.m4PrimitiveTarget
  rw [row4_eq]
  exact mRow_primitive 4 (Or.inr ⟨2, rfl⟩) (by norm_num)

/-- Degree 1 agreement: hand control `m₁ = h₁` versus production. -/
theorem m1_agree : IsPrimitive (mRow 1).val := mRow_primitive 1 (Or.inl rfl) (by norm_num)

/-- Degree 2 agreement: production recovers the hand control `m₂ = h₁h₁` primitive. -/
theorem m2_agree : IsPrimitive (mRow 2).val := mRow_primitive 2 (Or.inr ⟨1, rfl⟩) (by norm_num)

theorem m2_hand_eq : (mRow 2 : Q) = h 1 * h 1 := by
  have e : rowShape 2 = EKDualBasesControls.row2 := by
    apply eq_rowShape (by norm_num)
    exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
  rw [mRow, e, EKDualBasesControls.degree_two_duals.1]

/-- Degree 3 agreement: production and the hand control both say no nonzero primitive. -/
theorem degree_three_agree (x : degreePiece 3) :
    (IsPrimitive x.val ↔ x = 0) :=
  primitive_iff_zero 3 ⟨1, rfl⟩ (le_refl 3) x

/-- Negative control: EK's `p₃ = m₃` is NOT primitive (it is a nonzero basis vector). -/
theorem m3_not_primitive : ¬ IsPrimitive (mRow 3).val := by
  intro hp
  have := (primitive_iff_zero 3 ⟨1, rfl⟩ (le_refl 3) (mRow 3)).mp hp
  exact (mBasis 3).ne_zero (rowShape 3) this

/-- Negative control, consumed from the pre-production file. -/
theorem h2_not_primitive : ¬ IsPrimitive (h 2) := EKPrimitivesControls.h2_not_primitive

/-- Upper bound agreement in degree 4: the control's coefficient matches production's. -/
theorem degree_four_agree (x : degreePiece 4) (hx : IsPrimitive x.val) :
    x = quotientPairing (h 4) x.val • mRow 4 :=
  primitive_upper (by norm_num) x hx

end OddMath.Frontier.EKPrimitivesAudit

#check @EKPrimitives.proposition_3_3
#check @EKPrimitives.primitive_iff_span
#check @EKPrimitives.primitive_iff_zero
#check @EKPrimitives.mRow_primitive
#check @EKPrimitives.sq_degree_one_iff
#check @EKPrimitives.sq_even_iff
#check @EKPrimitives.sq_even_saturated_iff
#check @EKPrimitives.sq_odd_two_smul
#print axioms EKPrimitives.proposition_3_3
#print axioms EKPrimitives.sq_degree_one_iff
#print axioms EKPrimitives.sq_even_saturated_iff
#print axioms EKPrimitives.sq_odd_saturated
#print axioms EKPrimitivesAudit.m4_primitive_closed

-- All owned safe declarations are audited, INCLUDING private/compiler-named helpers.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKPrimitives,
        `OddMath.Frontier.EKPrimitivesControls,
        `OddMath.Frontier.EKPrimitivesAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``EKPrimitives.IsPrimitive, ``EKPrimitives.proposition_3_3,
      ``EKPrimitives.primitive_iff_span, ``EKPrimitives.primitive_iff_zero,
      ``EKPrimitives.mRow_primitive, ``EKPrimitives.primitive_upper,
      ``EKPrimitives.posIdeal, ``EKPrimitives.posIdealSq,
      ``EKPrimitives.sq_degree_one, ``EKPrimitives.sq_degree_one_iff,
      ``EKPrimitives.sq_even_iff, ``EKPrimitives.sq_even_saturated_iff,
      ``EKPrimitives.sq_odd_two_smul, ``EKPrimitives.sq_odd_saturated,
      ``EKPrimitivesControls.m1_primitive, ``EKPrimitivesControls.m2_primitive,
      ``EKPrimitivesControls.degree_three_no_primitive, ``EKPrimitivesControls.degree_four_upper,
      ``EKPrimitivesControls.h2_not_primitive,
      ``EKPrimitivesAudit.m4_primitive_closed, ``EKPrimitivesAudit.m3_not_primitive] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler && info.isUnsafe then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' unsafe=true depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' unsafe=false depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"
