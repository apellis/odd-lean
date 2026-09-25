import OddMath.Frontier.EKDeterminantControls
import OddMath.Frontier.EKCoideal
import OddMath.Frontier.EKQuotientRelations

/-! EK1107.5610v2 §3.2 p25 Proposition 3.3 — PRE-production hand controls,
compiled before `EKPrimitives` exists. Actual integral `Q`, actual existing
coproduct `EKCoideal.quotientCoproduct`, actual `EKDualBases.mBasis`.

* degree 1: `m₁ = h₁` and it is primitive (direct coproduct expansion);
* degree 2: `m₂ = h₁h₁` (inherited hand dual) and it is primitive (direct
  expansion of the signed two-generator coproduct); `h₂` is NOT primitive;
* degree 3: no nonzero primitive (the `h₁h₂+h₂h₁ = 2h₃` relation and
  torsion-freeness of ℤ, NOT division by 2);
* degree 4: every primitive lies in `ℤ • m₄`; the literal statement
  "m₄ is primitive" is fixed here as a target `Prop` and closed only in the
  post-production section (the hand straightening facts `h₁h₃ = h₃h₁`,
  `h₁h₂ = 2h₃ - h₂h₁` that make it true are checked here). -/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKPrimitivesControls
open EKRadicalQuotient EKCoideal EKElementaryQuotient EKDualBases EKIntegralBases
  DegreeShapes EKDualBasesControls EKDeterminantControls
open EKPartitionSpanning (hPartition)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- The source predicate, literally `Δ x = 1 ⊗ x + x ⊗ 1`. -/
def IsPrim (x : Q) : Prop := quotientCoproduct x = (1 : Q) ⊗ₜ[ℤ] x + x ⊗ₜ[ℤ] (1 : Q)

/-- Adjointness on the quotient (inline, from the inherited free-algebra adjointness). -/
theorem test_coproduct (a b x : Q) :
    tensorTest a b (quotientCoproduct x) = quotientPairing (a * b) x := by
  obtain ⟨a, rfl⟩ := pi_surjective a
  obtain ⟨b, rfl⟩ := pi_surjective b
  obtain ⟨x, rfl⟩ := pi_surjective x
  rw [quotientCoproduct_pi, tensorTest_map, EKPairingAdjoint.tensorPairing_symm,
    EKPairingAdjoint.adjointness, ← pi.map_mul, quotientPairing_pi]

/-- Primitive elements are derivations against the pairing. -/
theorem prim_deriv {x : Q} (hx : IsPrim x) (a b : Q) :
    quotientPairing (a * b) x =
      quotientCounit a * quotientPairing b x + quotientPairing a x * quotientCounit b := by
  rw [← test_coproduct, hx, map_add, tensorTest_tmul, tensorTest_tmul,
    quotientPairing_symm 1 a, quotientPairing_right_one, quotientPairing_symm 1 b,
    quotientPairing_right_one, quotientPairing_symm x b, quotientPairing_symm x a]

theorem counit_h_pos {k : ℕ} (hk : 0 < k) : quotientCounit (h k) = 0 := by
  rw [h, quotientCounit_pi, EKFreeCoproduct.counit_h, if_neg (by omega)]

theorem counit_prod_pos (t : List ℕ) (ht : ∀ k ∈ t, 0 < k) (hne : t ≠ []) :
    quotientCounit ((t.map h).prod) = 0 := by
  cases t with
  | nil => exact absurd rfl hne
  | cons k t =>
    rw [List.map_cons, List.prod_cons, map_mul, counit_h_pos (ht k (by simp)), zero_mul]

/-- Generic in this control file: a primitive is orthogonal to every
complete word of at least two positive rows. -/
theorem prim_long_zero {x : Q} (hx : IsPrim x) (μ : YoungDiagram)
    (hμ : 2 ≤ μ.rowLens.length) : quotientPairing (hPartition μ) x = 0 := by
  have hp := μ.pos_of_mem_rowLens
  unfold hPartition
  cases he : μ.rowLens with
  | nil => simp [he] at hμ
  | cons a t =>
    have ht : t ≠ [] := by rintro rfl; simp [he] at hμ
    rw [List.map_cons, List.prod_cons, prim_deriv hx, counit_h_pos (hp a (by simp [he])),
      counit_prod_pos t (fun k hk => hp k (by simp [he, hk])) ht]
    ring

/-- Exhaustive row-shape dichotomy in positive degree. -/
theorem shape_cases {n : ℕ} (hn : 0 < n) (μ : DegreeShape n) :
    μ.val.rowLens = [n] ∨ 2 ≤ μ.val.rowLens.length := by
  have hs := (rowLens_sum μ.val).trans μ.property
  cases he : μ.val.rowLens with
  | nil => simp [he] at hs; omega
  | cons a t =>
    cases t with
    | nil => left; simp only [he, List.sum_cons, List.sum_nil, add_zero] at hs; simp [hs]
    | cons b t => right; simp

/-! ### degree 1 -/

theorem h1_primitive : IsPrim (h 1) := by
  unfold IsPrim h
  rw [quotientCoproduct_pi, EKFreeCoproduct.coproduct_h]
  simp [Fin.sum_univ_two, add_comm]

theorem m1_eq_h1 : (mBasis 1 oneShape : Q) = h 1 := by
  have hm := m_unique 1 oneShape (degreeHBasis 1 oneShape) (by
    intro ν; rw [degree_one_shape ν]; simp [hPartition, degree_one])
  rw [← hm, degreeHBasis_apply]
  simp [hPartition]

theorem m1_primitive : IsPrim (mBasis 1 oneShape : Q) := by
  rw [m1_eq_h1]; exact h1_primitive

/-! ### degree 2 -/

theorem h11_primitive : IsPrim (h 1 * h 1) := by
  unfold IsPrim h
  rw [← pi.map_mul, quotientCoproduct_pi, EKFreeCoproduct.coproduct_two]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Nat.sub_zero, Nat.sub_self, zero_add, add_zero, Fin.succ_zero_eq_one, Fin.val_one]
  norm_num [map_add, map_zsmul, quotientTensorMap_tmul, CompleteElementary.h_zero,
    TensorProduct.neg_tmul]
  abel

theorem m2_primitive : IsPrim (mBasis 2 row2 : Q) := by
  rw [degree_two_duals.1]; exact h11_primitive

theorem h2_coproduct :
    quotientCoproduct (h 2) = (1 : Q) ⊗ₜ[ℤ] h 2 + h 1 ⊗ₜ[ℤ] h 1 + h 2 ⊗ₜ[ℤ] (1 : Q) := by
  unfold h
  rw [quotientCoproduct_pi, EKFreeCoproduct.coproduct_h]
  simp [Fin.sum_univ_succ, add_assoc]

/-- Negative control: the one-row complete element `h₂` is NOT primitive. -/
theorem h2_not_primitive : ¬ IsPrim (h 2) := by
  intro hp
  unfold IsPrim at hp
  rw [h2_coproduct] at hp
  have hz : h 1 ⊗ₜ[ℤ] h 1 = (0 : Q ⊗[ℤ] Q) := by
    have e : ((1 : Q) ⊗ₜ[ℤ] h 2 + h 2 ⊗ₜ[ℤ] (1 : Q)) + h 1 ⊗ₜ[ℤ] h 1 =
        ((1 : Q) ⊗ₜ[ℤ] h 2 + h 2 ⊗ₜ[ℤ] (1 : Q)) + 0 := by
      rw [add_zero]; conv_rhs => rw [← hp]
      abel
    exact add_left_cancel e
  have ht := congrArg (tensorTest (h 1) (h 1)) hz
  rw [tensorTest_tmul, degree_one, map_zero] at ht
  norm_num at ht

/-! ### degree 3: no nonzero primitive -/

theorem h3_orth {x : Q} (hx : IsPrim x) : quotientPairing (h 3) x = 0 := by
  have hrel := EKQuotientRelations.complete_one_even 1
  have e : quotientPairing ((2 : ℤ) • h 3) x = 0 := by
    rw [show (2 * 1 + 1 : ℕ) = 3 from rfl, show (2 * 1 : ℕ) = 2 from rfl] at hrel
    rw [← hrel, map_add, LinearMap.add_apply, prim_deriv hx, prim_deriv hx,
      counit_h_pos (by norm_num : 0 < 1), counit_h_pos (by norm_num : 0 < 2)]
    ring
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at e
  omega

theorem degree_three_no_primitive (x : degreePiece 3) (hx : IsPrim x.val) : x = 0 := by
  rw [reconstruct_m 3 x]
  apply Finset.sum_eq_zero
  intro μ _
  rcases shape_cases (by norm_num) μ with hr | hr
  · have : hPartition μ.val = h 3 := by simp [hPartition, hr]
    rw [this, h3_orth hx, zero_smul]
  · rw [prim_long_zero hx μ.val hr, zero_smul]

/-! ### degree 4 -/

def row4 : DegreeShape 4 :=
  ⟨YoungDiagram.ofRowLens [4] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩

@[simp] theorem row4_rows : row4.val.rowLens = [4] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)

theorem eq_row4 (μ : DegreeShape 4) (h : μ.val.rowLens = [4]) : μ = row4 := by
  apply Subtype.ext
  apply YoungDiagram.equivListRowLens.injective
  apply Subtype.ext
  change μ.val.rowLens = row4.val.rowLens
  rw [h, row4_rows]

/-- Degree 4 upper bound, pre-production: every primitive is an integer multiple of m₄. -/
theorem degree_four_upper (x : degreePiece 4) (hx : IsPrim x.val) :
    x = quotientPairing (h 4) x.val • mBasis 4 row4 := by
  conv_lhs => rw [reconstruct_m 4 x]
  rw [Finset.sum_eq_single row4]
  · have : hPartition row4.val = h 4 := by simp [hPartition]
    rw [this]
  · intro μ _ hne
    rcases shape_cases (by norm_num) μ with hr | hr
    · exact absurd (eq_row4 μ hr) hne
    · rw [prim_long_zero hx μ.val hr, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Hand straightening inputs for the degree-4 lower bound. -/
theorem h1_h3_comm : h 1 * h 3 = h 3 * h 1 :=
  EKQuotientRelations.complete_even 1 3 (by decide)

theorem h1_h2_straighten : h 1 * h 2 = (2 : ℤ) • h 3 - h 2 * h 1 := by
  have hrel := EKQuotientRelations.complete_one_even 1
  rw [show (2 * 1 + 1 : ℕ) = 3 from rfl, show (2 * 1 : ℕ) = 2 from rfl] at hrel
  rw [← hrel]; abel

/-- The degree-4 lower-bound target, FIXED before production. -/
def m4PrimitiveTarget : Prop := IsPrim (mBasis 4 row4 : Q)

end OddMath.Frontier.EKPrimitivesControls
