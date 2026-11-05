import OddMath.QuiverHecke.NondegeneracyIndependentRoots
import NonVacuity.ELVWeightedAppendFixture

/-!
Non-vacuity of `SKM.CScalars.nonempty_of_linearIndependent`: on a mixed even/odd datum with
linearly independent simple roots and nontrivial scalars `tᵢⱼ`, normalizations exist, and the
Nondegeneracy Conjecture holds for the resulting choice.
-/

noncomputable section
open OddMath OddMath.SKM OddMath.QuiverHecke
namespace NondegeneracyIndependentRootsConsumer

private abbrev D := ELVOld.WeightedAppendFixture.datum

/-- The simple roots `(2, -4)` and `(-2, 2)` of the fixture are linearly independent. -/
private theorem roots_linearIndependent : LinearIndependent ℤ D.α := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg false
  have h1 := congrFun hg true
  simp [Fintype.sum_bool, D, ELVOld.WeightedAppendFixture.datum,
    CyclotomicAction.AsymmetricParameters.datum] at h0 h1
  intro i
  cases i <;> omega

/-- The unit `2` of `ℚ`. -/
private def two : ℚˣ := Units.mk0 2 (by norm_num)

/-- Scalars with `t₀₁ = t₁₀ = 2` and vanishing `s`. -/
private def scalars : Scalars D ℚ :=
  { ELVOld.WeightedAppendFixture.scalars with
    t := fun i j => if i = j then 1 else two
    t_self := fun _ => if_pos rfl
    t_symm_of_d_eq_zero := by intro i j _; cases i <;> cases j <;> rfl }

private def sy : Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

private theorem hc : scalars.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

/-- Normalizations exist for these scalars. -/
example : Nonempty (CScalars scalars) :=
  CScalars.nonempty_of_linearIndependent scalars roots_linearIndependent

/-- The conjecture for the constructed normalizations. -/
example : NondegeneracyConjecture
    (CScalars.nonempty_of_linearIndependent scalars roots_linearIndependent).some :=
  nondegeneracy_of_symmetrizer sy (by norm_num) hc _

/-! ## A purely even datum with general homogeneous scalars

The Cartan matrix `((2, -2), (-2, 2))` realized on `X = ℤ^{none, some false, some true}` with
the extra coordinate making the simple roots independent; both colours are even. The scalars
`t₀₁ = 2`, `t₁₀ = 3`, `s₀₁^{11} = s₁₀^{11} = 5` are homogeneous but not Khovanov–Lauda scalars
(`s ≠ 0`), so the even bridge does not apply; the conjecture follows from the end theorem. -/

/-- The even datum. -/
private def evenDatum : Datum Bool (Option Bool → ℤ) where
  cd := {
    root := fun j i => Option.elim i (if j then 1 else 0) fun i => if i = j then 2 else -2
    coroot := fun i => LinearMap.proj (some i)
    coroot_root_self := fun i => by simp }
  isGCM := {
    diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j hij
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => 0
  even_of_odd := by
    intro i j h
    exact absurd h (by decide)

private theorem evenDatum_d (i j : Bool) : evenDatum.d i j = if i = j then -2 else 2 := by
  cases i <;> cases j <;> rfl

private theorem evenRoots_linearIndependent : LinearIndependent ℤ evenDatum.α := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg none
  have h1 := congrFun hg (some false)
  simp [Fintype.sum_bool, evenDatum] at h0 h1
  intro i
  cases i <;> omega

/-- The unit `3` of `ℚ`. -/
private def three : ℚˣ := Units.mk0 3 (by norm_num)

/-- General homogeneous even scalars. -/
private def evenScalars : Scalars evenDatum ℚ where
  t := fun i j => if i = j then 1 else if i then three else two
  t_self := fun _ => if_pos rfl
  t_symm_of_d_eq_zero := by
    intro i j h
    rw [evenDatum_d] at h
    cases i <;> cases j <;> simp_all
  s := fun _ _ p q => if p = 1 ∧ q = 1 then 5 else 0
  s_symm := by intro _ _ p q; simp only [and_comm]
  s_eq_zero := by
    intro _ _ _ _ h
    simp [evenDatum] at h
  two_isUnit := by
    rintro ⟨_, h⟩
    exact absurd h (by decide)

private def evenSy : Symmetrizer evenDatum where
  d := fun _ => 1
  pos := fun _ => one_pos
  symm := by intro i j; cases i <;> cases j <;> rfl

private theorem evenScalars_homogeneous : evenScalars.Homogeneous := by
  intro i j p q hp hpd hq hqd _
  rw [evenDatum_d] at hpd hqd
  rw [evenDatum_d, evenDatum_d]
  cases i <;> cases j <;> simp at hpd hqd ⊢ <;> omega

/-- The scalar `s₀₁^{11}` is nonzero, so these are not Khovanov–Lauda scalars. -/
example : evenScalars.s false true 1 1 ≠ 0 := by simp [evenScalars]

/-- Even nondegeneracy for general homogeneous scalars, with normalizations constructed. -/
example : Nonempty (CScalars evenScalars) ∧
    ∀ cs : CScalars evenScalars, NondegeneracyConjecture cs :=
  exists_nondegeneracy_of_linearIndependent evenSy evenRoots_linearIndependent (by norm_num)
    evenScalars_homogeneous

#print axioms exists_nondegeneracy_of_linearIndependent

end NondegeneracyIndependentRootsConsumer
