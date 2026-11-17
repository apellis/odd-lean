import OddMath

/-! # BE2 Theorem 11.7 with infinitely many colours of the same degree

Concrete applications of `QuiverHecke.SerreComplex.theorem_11_7_existence` and
`QuiverHecke.theorem_11_7_surjective` to BE2's weight lattice of a complex realization with
infinitely many odd colours, all of symmetrizing degree `1`. Every hypothesis is proved, and the
colour set is not degree-locally finite (`not_degreeLocallyFinite`), so the examples use the
theorems in a case outside `Symmetrizer.DegreeLocallyFinite`.
-/

noncomputable section
namespace NonVacuity.Theorem117AllColours
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.SerreComplex
open OddMath.CoveringQuantum

/-- The Cartan space `ℕ →₀ ℂ`. -/
abbrev H := ℕ →₀ ℂ

/-- The coroots: the standard basis. -/
def h (i : ℕ) : H := Finsupp.single i 1

/-- The roots `αᵢ = 2 εᵢ`. -/
def alpha (i : ℕ) : Module.Dual ℂ H := (2 : ℂ) • Finsupp.lapply i

/-- The diagonal super Cartan datum with all colours odd and `dᵢ = 1`. -/
def cartan : SuperCartanDatum ℕ where
  a i j := if i = j then 2 else 0
  isGCM := {
    diag := fun i ↦ by simp
    offDiag_nonpos := fun i j hij ↦ by simp [hij]
    zero_comm := fun i j ↦ by simp [eq_comm] }
  d _ := 1
  d_pos _ := by omega
  d_mul_symm i j := by by_cases hij : i = j <;> simp [hij, eq_comm]
  parity _ := 1
  even_of_odd i j _ := by by_cases hij : i = j <;> simp [hij]

theorem cartan_eval (i j : ℕ) : alpha j (h i) = (cartan.a i j : ℂ) := by
  by_cases hij : i = j <;> simp [alpha, h, cartan, hij, eq_comm]

/-- The root datum on `P`. -/
abbrev datum : RootDatum ℕ (SourceWeightLattice.weightLattice h) :=
  SourceWeightLattice.datum h cartan alpha cartan_eval

/-- Scalars `tᵢⱼ = 1`, `sᵢⱼ^{pq} = 0` over `ℚ`. -/
def scalars : Scalars datum.toSKM ℚ where
  t := fun _ _ ↦ 1
  t_self := fun _ ↦ rfl
  t_symm_of_d_eq_zero := fun _ _ _ ↦ rfl
  s := fun _ _ _ _ ↦ 0
  s_symm := fun _ _ _ _ ↦ rfl
  s_eq_zero := fun _ _ _ _ _ ↦ rfl
  two_isUnit := fun _ ↦ isUnit_iff_ne_zero.mpr (by norm_num)

def cScalars : CScalars scalars where
  c := fun _ _ ↦ 1
  shift := fun _ _ _ ↦ by simp [scalars]

theorem homogeneous : scalars.Homogeneous :=
  fun _ _ _ _ _ _ _ h ↦ absurd rfl h

/-- Infinitely many colours have degree `1`, so `DegreeLocallyFinite` fails. -/
theorem not_degreeLocallyFinite : ¬ datum.skmSymmetrizer.DegreeLocallyFinite := by
  intro hf
  have h1 : {i | datum.skmSymmetrizer.d i ≤ ((1 : ℕ) : ℤ)} = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ show ((1 : ℕ) : ℤ) ≤ ((1 : ℕ) : ℤ) from le_rfl
  exact Set.infinite_univ (α := ℕ) (h1 ▸ hf 1)

/-- Existence and uniqueness of `γ`. -/
example := theorem_11_7_existence datum homogeneous cScalars

/-- `γ` is surjective. -/
example : Function.Surjective (gammaInt datum homogeneous cScalars) :=
  theorem_11_7_surjective datum homogeneous cScalars

end NonVacuity.Theorem117AllColours
