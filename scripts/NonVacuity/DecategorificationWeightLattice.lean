import OddMath
import NonVacuity.Decategorification

/-! # The Decategorification Conjecture without finiteness of the weight lattice

Concrete applications of `QuiverHecke.SerreComplex.decategorification_of_separating` and
`QuiverHecke.SerreComplex.decategorification_sourceWeightLattice`, with every hypothesis proved:

* the two-odd-colour datum of `OddMath.SKM.LaurentianK0Examples`, with separating weights the
  standard basis vectors of `Bool → ℤ`;
* BE2's weight lattice `P` of a complex realization with infinitely many odd colours, colour
  `i` having symmetrizing degree `i + 1` so that `DegreeLocallyFinite` holds. This lattice is
  not finitely generated.
-/

noncomputable section
namespace NonVacuity.DecategorificationWeightLattice
open OddMath OddMath.SKM OddMath.QuiverHecke.SerreComplex OddMath.CoveringQuantum
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

/-- `γ` is bijective for the two-odd-colour datum over `ℚ`, from separating weights. -/
example : Function.Bijective (gammaInt twoOddDatum homogeneous cScalars locallyFinite) :=
  decategorification_of_separating twoOddDatum homogeneous cScalars locallyFinite two_ne_zero
    (fun j ↦ Pi.single j 1) (fun i j ↦ by
      change (Pi.single j (1 : ℤ) : Bool → ℤ) i = _
      simp [Pi.single_apply])
    NonVacuity.GroundRingNondegeneracy.twoOdd_root_independent

/-! ### Infinitely many odd colours on BE2's weight lattice -/

/-- The Cartan space `ℕ →₀ ℂ`. -/
abbrev H := ℕ →₀ ℂ

/-- The coroots: the standard basis. -/
def h (i : ℕ) : H := Finsupp.single i 1

/-- The roots `αᵢ = 2 εᵢ`. -/
def alpha (i : ℕ) : Module.Dual ℂ H := (2 : ℂ) • Finsupp.lapply i

/-- The diagonal super Cartan datum with all colours odd and `dᵢ = i + 1`. -/
def cartan : SuperCartanDatum ℕ where
  a i j := if i = j then 2 else 0
  isGCM := {
    diag := fun i ↦ by simp
    offDiag_nonpos := fun i j hij ↦ by simp [hij]
    zero_comm := fun i j ↦ by simp [eq_comm] }
  d i := i + 1
  d_pos _ := by omega
  d_mul_symm i j := by by_cases hij : i = j <;> simp [hij, eq_comm]
  parity _ := 1
  even_of_odd i j _ := by by_cases hij : i = j <;> simp [hij]

theorem cartan_eval (i j : ℕ) : alpha j (h i) = (cartan.a i j : ℂ) := by
  by_cases hij : i = j <;> simp [alpha, h, cartan, Finsupp.single_apply, hij, eq_comm]

theorem coroots_independent : LinearIndependent ℂ h :=
  Finsupp.basisSingleOne.linearIndependent

theorem roots_independent : LinearIndependent ℂ alpha := by
  apply linearIndependent_iff'.mpr
  intro s g hg i hi
  have he := congrArg (fun f : Module.Dual ℂ H ↦ f (h i)) hg
  have hz : g i * 2 = 0 := by
    simpa [LinearMap.sum_apply, alpha, h, Finsupp.single_apply, hi, eq_comm] using he
  exact (mul_eq_zero.mp hz).resolve_right (by norm_num)

/-- The root datum on `P`. -/
abbrev datumP : RootDatum ℕ (SourceWeightLattice.weightLattice h) :=
  SourceWeightLattice.datum h cartan alpha cartan_eval

/-- Scalars `tᵢⱼ = 1`, `sᵢⱼ^{pq} = 0` over `ℚ`. -/
def scalarsP : Scalars datumP.toSKM ℚ where
  t := fun _ _ ↦ 1
  t_self := fun _ ↦ rfl
  t_symm_of_d_eq_zero := fun _ _ _ ↦ rfl
  s := fun _ _ _ _ ↦ 0
  s_symm := fun _ _ _ _ ↦ rfl
  s_eq_zero := fun _ _ _ _ _ ↦ rfl
  two_isUnit := fun _ ↦ isUnit_iff_ne_zero.mpr (by norm_num)

def cScalarsP : CScalars scalarsP where
  c := fun _ _ ↦ 1
  shift := fun _ _ _ ↦ by simp [scalarsP]

theorem homogeneousP : scalarsP.Homogeneous :=
  fun _ _ _ _ _ _ _ _ h ↦ absurd rfl h

theorem locallyFiniteP : datumP.skmSymmetrizer.DegreeLocallyFinite := fun N ↦
  (Set.finite_Iic N).subset fun i (hi : i + 1 ≤ N) ↦ by
    change i ≤ N
    omega

/-- `γ` is bijective on BE2's weight lattice with infinitely many odd colours over `ℚ`. -/
example : Function.Bijective (gammaInt datumP homogeneousP cScalarsP locallyFiniteP) :=
  decategorification_sourceWeightLattice h cartan alpha cartan_eval homogeneousP cScalarsP
    locallyFiniteP two_ne_zero coroots_independent roots_independent

example : Infinite ℕ := inferInstance

#print axioms OddMath.QuiverHecke.SerreComplex.decategorification_of_separating
#print axioms OddMath.QuiverHecke.SerreComplex.decategorification_sourceWeightLattice
#print axioms OddMath.CoveringQuantum.UDot.WindowForm.sourceWeightLattice_nondegenerate

end NonVacuity.DecategorificationWeightLattice
