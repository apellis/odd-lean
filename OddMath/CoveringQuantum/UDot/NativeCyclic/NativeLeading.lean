import OddMath.CoveringQuantum.UDot.TensorGram.TensorPositive
import OddMath.CoveringQuantum.UDot.Triangular

/-!
# Native matched-word leading terms

The native Delta1/Delta2 action on the original highest/lowest quotient tensor.
The first results identify actual matched normal words and their positive vacuum
values; the downstream use is triangular cyclic evaluation, not faithfulness.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
open PreF Coefficients TensorProduct MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

/-- The actual unprojected operators of one signed half-word. -/
def halfOperators (s positive : Bool) (w : List I) :=
  (w.map (tensorChevalley D hD Λ Μ s positive)).prod

/-- Original weight-labelled half-word, with its right projector retained. -/
theorem representation_halfWord (s positive : Bool) (w : List I) (ν : X) :
    tensorRepresentation D hD Λ Μ s (halfWord D Coefficients.q pi positive w ν) =
      halfOperators D hD Λ Μ s positive w * tensorProject D hD Λ Μ ν := by
  have hg (i : I) (μ : X) :
      tensorRepresentation D hD Λ Μ s (halfGen D Coefficients.q pi positive i μ) =
        tensorChevalley D hD Λ Μ s positive i * tensorProject D hD Λ Μ μ := by
    cases positive <;> simp [halfGen, tensorChevalley, tensorEBlock]
  induction w with
  | nil => simp [halfWord, halfOperators]
  | cons i w ih =>
    rw [halfWord, map_mul, hg, mul_assoc, ← tensorRepresentation_one,
      ← map_mul, (halfWord_mem_block D Coefficients.q pi positive w ν).1, ih]
    simp only [halfOperators, List.map_cons, List.prod_cons, mul_assoc]

/-- Exact bridge to the requested matched normal word in the original algebra. -/
theorem normalWord_action (s : Bool) (a b : List I) :
    tensorRepresentation D hD Λ Μ s (normalWord D Coefficients.q pi a b (Λ - Μ))
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
      halfOperators D hD Λ Μ s false a
        (halfOperators D hD Λ Μ s true b
          (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1)) := by
  rw [normalWord, map_mul, representation_halfWord, mul_assoc,
    ← tensorRepresentation_one, ← map_mul,
    (halfWord_mem_block D Coefficients.q pi true b (Λ - Μ)).1,
    representation_halfWord]
  simp only [Module.End.mul_apply, project_vacuum]

/-- The exact candidate toral coefficient; no inverse or nonzero assumption. -/
def leadingScalar (s : Bool) (a b : List I) : Coefficients.Ring :=
  TensorPositive.amplitude D s Λ b *
    TensorPositive.amplitude D false (Μ - halfWeight D true (wordWeight b)) a

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- Toral factors are units even though the covering ring has zero divisors. -/
theorem toral_isUnit (s : Bool) (i : I) (ν : X) :
    IsUnit (tensorToralScalar D s i ν) := by
  have hp : IsUnit (D.pii pi i) := isUnit_iff_exists_inv.mpr
    ⟨D.pii pi i, by simpa only [pow_two] using D.pii_sq pi pi_sq i⟩
  unfold tensorToralScalar
  apply IsUnit.mul
  · cases s
    · exact isUnit_one
    · exact hp.pow _
  · exact Units.isUnit _

omit [DecidableEq I] [DecidableEq X] [Finite I] in
theorem amplitude_isUnit (s : Bool) (ν : X) (w : List I) :
    IsUnit (TensorPositive.amplitude D s ν w) := by
  induction w with
  | nil => exact isUnit_one
  | cons i w ih => exact (toral_isUnit D s i ν).mul ih

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- The complete proposed leading coefficient is invertible in the actual ring. -/
theorem leadingScalar_isUnit (s : Bool) (a b : List I) :
    IsUnit (leadingScalar D Λ Μ s a b) :=
  (amplitude_isUnit D s Λ b).mul (amplitude_isUnit D false _ a)

/-- Empty negative half: exact native recovery of every positive word. -/
theorem normalWord_nil_left (s : Bool) (b : List I) :
    tensorRepresentation D hD Λ Μ s (normalWord D Coefficients.q pi [] b (Λ - Μ))
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
      leadingScalar D Λ Μ s [] b •
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring]
          toIntegrable D hD Μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) := by
  rw [normalWord_action]
  simpa only [halfOperators, List.map_nil, List.prod_nil, Module.End.one_apply,
    leadingScalar, TensorPositive.amplitude, mul_one, TensorPositive.pos,
    wordAction, List.map_map, Function.comp_def, project, PolarizationTransport.vac] using
    TensorPositive.wordAction_pos D hD Λ Μ s b

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
