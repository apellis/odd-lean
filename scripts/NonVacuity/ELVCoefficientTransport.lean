import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTransport

noncomputable section
namespace ELVCoefficientTransportConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
/-- Odd rank one over a ring with two invertible. -/
def datum : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

def oddColour : {i : Unit // datum.parity i = 1} := ⟨(), rfl⟩

def delta : SKM.SYM datum ℚ := SKM.SYM.delta datum ℚ oddColour

/-- The tested exterior coefficient is not specialized to zero. -/
theorem delta_ne_zero : delta ≠ 0 := by
  intro h
  have he := congrArg (SKM.SYM.exteriorProjection datum ℚ) h
  simp only [delta, SKM.SYM.exteriorProjection_delta, map_zero] at he
  have hz := (ExteriorAlgebra.ι_eq_zero_iff (R := ℚ) _).mp he
  have hz' := congrArg (fun f : SKM.SYM.OddModule datum ℚ => f oddColour) hz
  simp at hz'

open SKM.SYM

/-- The odd parameter survives the exact quotient at both positive cutoff parities. -/
theorem quotient_delta_ne_zero (N : ℕ) (hN : 1 ≤ N) :
    elvCoefficientQuotient datum (fun _ => N) delta ≠ 0 := by
  have hd : delta ∈ CoefficientAtMost datum ℚ 1 := by
    apply Submodule.subset_span
    refine ⟨(0, {oddColour}), ?_, ?_⟩
    · simp [coefficientWeight]
    · exact coefficientBasis_delta datum ℚ oddColour
  intro hz
  have hi := elvCoefficient_quotient_injective datum ℚ
    (cutoff := fun _ => N) (d := 1) (fun _ => hN)
  have he := hi (a₁ := ⟨delta, hd⟩) (a₂ := 0) hz
  exact delta_ne_zero (congrArg Subtype.val he)

example := quotient_delta_ne_zero 2 (by decide)
example := quotient_delta_ne_zero 3 (by decide)

/-- At even cutoff two, the full polynomial is chi_1 + delta*x + x². -/
example : elvMonicCoefficient datum ℚ oddColour 2 =
    ![e datum ℚ () 0, delta, 1] := by
  funext j
  fin_cases j <;> norm_num [elvMonicCoefficient, elvCoefficient, elvChi, delta, oddColour]

/-- At odd cutoff three, it is -delta*chi_1 + chi_1*x - delta*x² + x³. -/
example : elvMonicCoefficient datum ℚ oddColour 3 =
    ![(-1 : ℚ) • (delta * e datum ℚ () 0), e datum ℚ () 0, (-1 : ℚ) • delta, 1] := by
  funext j
  fin_cases j <;> norm_num [elvMonicCoefficient, elvCoefficient, elvChi, delta, oddColour]

/-- Explicitly test the top relation in the coefficient algebra. -/
example : elvCoefficientQuotient datum (fun _ => 2)
    (delta * e datum ℚ () 0) = 0 := by
  exact elvCoefficientQuotient_top datum (fun _ => 2) oddColour rfl

/-- Test the same top relation after tensoring with a nonempty affine word. -/
example : elvHomQuotient datum scalars (fun _ => 2) [()] [()]
    (sourceCoefficientHom datum scalars (delta * e datum ℚ () 0) (𝟙 _)) = 0 := by
  rw [elvHomQuotient_source]
  have h := elvCoefficientQuotient_top (k := ℚ) datum (fun _ => 2) oddColour rfl
  change elvCoefficientQuotient datum (fun _ => 2) (delta * e datum ℚ () 0) = 0 at h
  rw [h, TensorProduct.zero_tmul]

/-- The zero cutoff has polynomial one and kills its odd parameter. -/
example : elvCoefficientQuotient datum (fun _ => 0) delta = 0 := by
  simpa [elvChi, delta] using
    elvCoefficientQuotient_top (k := ℚ) datum (fun _ => 0) oddColour rfl

example : elvMonicCoefficient datum ℚ oddColour 0 0 = 1 := by
  simp [elvMonicCoefficient, elvCoefficient, elvChi]

/-- Even cutoff: the coefficient sign cancels the dot sign. -/
example :
    elvHomQuotient datum scalars (fun _ => 2) [(), ()] [(), ()]
      (elvDotPolynomial datum scalars oddColour [(), ()] 0 2 ≫
        sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()])) =
    elvHomQuotient datum scalars (fun _ => 2) [(), ()] [(), ()]
      (sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()]) ≫
        elvDotPolynomial datum scalars oddColour [(), ()] 1 2) := by
  simpa [datum, oddColour, wordSumParity, sign, show (2 : ZMod 2) = 0 from rfl] using
    elvDotPolynomial_transport datum scalars (fun _ => 2) oddColour [] [()]

/-- Odd cutoff: all terms acquire the same minus sign. -/
example :
    elvHomQuotient datum scalars (fun _ => 3) [(), ()] [(), ()]
      (elvDotPolynomial datum scalars oddColour [(), ()] 0 3 ≫
        sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()])) =
    (-1 : ℚ) • (elvHomQuotient datum scalars (fun _ => 3) [(), ()] [(), ()]
      (sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()]) ≫
        elvDotPolynomial datum scalars oddColour [(), ()] 1 3)) := by
  simpa [datum, oddColour, wordSumParity, sign, show (3 : ZMod 2) = 1 from rfl] using
    elvDotPolynomial_transport datum scalars (fun _ => 3) oddColour [] [()]

example := elvDotPolynomial_old_transport datum scalars (fun _ => 2) () oddColour [()] [()] []
example := elvDotPolynomial_old_transport datum scalars (fun _ => 3) () oddColour [] [()] []
example := elvDotPolynomial_transport datum scalars (fun _ => 0) oddColour [] []
example := elvDotPolynomial_first datum scalars oddColour [()] 3

/-- A ground ring with a nonzero square-zero element and invertible two. -/
example : (3 : ZMod 9) ≠ 0 ∧ (3 : ZMod 9) * 3 = 0 := by decide

def scalarsModNine : SKM.Scalars datum (ZMod 9) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => ⟨⟨2, 5, by decide, by decide⟩, rfl⟩

example := elvDotPolynomial_transport datum scalarsModNine (fun _ => 2) oddColour [] [()]
example := elvDotPolynomial_old_transport datum scalarsModNine (fun _ => 3) () oddColour [] [] []
example : elvCoefficientQuotient (k := ZMod 9) datum (fun _ => 2)
    (SKM.SYM.delta datum (ZMod 9) oddColour * e datum (ZMod 9) () 0) = 0 := by
  exact elvCoefficientQuotient_top datum (fun _ => 2) oddColour rfl

#print axioms elvMonicCoefficient_mem_parity
#print axioms elvCoefficientQuotient_top
#print axioms elvHomQuotient_kills
#print axioms elvHomQuotient_dotPolynomial
#print axioms elvDotPolynomial_first
#print axioms elvDotPolynomial_transport
#print axioms elvDotPolynomial_old_transport
#print axioms quotient_delta_ne_zero
end ELVCoefficientTransportConsumer
