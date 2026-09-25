import OddMath.Frontier.CenterPoly

/-! Audit of the corrected center of EKL arXiv:1111.1320v1, Prop. 2.15, p. 13
(polynomial side). Each headline is restated verbatim with no residual hypothesis,
for every rank `N = n+2`, and its axioms are printed. -/
namespace OddMath.Frontier.CenterPolyAudit
open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.CenterPoly
noncomputable section

/-- (P1) The center of the skew polynomial ring, on the coefficient function. -/
theorem audit_mem_center_iff (n : ℕ) (z : SkewPolynomial (n+2)) :
    z ∈ Subring.center (SkewPolynomial (n+2)) ↔
      ∀ a, z a ≠ 0 → (∀ j, Even (a j)) ∨ (Odd (n+2) ∧ ∀ j, Odd (a j)) :=
  CenterPoly.mem_center_iff z

/-- (P2) The squared-variable homomorphism sends `X j` to `x_j ^ 2`, lands in the
center, and is injective. -/
theorem audit_squareHom (n : ℕ) :
    (∀ j : Fin (n+2), CenterPoly.squareHom (MvPolynomial.X j) = generator j ^ 2) ∧
    (∀ p, CenterPoly.squareHom (n := n) p ∈ Subring.center (SkewPolynomial (n+2))) ∧
    Function.Injective (CenterPoly.squareHom (n := n)) :=
  ⟨CenterPoly.squareHom_X, CenterPoly.squareHom_mem_center, CenterPoly.squareHom_injective⟩

/-- (P2) The squared symmetric ring is the image of Mathlib's `symmetricSubalgebra`. -/
theorem audit_mem_sq (n : ℕ) (z : SkewPolynomial (n+2)) :
    z ∈ CenterPoly.sq n ↔
      ∃ p ∈ MvPolynomial.symmetricSubalgebra (Fin (n+2)) ℤ, CenterPoly.squareHom p = z :=
  CenterPoly.mem_sq z

/-- (P2) The volume is the ordered product of the generators. -/
theorem audit_V (n : ℕ) :
    CenterPoly.V n = (List.ofFn (fun j : Fin (n+2) => generator j)).prod := rfl

/-- Central elements of the joint kernel, both directions, every rank. -/
theorem audit_kernel_inter_center (n : ℕ) (z : SkewPolynomial (n+2)) :
    (z ∈ kernelSubring n ∧ z ∈ Subring.center (SkewPolynomial (n+2))) ↔
      ∃ a ∈ CenterPoly.sq n, ∃ b ∈ CenterPoly.sq n,
        z = a + (if Odd (n+2) then CenterPoly.V n * b else 0) :=
  CenterPoly.kernel_inter_center n z

/-- (P4) The second claim of the printed proof. -/
theorem audit_second_claim (n : ℕ) (i : Fin (n+1)) (f : SkewPolynomial (n+2))
    (hf : f ∈ (CenterPoly.squareHom (n := n)).range) : divided i f = 0 ↔ s i f = f :=
  CenterPoly.second_claim_range i f hf

/-- (P5) Even rank: the printed statement holds. -/
theorem audit_even_rank (n : ℕ) (h : Even (n+2)) (z : SkewPolynomial (n+2)) :
    (z ∈ kernelSubring n ∧ z ∈ Subring.center (SkewPolynomial (n+2))) ↔ z ∈ CenterPoly.sq n :=
  CenterPoly.even_rank n h z

/-- (P5) Odd rank: the volume is a central kernel element outside the squared symmetric ring. -/
theorem audit_odd_rank (n : ℕ) (h : Odd (n+2)) :
    CenterPoly.V n ∈ kernelSubring n ∧ CenterPoly.V n ∈ Subring.center (SkewPolynomial (n+2)) ∧
      CenterPoly.V n ∉ CenterPoly.sq n :=
  CenterPoly.odd_rank n h

/-- (P5) The printed statement holds exactly in even rank. -/
theorem audit_printed_statement_iff (n : ℕ) :
    (∀ z : SkewPolynomial (n+2),
      (z ∈ kernelSubring n ∧ z ∈ Subring.center (SkewPolynomial (n+2))) ↔ z ∈ CenterPoly.sq n) ↔
      Even (n+2) :=
  CenterPoly.printed_statement_iff n

#print axioms CenterPoly.mem_center_iff
#print axioms CenterPoly.squareHom_X
#print axioms CenterPoly.squareHom_mem_center
#print axioms CenterPoly.squareHom_injective
#print axioms CenterPoly.mem_sq
#print axioms CenterPoly.second_claim
#print axioms CenterPoly.second_claim_range
#print axioms CenterPoly.kernel_inter_center
#print axioms CenterPoly.even_rank
#print axioms CenterPoly.odd_rank
#print axioms CenterPoly.printed_statement_iff
#print axioms audit_mem_center_iff
#print axioms audit_squareHom
#print axioms audit_mem_sq
#print axioms audit_V
#print axioms audit_kernel_inter_center
#print axioms audit_second_claim
#print axioms audit_even_rank
#print axioms audit_odd_rank
#print axioms audit_printed_statement_iff

end
end OddMath.Frontier.CenterPolyAudit
