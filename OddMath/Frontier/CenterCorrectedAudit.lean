import OddMath.Frontier.CenterCorrected

/-!
# Audit for `CenterCorrected`

Each headline of the corrected EKL arXiv:1111.1320v1, Prop. 2.15, p. 13 is restated with
no residual hypothesis, for every rank `N = n + 2`, followed by `#print axioms` for every
headline and for the proved halves it composes.
-/

namespace OddMath.Frontier.CenterCorrectedAudit
open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.NilHeckeAction

/-- `Z(OΛ_N) = S_N` (`N` even), `S_N ⊕ V S_N` (`N` odd). -/
theorem audit_center_oddSymmetric (n : ℕ) (z : kernelSubring n) :
    z ∈ Subring.center (kernelSubring n) ↔
      ∃ a ∈ CenterPoly.sq n, ∃ b ∈ CenterPoly.sq n,
        (z : SkewPolynomial (n+2)) = a + (if Odd (n+2) then CenterPoly.V n * b else 0) :=
  CenterCorrected.center_oddSymmetric n z

/-- `Z(ONH_N)` is the dot image of `Z(OΛ_N)`. -/
theorem audit_center_nilHecke (n : ℕ) (x : Presented n) :
    x ∈ Subring.center (Presented n) ↔
      ∃ a ∈ CenterPoly.sq n, ∃ b ∈ CenterPoly.sq n,
        x = CenterONH.polynomialInclusion n
          (a + (if Odd (n+2) then CenterPoly.V n * b else 0)) :=
  CenterCorrected.center_nilHecke n x

/-- The printed statement for `OΛ_N` holds iff `N` is even. -/
theorem audit_printed_iff_even (n : ℕ) :
    (∀ z : kernelSubring n,
      z ∈ Subring.center (kernelSubring n) ↔ (z : SkewPolynomial (n+2)) ∈ CenterPoly.sq n) ↔
      Even (n+2) :=
  CenterCorrected.printed_iff_even n

/-- The printed statement for `ONH_N` holds iff `N` is even. -/
theorem audit_printed_iff_even_nilHecke (n : ℕ) :
    (∀ x : Presented n,
      x ∈ Subring.center (Presented n) ↔
        ∃ a ∈ CenterPoly.sq n, x = CenterONH.polynomialInclusion n a) ↔
      Even (n+2) :=
  CenterCorrected.printed_iff_even_nilHecke n

/-- Directness of `S_N + V S_N`. -/
theorem audit_decomposition_unique (n : ℕ) (a b a' b' : SkewPolynomial (n+2))
    (ha : a ∈ CenterPoly.sq n) (hb : b ∈ CenterPoly.sq n)
    (ha' : a' ∈ CenterPoly.sq n) (hb' : b' ∈ CenterPoly.sq n)
    (h : a + CenterPoly.V n * b = a' + CenterPoly.V n * b') : a = a' ∧ b = b' :=
  CenterCorrected.decomposition_unique n ha hb ha' hb' h

/-- The objects in the statements are the library's actual ones. -/
theorem audit_objects (n : ℕ) :
    CenterPoly.V n =
        (List.ofFn (fun j : Fin (n+2) => OddMath.SkewPolynomial.generator j)).prod ∧
      (∀ z : SkewPolynomial (n+2),
        z ∈ CenterPoly.sq n ↔
          ∃ p ∈ MvPolynomial.symmetricSubalgebra (Fin (n+2)) ℤ, CenterPoly.squareHom p = z) ∧
      (∀ j : Fin (n+2), CenterPoly.squareHom (MvPolynomial.X j) =
          OddMath.SkewPolynomial.generator j ^ 2) ∧
      (∀ j : Fin (n+2), CenterONH.polynomialInclusion n (OddMath.SkewPolynomial.generator j) =
          dot n j) ∧
      Function.Injective (CenterONH.polynomialInclusion n) :=
  ⟨rfl, CenterPoly.mem_sq, CenterPoly.squareHom_X, CenterONH.polynomialInclusion_generator,
    CenterONH.polynomialInclusion_injective⟩

end OddMath.Frontier.CenterCorrectedAudit

#print axioms OddMath.Frontier.CenterCorrected.center_oddSymmetric
#print axioms OddMath.Frontier.CenterCorrected.center_nilHecke
#print axioms OddMath.Frontier.CenterCorrected.printed_iff_even
#print axioms OddMath.Frontier.CenterCorrected.printed_iff_even_nilHecke
#print axioms OddMath.Frontier.CenterCorrected.decomposition_unique
#print axioms OddMath.Frontier.CenterPoly.kernel_inter_center
#print axioms OddMath.Frontier.CenterPoly.even_rank
#print axioms OddMath.Frontier.CenterPoly.odd_rank
#print axioms OddMath.Frontier.CenterPoly.separate
#print axioms OddMath.Frontier.CenterONH.center_kernel
#print axioms OddMath.Frontier.CenterONH.center_nilHecke
#print axioms OddMath.Frontier.CenterONH.polynomialInclusion_injective
#print axioms OddMath.Frontier.CenterCorrectedAudit.audit_center_oddSymmetric
#print axioms OddMath.Frontier.CenterCorrectedAudit.audit_center_nilHecke
#print axioms OddMath.Frontier.CenterCorrectedAudit.audit_printed_iff_even
#print axioms OddMath.Frontier.CenterCorrectedAudit.audit_printed_iff_even_nilHecke
#print axioms OddMath.Frontier.CenterCorrectedAudit.audit_decomposition_unique
#print axioms OddMath.Frontier.CenterCorrectedAudit.audit_objects
