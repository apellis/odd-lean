import OddMath.Frontier.EQFunctorDual
import OddMath.Frontier.EQFixZabCells
import DG.Derived.RightDualEnd

/-!
# Ellis–Qi, Proposition 4.12 (2): `END(Z_{a,b}) = Z_{a,b} ⊗ Z_{a,b}^∨` through rank-one maps

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, the paragraph before Proposition 4.12 and Proposition 4.12 (2).

The source builds endomorphisms of `Z_{a,b}` from the trace pairing,
`Z_{a,b} ⊗_{OΛ_{a+b}} Z_{a,b}^∨ → END_{OΛ_{a+b}^{op}}(Z_{a,b})`, `g z ⊗ z^∨ f ↦ (x ↦ g z · (z^∨ f)(x))`,
calls the algebra they span `E_{a,b}` (defined only diagrammatically), and asserts
`E_{a,b} ≅ END(Z_{a,b})` "by a graded rank count". What is formalized:

* dg-lean (`DG.RightBasis.eq_sum_rankOne`, `DG.RightBasis.rankOne_injective`): for a right module `M`
  with a finite basis `(b_i)` and dual basis `δ_i` (the coefficient maps, `RightBasis.coeffHom`),
  every right-linear additive endomorphism `f` of `M` is `Σ_i f(b_i) · δ_i(−)`, a sum of rank-one
  maps `m · φ(−)` (`rankOne m φ`), and the `m_i` in `Σ_i m_i · δ_i(−)` are unique; so the trace
  pairing map `M ⊗_A M^∨ → END_A(M)` is bijective (`M^∨` being free on the `δ_i`);
* **Proposition 4.12 (2)** for `Z_{a,b}` (`prop_4_12_two`, `prop_4_12_two_unique`): every right
  `OΛ_{a+b}`-linear endomorphism of `Z_{a,b}` is `Σ_μ f(s̃_μ(y) z) · δ_μ(−)`, uniquely; i.e.
  `END_{OΛ_{a+b}^{op}}(Z_{a,b})` is exactly the span of the maps `φ` of the source, free over
  the basis of Corollary 4.8 in each of the `binom(a+b, a)` slots;
* **Proposition 4.12 (2), second isomorphism** (`prop_4_12_two_dual`):
  `END_{OΛ_{a+b}^{op}}(Z_{a,b}) ≅ END_{OΛ_{a+b}}(Z_{a,b}^∨)` as dg algebras, by transposition
  `f ↦ f^∨`, `f^∨(φ) = (-1)^{|f||φ|} φ ∘ f` (dg-lean's `DG.RightBasis.transposeEquiv` for the basis
  of Corollary 4.8). In the conventions of the `DG` library both endomorphism dg rings act on the
  right (`DG.DGModule.END`), so the isomorphism lands in the graded opposite of
  `END_{OΛ_{a+b}}(Z_{a,b}^∨)`; in the source's conventions (`END(Z_{a,b})` acting on the left of the
  right module `Z_{a,b}`, `END(Z^∨_{a,b})` on the right of the left module `Z^∨_{a,b}`) this is the
  printed isomorphism.
-/

namespace OddMath.Frontier.EQFunctor

open DG MulOpposite


variable (a b : ℕ)

/-- **Ellis–Qi, Proposition 4.12 (2)** (spanning): every right `OΛ_{a+b}`-linear endomorphism `f`
of `Z_{a,b}` is the sum `Σ_μ f(s̃_μ(y) z) · δ_μ(−)` of the trace-pairing maps of the source. -/
theorem prop_4_12_two (f : EQFix.Zab a b →+ EQFix.Zab a b)
    (hf : ∀ (c : EQSkewDifferential.osymDG (a+b)) (x : EQFix.Zab a b), f (op c • x) = op c • f x) :
    f = ∑ μ, rankOne (f ((zabRightBasis a b).b μ)) ((zabRightBasis a b).coeffHom μ) :=
  (zabRightBasis a b).eq_sum_rankOne f hf

/-- **Ellis–Qi, Proposition 4.12 (2)** (uniqueness): `Σ_μ m_μ · δ_μ(−)` determines the `m_μ ∈ Z_{a,b}`;
so the trace pairing `Z_{a,b} ⊗ Z_{a,b}^∨ → END(Z_{a,b})` is injective. -/
theorem prop_4_12_two_unique (m m' : EQFix.ParIdx a b → EQFix.Zab a b)
    (h : ∑ μ, rankOne (m μ) ((zabRightBasis a b).coeffHom μ) =
      ∑ μ, rankOne (m' μ) ((zabRightBasis a b).coeffHom μ)) : m = m' := by
  classical
  exact (zabRightBasis a b).rankOne_injective m m' h

attribute [local instance] EQFix.zabOpModule EQFix.zabOpDGModule

/-- **Ellis–Qi, Proposition 4.12 (2)**, `END_{OΛ_{a+b}^{op}}(Z_{a,b}) ≅ END_{OΛ_{a+b}}(Z^∨_{a,b})`:
transposition `f ↦ f^∨`, `f^∨(φ) = (-1)^{|f||φ|} φ ∘ f`, is an isomorphism of dg `ℤ`-algebras from
the endomorphism dg ring of the right dg `OΛ_{a+b}`-module `Z_{a,b}` (a left dg `OΛ_{a+b}ᵒᵖ`-module)
onto the graded opposite of the endomorphism dg ring of the left dg `OΛ_{a+b}`-module
`Z^∨_{a,b}` (`DG.DGModule.END` lets both act on the right). -/
noncomputable def prop_4_12_two_dual :
    DG.DGModule.END (EQFix.OsymOp (a+b)) (EQFix.Zab a b) ≃ᵈᵍₐ[ℤ]
      DG.GradedOpposite (DG.DGAlgebra.gradingSubmodule ℤ
        (DG.DGModule.END (EQSkewDifferential.osymDG (a+b)) (ZDual a b))) :=
  (zabRightBasis a b).transposeEquiv ℤ

/-- The isomorphism of `prop_4_12_two_dual` is transposition: on an endomorphism `f` of degree `n`
and a homogeneous `φ ∈ Z^∨_{a,b}` of degree `k`, `f^∨(φ) = (-1)^{n k} φ ∘ f`. -/
theorem prop_4_12_two_dual_apply {n k : ℤ} (f : DG.Cochain (EQFix.OsymOp (a+b)) (EQFix.Zab a b) (EQFix.Zab a b) n)
    {φ : ZDual a b} (hφ : φ ∈ DG.grading k) (x : EQFix.Zab a b) :
    RightDual.toHom (RightDual.transpose f φ) x = koszulSign (n * k) • RightDual.toHom φ (f x) :=
  RightDual.toHom_transpose f hφ x

theorem prop_4_12_two_dual_of (n : ℤ) (f : DG.Cochain (EQFix.OsymOp (a+b)) (EQFix.Zab a b) (EQFix.Zab a b) n) :
    prop_4_12_two_dual a b (DirectSum.of _ n f) =
      DG.GradedOpposite.op _ (DirectSum.of _ n (RightDual.transpose f)) := by
  rw [prop_4_12_two_dual, RightBasis.transposeEquiv_apply, RightDual.transposeRingHom_apply,
    RightDual.transposeSum_of]

end OddMath.Frontier.EQFunctor
