/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GrothendieckPresentation
import OddMath.QuiverHecke.CoefficientLocalization
import OddMath.CoveringQuantum.UDot.LFormRestriction
import OddMath.SKM.GrothendieckShift

/-!
# The homomorphism `γ` on the `ℒ`-form of `U̇_{q,π}(𝔤)`

Brundan–Ellis, arXiv:1701.04133v2, existence part of Theorem 11.7. The proof in the paper
extends scalars to `𝕃 = ℚ(q)[π]/(π² - 1)`: the homomorphism `γ` over `ℒ` of
`GrothendieckPresentation` gives an `𝕃`-algebra homomorphism `U̇_{q,π}(𝔤)_𝕃 → 𝕃 ⊗_ℒ K₀(𝔘̇(𝔤))`
sending the divided powers `e_i^{(n)} 1_λ`, `f_i^{(n)} 1_λ` to the classes of the
divided-power objects by Lemma 11.5 (`CoveringQuantum.UDot.baseHom`). Since `𝕃` is a
localization of `ℒ` at nonzero elements of `ℤ[q, q⁻¹]` (`Coefficients.isLocalization`) and
`K₀(𝔘̇(𝔤))` has no `ℤ[q, q⁻¹]`-torsion (`SKM.UDot.int_smul_eq_zero`), `x ↦ 1 ⊗ x` is injective
(`toBase_injective`), so the base change restricts to the `ℒ`-form (9.5) with values in
`K₀(𝔘̇(𝔤))` (`CoveringQuantum.UDot.lFormHom`).

* `gammaInt`: the `ℒ`-algebra homomorphism `U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))`;
* `theorem_11_7_existence`: it is the unique `ℒ`-algebra homomorphism sending `1_λ`,
  `e_i^{(n)} 1_λ`, `f_i^{(n)} 1_λ` to `[1_λ]`, `[E_i^{(n)} 1_λ]`, `[F_i^{(n)} 1_λ]`.

As in `SKM.UDot.int_smul_eq_zero`, the ground field is a field (BE2 §11), the scalars satisfy
the hypotheses of §9 (`CScalars`, homogeneous), and the symmetrizer has finitely many colours in
each degree (`DegreeLocallyFinite`). The last hypothesis is needed by the current proof of the
torsion-freeness of `K₀` (bounded-below graded hom spaces); BE2 allows any index set. The
surjectivity in Theorem 11.7 is a separate step.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LaurentPolynomial
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type w} [Field k]

namespace SerreComplex

open SKM.K0Relations CoveringQuantum CoveringQuantum.UDot

variable (Q : CoveringQuantum.RootDatum I X) {S : SKM.Scalars Q.toSKM k} (hS : S.Homogeneous)

theorem ofLaurent_qUnit :
    Coefficients.ofLaurentHom (qUnit 1 : LaurentPolynomial Zπ) = (Coefficients.q : Coefficients.Ring) := by
  change Coefficients.ofLaurent (T 1) = _
  rw [Coefficients.ofLaurent, eval₂_T, zpow_one]

theorem ofLaurent_pi : Coefficients.ofLaurentHom (C Zπ.π) = Coefficients.pi :=
  Coefficients.ofLaurent_C_pi

theorem qpFact_isUnit (i : I) (n : ℕ) :
    IsUnit (qpFact (Q.qi Coefficients.q i) (Q.pii Coefficients.pi i) n) :=
  Coefficients.qpFact_isUnit Q.toSuperCartanDatum i n

theorem gammaL_epow' (i : I) (n : ℕ) (μ : X) :
    gammaL Q hS (UDot.mk Q (qUnit 1) (C Zπ.π) (UDot.epow Q i n μ)) =
      qpFact (Q.qi (qUnit 1) i) (Q.pii (C Zπ.π) i) n •
        Unitization.inrNonUnitalAlgHom (LaurentPolynomial Zπ) (Grothendieck S Q.skmSymmetrizer hS)
          (Edp Q.skmSymmetrizer hS i n _ μ (wt_rep μ n) (Q.d i * (n.choose 2 : ℕ))
            (((n.choose 2 : ℕ) : ZMod 2) * Q.parity i)) :=
  (gammaL_epow Q hS i n μ).trans (inr_smul' Q hS _ _).symm

theorem gammaL_fpow' (i : I) (n : ℕ) (μ : X) :
    gammaL Q hS (UDot.mk Q (qUnit 1) (C Zπ.π) (UDot.fpow Q i n μ)) =
      qpFact (Q.qi (qUnit 1) i) (Q.pii (C Zπ.π) i) n •
        Unitization.inrNonUnitalAlgHom (LaurentPolynomial Zπ) (Grothendieck S Q.skmSymmetrizer hS)
          (Fdp Q.skmSymmetrizer hS i n _ (-μ) (wt_rep (-μ) n) (-(Q.d i * (n.choose 2 : ℕ))) 0) :=
  (gammaL_fpow Q hS i n μ).trans (inr_smul' Q hS _ _).symm

variable (cs : SKM.CScalars S) (hf : Q.skmSymmetrizer.DegreeLocallyFinite)

include cs hf in
/-- **Extension of scalars to `𝕃` is injective on `K₀(𝔘̇(𝔤))`**: `x ↦ 1 ⊗ x` from `K₀(𝔘̇(𝔤))`
to `𝕃 ⊗_ℒ K₀(𝔘̇(𝔤))` (with an identity adjoined). -/
theorem toBase_injective :
    Function.Injective (includeB (k := LaurentPolynomial Zπ) (k' := Coefficients.Ring) (A := GrUnit Q hS)
      (B := Grothendieck S Q.skmSymmetrizer hS)
      (Unitization.inrNonUnitalAlgHom (LaurentPolynomial Zπ) (Grothendieck S Q.skmSymmetrizer hS))) := by
  have := Coefficients.isLocalization
  refine includeB_injective Coefficients.intDenominators
    (Unitization.sndHom (LaurentPolynomial Zπ) (LaurentPolynomial Zπ) _)
    (fun b ↦ Unitization.snd_inr (LaurentPolynomial Zπ) b) ?_
  rintro _ ⟨p, hp, rfl⟩ b hb
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact nonZeroDivisors.ne_zero (Submonoid.mem_comap.mp hp) (map_zero _)
  apply MulOpposite.unop_injective
  exact SKM.UDot.int_smul_eq_zero Q.skmSymmetrizer cs hS hf p hp0 b.unop (congrArg MulOpposite.unop hb)

/-- **The homomorphism `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` of BE2 Theorem 11.7.** -/
def gammaInt : lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ) →ₙₐ[LaurentPolynomial Zπ]
    Grothendieck S Q.skmSymmetrizer hS := by
  refine lFormHom (k := LaurentPolynomial Zπ) (k' := Coefficients.Ring) (A := GrUnit Q hS)
    (B := Grothendieck S Q.skmSymmetrizer hS)
    (j := Unitization.inrNonUnitalAlgHom (LaurentPolynomial Zπ) (Grothendieck S Q.skmSymmetrizer hS))
    (g := gammaL Q hS) (q' := Coefficients.q) (π' := Coefficients.pi) ?_ ?_ ?_
    (one S Q.skmSymmetrizer hS)
    (fun i n μ ↦ Edp Q.skmSymmetrizer hS i n _ μ (wt_rep μ n) (Q.d i * (n.choose 2 : ℕ))
      (((n.choose 2 : ℕ) : ZMod 2) * Q.parity i))
    (fun i n μ ↦ Fdp Q.skmSymmetrizer hS i n _ (-μ) (wt_rep (-μ) n) (-(Q.d i * (n.choose 2 : ℕ))) 0)
    ?_ ?_ ?_ ?_
  · exact ofLaurent_qUnit
  · exact ofLaurent_pi
  · exact qpFact_isUnit Q
  · exact gammaL_one Q hS
  · exact gammaL_epow' Q hS
  · exact gammaL_fpow' Q hS
  · exact toBase_injective Q hS cs hf

theorem gammaInt_one (μ : X) :
    gammaInt Q hS cs hf ⟨_, one_mem_lForm Q Coefficients.q Coefficients.pi _ μ⟩ =
      one S Q.skmSymmetrizer hS μ :=
  lFormHom_one _ _ _ _ _ _ _ _ _ _ μ

theorem gammaInt_edp (i : I) (n : ℕ) (μ : X) :
    gammaInt Q hS cs hf ⟨_, edp_mem_lForm Q Coefficients.q Coefficients.pi _ i n μ⟩ =
      Edp Q.skmSymmetrizer hS i n _ μ (wt_rep μ n) (Q.d i * (n.choose 2 : ℕ))
        (((n.choose 2 : ℕ) : ZMod 2) * Q.parity i) :=
  lFormHom_edp _ _ _ _ _ _ _ _ _ _ i n μ

theorem gammaInt_fdp (i : I) (n : ℕ) (μ : X) :
    gammaInt Q hS cs hf ⟨_, fdp_mem_lForm Q Coefficients.q Coefficients.pi _ i n μ⟩ =
      Fdp Q.skmSymmetrizer hS i n _ (-μ) (wt_rep (-μ) n) (-(Q.d i * (n.choose 2 : ℕ))) 0 :=
  lFormHom_fdp _ _ _ _ _ _ _ _ _ _ i n μ

theorem gammaInt_unique
    (ψ : lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ) →ₙₐ[LaurentPolynomial Zπ]
      Grothendieck S Q.skmSymmetrizer hS)
    (h1 : ∀ μ, ψ ⟨_, one_mem_lForm Q Coefficients.q Coefficients.pi _ μ⟩ =
      one S Q.skmSymmetrizer hS μ)
    (h2 : ∀ i n μ, ψ ⟨_, edp_mem_lForm Q Coefficients.q Coefficients.pi _ i n μ⟩ =
      Edp Q.skmSymmetrizer hS i n _ μ (wt_rep μ n) (Q.d i * (n.choose 2 : ℕ))
        (((n.choose 2 : ℕ) : ZMod 2) * Q.parity i))
    (h3 : ∀ i n μ, ψ ⟨_, fdp_mem_lForm Q Coefficients.q Coefficients.pi _ i n μ⟩ =
      Fdp Q.skmSymmetrizer hS i n _ (-μ) (wt_rep (-μ) n) (-(Q.d i * (n.choose 2 : ℕ))) 0) :
    ψ = gammaInt Q hS cs hf := by
  refine lForm_hom_ext (k := LaurentPolynomial Zπ) (k' := Coefficients.Ring)
    (B := Grothendieck S Q.skmSymmetrizer hS) (ψ := ψ) (ψ' := gammaInt Q hS cs hf) ?_ ?_ ?_
  · exact fun μ ↦ (h1 μ).trans (gammaInt_one Q hS cs hf μ).symm
  · exact fun i n μ ↦ (h2 i n μ).trans (gammaInt_edp Q hS cs hf i n μ).symm
  · exact fun i n μ ↦ (h3 i n μ).trans (gammaInt_fdp Q hS cs hf i n μ).symm

include cs hf in
/-- **BE2 Theorem 11.7, existence of `γ`** (arXiv:1701.04133v2). There is a unique
`ℒ`-algebra homomorphism `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` sending `1_λ`, `e_i^{(n)} 1_λ`,
`f_i^{(n)} 1_λ` to the classes `[1_λ]`, `[E_i^{(n)} 1_λ]`, `[F_i^{(n)} 1_λ]` of the divided-power
objects (with the grading shift of Lemma 11.5 as corrected in ERRATA [BE2] 13). Hypotheses: a
ground field, the scalar hypotheses of §9, and the route hypothesis `DegreeLocallyFinite` (see
the module docstring). -/
theorem theorem_11_7_existence :
    ∃! γ : lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ) →ₙₐ[LaurentPolynomial Zπ]
        Grothendieck S Q.skmSymmetrizer hS,
      (∀ μ, γ ⟨_, one_mem_lForm Q Coefficients.q Coefficients.pi _ μ⟩ =
        one S Q.skmSymmetrizer hS μ) ∧
      (∀ i n μ, γ ⟨_, edp_mem_lForm Q Coefficients.q Coefficients.pi _ i n μ⟩ =
        Edp Q.skmSymmetrizer hS i n _ μ (wt_rep μ n) (Q.d i * (n.choose 2 : ℕ))
          (((n.choose 2 : ℕ) : ZMod 2) * Q.parity i)) ∧
      (∀ i n μ, γ ⟨_, fdp_mem_lForm Q Coefficients.q Coefficients.pi _ i n μ⟩ =
        Fdp Q.skmSymmetrizer hS i n _ (-μ) (wt_rep (-μ) n) (-(Q.d i * (n.choose 2 : ℕ))) 0) := by
  exact ⟨gammaInt Q hS cs hf, ⟨gammaInt_one Q hS cs hf, gammaInt_edp Q hS cs hf,
    gammaInt_fdp Q hS cs hf⟩, fun ψ h ↦ gammaInt_unique Q hS cs hf ψ h.1 h.2.1 h.2.2⟩

end SerreComplex
end OddMath.QuiverHecke
