import OddMath.Frontier.EQZnFiniteCell
import OddMath.Frontier.EQDGStructures
import DG.Homotopy.Homotopy

/-!
# Corollary 3.15 under the dg-module definition of null-homotopy

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2.1 (definition of null-homotopic morphisms) and §3.4, Lemma 3.14, Corollary 3.15.

Corollary 3.15 asserts that for `α ∈ {0,1}ⁿ` not identically `0` the identity of `OPol_n(α)` is
null-homotopic, via the odd derivative `h = ∂/∂x_i` with `α_i = 1`. This `h` is additive but
not `OPol_n`-linear, so the statement holds for the underlying complex
(`EQSkewDifferential.cor_3_15`). §2.2.1 defines null-homotopies of morphisms of dg modules over
`A` as homogeneous `A`-module maps of degree `-1`; with `A = OPol_n` this reading of
Corollary 3.15 is false for **every** `n ≥ 0` and **every** `α ∈ ℤⁿ` (in particular every
`α ∈ {0,1}ⁿ`):

* `no_homotopy_of_generator`: if `h : OPol_n → OPol_n` is additive and `h(x_j)` has no constant
  term for all `j`, then `(d_α h + h d_α)(1_α) ≠ 1_α`. Indeed `d_α(h(1_α))` has no constant term
  (`EQZn.dAlpha_apply_zero`) and `h(d_α 1_α) = Σ α_i h(x_i)`.
* `cor_3_15_superLinear_false`: no odd left `OPol_n`-linear map in the super sense
  (`h(x_j f) = -x_j h(f)`, the sign convention of (2.9)) satisfies `d_α h + h d_α = id`;
  `cor_3_15_linear_false`: nor does any left `OPol_n`-linear map (`h(x_j f) = x_j h(f)`).
* `cor_3_15_dg_false`: in the `DG` library, `OPol_n(α)` (`α = 𝟙_S ∈ {0,1}ⁿ`,
  `EQSkewDifferential.OPolAlpha n S`) is not contractible as a left dg `OPol_n`-module,
  `¬ DG.IsContractible (OPol n) (OPolAlpha n S)`, for all `n` and `S` (a null-homotopy there is
  a cochain of degree `-1`, i.e. a Koszul-signed `OPol_n`-linear map).

For `α ≠ 0` the dg module `OPol_n(α)` is nevertheless acyclic (`EQSkewDifferential.acyclic`),
hence zero in the derived category; it is not zero in the homotopy category. The remark after
Corollary 3.15 (`∂/∂x_2` as a null-homotopy of `id_{Z_n}` as a left `OPol_n`-module) is the case
`α = (0,1,0,1,…)` (`EQZn.zn_not_contractible`).
-/

namespace OddMath.Frontier.EQFix

open OddMath.SkewPolynomial (SkewPolynomial generator)
open EQSkewDifferential (dAlpha dAlpha_apply sAlpha OPol OPolAlpha indicator)
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqFixNHNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqFixNHNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-- If `h(x_j)` has no constant term for every `j`, then `(d_α h + h d_α)(1_α) ≠ 1_α`: the
left-hand side has no constant term. Valid for every `n` and every `α ∈ ℤⁿ`. -/
theorem no_homotopy_of_generator (α : Fin n → ℤ) (h : SkewPolynomial n →+ SkewPolynomial n)
    (hgen : ∀ j, (h (generator j)) 0 = 0) : dAlpha α (h 1) + h (dAlpha α 1) ≠ 1 := by
  intro h1
  have hD1 : dAlpha α 1 = ∑ i, α i • generator i := by
    rw [dAlpha_apply, EQSkewDifferential.d_one, map_one, one_mul, zero_add, sAlpha]
  have h0 := congrArg (fun p : SkewPolynomial n => p 0) h1
  simp only [Finsupp.add_apply, EQZn.dAlpha_apply_zero, zero_add, hD1, map_sum, map_zsmul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, hgen, smul_zero, Finset.sum_const_zero] at h0
  exact EKLSectionTwo.one_apply_zero n h0.symm

/-- **Ellis–Qi, Corollary 3.15 is false for dg `OPol_n`-modules** (super sign convention): for
every `n` and every `α ∈ ℤⁿ`, no odd left `OPol_n`-linear map `h` (`h(x_j f) = -x_j h(f)`) on
`OPol_n(α)` satisfies `d_α h + h d_α = id`. -/
theorem cor_3_15_superLinear_false (α : Fin n → ℤ) :
    ¬ ∃ h : SkewPolynomial n →+ SkewPolynomial n,
      (∀ j f, h (generator j * f) = -(generator j * h f)) ∧
      ∀ f, dAlpha α (h f) + h (dAlpha α f) = f := by
  rintro ⟨h, hlin, hhom⟩
  refine no_homotopy_of_generator α h (fun j => ?_) (hhom 1)
  have := hlin j 1
  rw [mul_one] at this
  rw [this, Finsupp.neg_apply, EQZn.generator_mul_apply_zero, neg_zero]

/-- **Ellis–Qi, Corollary 3.15 is false for dg `OPol_n`-modules** (strictly linear maps): for
every `n` and every `α ∈ ℤⁿ`, no left `OPol_n`-linear map `h` (`h(x_j f) = x_j h(f)`) on
`OPol_n(α)` satisfies `d_α h + h d_α = id`. -/
theorem cor_3_15_linear_false (α : Fin n → ℤ) :
    ¬ ∃ h : SkewPolynomial n →+ SkewPolynomial n,
      (∀ j f, h (generator j * f) = generator j * h f) ∧
      ∀ f, dAlpha α (h f) + h (dAlpha α f) = f := by
  rintro ⟨h, hlin, hhom⟩
  refine no_homotopy_of_generator α h (fun j => ?_) (hhom 1)
  have := hlin j 1
  rw [mul_one] at this
  rw [this, EQZn.generator_mul_apply_zero]

/-- **Ellis–Qi, Corollary 3.15 is false for dg `OPol_n`-modules** (`DG` library form): for every
`n` and every `S ⊆ {0, …, n-1}` (`α = 𝟙_S`, including `α ≠ 0`), `OPol_n(α)` is not contractible
as a left dg `OPol_n`-module. -/
theorem cor_3_15_dg_false (S : Finset (Fin n)) : ¬ DG.IsContractible (OPol n) (OPolAlpha n S) := by
  rintro ⟨h⟩
  apply cor_3_15_superLinear_false (indicator S)
  let e := OPolAlpha.equiv n S
  let H : SkewPolynomial n →+ SkewPolynomial n :=
    { toFun := fun f => e.symm (h.hom (e f))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun f g => by rw [map_add, map_add, map_add] }
  have hmul : ∀ j f, e (generator j * f) = OPol.x j • e f := fun j f => rfl
  refine ⟨H, fun j f => ?_, fun f => ?_⟩
  · change e.symm (h.hom (e (generator j * f))) = -(generator j * e.symm (h.hom (e f)))
    rw [hmul, h.hom.map_smul (OPol.x_mem_grading j),
      show (-1 : ℤ) * 1 = -1 by norm_num, DG.koszulSign_odd (by decide), Units.smul_def,
      Units.val_neg, Units.val_one, neg_one_zsmul, map_neg, OPolAlpha.symm_smul]
    rfl
  · have hc := h.comm (e f)
    rw [DG.DGModuleHom.zero_apply, add_zero, DG.DGModuleHom.id_apply] at hc
    have hd : ∀ z, dAlpha (indicator S) (e.symm z) = e.symm (DG.d z) := fun z => by
      rw [OPolAlpha.symm_d]
    change dAlpha (indicator S) (e.symm (h.hom (e f))) +
      e.symm (h.hom (e (dAlpha (indicator S) f))) = f
    rw [hd, ← OPolAlpha.d_equiv, ← map_add, ← hc, AddEquiv.symm_apply_apply]

end

end OddMath.Frontier.EQFix
