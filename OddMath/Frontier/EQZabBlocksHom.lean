import OddMath.Frontier.EQZabBlocks

/-!
# Ellis–Qi, Proposition 4.13 (3): `HOM(Z_a, Z_b)` for any compositions

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Proposition 4.13 (3).

* `OLam_le_TB`: `OΛ̃_n ⊆ OΛ̃_{a_1} ⊠ ⋯ ⊠ OΛ̃_{a_r}`, from the expansion of the twisted elementary
  polynomials over the last block (`elementaryPoly_add`).
* `TBN a N h`: `Z_a = OΛ̃_{a_1} ⊠ ⋯ ⊠ OΛ̃_{a_r}` inside `OPol_N` for `N = a_1 + ⋯ + a_r`, a right
  `OΛ̃_N`-module by right multiplication (`TBN.module`), with the basis of Proposition 4.13 (1)
  as a `Module.Basis` (`basisTBN`).
* **Proposition 4.13 (3)** (`prop_4_13_three`): right `OΛ̃_N`-linear maps `Z_a → Z_b` are
  matrices `Idx a × Idx b → OΛ̃_N` (`f ↦ (i, j) ↦` the `j`-th coefficient of `f(b_i)`); there are
  `(N! / a_1! ⋯ a_r!) (N! / b_1! ⋯ b_s!)` entries (`card_Idx`). The grading is treated in
  `EQZabBlocksRank`.
-/

namespace OddMath.Frontier.EQBlocks

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential (theta elementary)
open OddMath.Frontier.EQZab (inclX inclY tauAB)
open OddMath.Frontier.SmallRank (OLam)
open FiniteCompleteElementary MulOpposite
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqBlocksHNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqBlocksHNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- `ẽ_j(x, y) = Σ_{p+q=j} (-1)^{mq} ẽ_p(x) ẽ_q(y)` for `m` variables `x`. -/
theorem elementaryPoly_add (m k j : ℕ) :
    elementaryPoly (m+k) j = ∑ p ∈ Finset.range (j+1),
      ((-1 : ℤ) ^ m) ^ (j - p) • (inclX m k (elementaryPoly m p) * inclY m k (elementaryPoly k (j - p))) := by
  rw [← EQFix.theta_elementary, ← EQZab.tauAB_epsAB, EQZab.elementary_add,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, EQZab.epsAB_inclX, EQZab.epsAB_inclY_elementary, mul_smul_comm, map_zsmul,
    map_mul, EQZab.tauAB_inclX, EQZab.tauAB_inclY, EQFix.theta_elementary, EQFix.theta_elementary]

/-- `OΛ̃_n ⊆ OΛ̃_{a_1} ⊠ ⋯ ⊠ OΛ̃_{a_r}`. -/
theorem OLam_le_TB : ∀ a : List ℕ, OLam (blocksN a) ≤ TB a
  | [] => fun _ _ => trivial
  | k :: a => by
    show OLam (blocksN a + k) ≤ TB (k :: a)
    rw [SmallRank.OLam_eq_elementaryClosure, Subring.closure_le]
    rintro _ ⟨j, -, -, rfl⟩
    rw [elementaryPoly_add]
    refine Subring.sum_mem _ fun p _ => Subring.zsmul_mem _ (Subring.mul_mem _ ?_ ?_) _
    · exact inclX_mem_TB (OLam_le_TB a (elementaryPoly_mem_OLam _ p))
    · exact inclY_elementaryPoly_mem_TB a k _

/-- `Z_a` inside `OPol_N` for `N = a_1 + ⋯ + a_r`. -/
def TBN (a : List ℕ) (N : ℕ) (h : blocksN a = N) : Subring (SkewPolynomial N) := h ▸ TB a

theorem OLam_le_TBN (a : List ℕ) (N : ℕ) (h : blocksN a = N) : OLam N ≤ TBN a N h := by
  subst h; exact OLam_le_TB a

/-- `Z_a` is a right `OΛ̃_N`-module by right multiplication. -/
abbrev TBN.module (a : List ℕ) (N : ℕ) (h : blocksN a = N) :
    Module (OLam N)ᵐᵒᵖ (TBN a N h) :=
  Module.compHom (TBN a N h) (Subring.inclusion (OLam_le_TBN a N h)).op

attribute [local instance] TBN.module

theorem TBN.op_smul_coe {a : List ℕ} {N : ℕ} {h : blocksN a = N} (c : OLam N) (x : TBN a N h) :
    ((op c • x : TBN a N h) : SkewPolynomial N) = (x : SkewPolynomial N) * c := rfl

/-- **Proposition 4.13 (1)** as a `Module.Basis` of the right `OΛ̃_N`-module `Z_a`. -/
def basisTBN (a : List ℕ) (N : ℕ) (h : blocksN a = N) :
    Module.Basis (Idx a) (OLam N)ᵐᵒᵖ (TBN a N h) := by
  subst h
  refine Module.Basis.mk (v := fun i => ⟨Bas a i, Bas_mem a i⟩) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : ∑ i, Bas a i * ((g i).unop : SkewPolynomial (blocksN a)) = 0 := by
      have := congrArg (fun x : TBN a (blocksN a) rfl => (x : SkewPolynomial (blocksN a))) hg
      simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at this
      exact (Finset.sum_congr rfl fun i _ => rfl).trans this
    have := prop_4_13_one_indep a (fun i => ((g i).unop : SkewPolynomial (blocksN a)))
      (fun i => (g i).unop.2) h0 i
    exact unop_injective (Subtype.ext this)
  · rintro x -
    obtain ⟨c, hc, e⟩ := prop_4_13_one_span a x.2
    have : x = ∑ i, op (⟨c i, hc i⟩ : OLam (blocksN a)) •
        (⟨Bas a i, Bas_mem a i⟩ : TBN a (blocksN a) rfl) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, TBN.op_smul_coe]
      exact e
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem basisTBN_apply (a : List ℕ) (i : Idx a) :
    ((basisTBN a (blocksN a) rfl i : TBN a (blocksN a) rfl) : SkewPolynomial (blocksN a)) =
      Bas a i := by
  simp [basisTBN]

/-- **Ellis–Qi, Proposition 4.13 (3)**: right `OΛ̃_N`-linear maps `Z_a → Z_b` correspond to
matrices `Idx a × Idx b → OΛ̃_N`, `f ↦ (i, j) ↦ (j-th coefficient of f(b_i))`. -/
def prop_4_13_three (a b : List ℕ) (N : ℕ) (ha : blocksN a = N) (hb : blocksN b = N) :
    (TBN a N ha →ₗ[(OLam N)ᵐᵒᵖ] TBN b N hb) ≃+ (Idx a → Idx b → (OLam N)ᵐᵒᵖ) :=
  ((basisTBN a N ha).constr ℕ).symm.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (basisTBN b N hb).equivFun.toAddEquiv)

theorem prop_4_13_three_apply (a b : List ℕ) (N : ℕ) (ha : blocksN a = N) (hb : blocksN b = N)
    (f : TBN a N ha →ₗ[(OLam N)ᵐᵒᵖ] TBN b N hb) (i : Idx a) (j : Idx b) :
    prop_4_13_three a b N ha hb f i j = (basisTBN b N hb).repr (f (basisTBN a N ha i)) j := rfl

end

end OddMath.Frontier.EQBlocks
