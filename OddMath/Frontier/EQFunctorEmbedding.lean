import OddMath.Frontier.EQFunctorBimodule
import OddMath.Frontier.EQFunctorDual
import OddMath.Frontier.EQOnhDGZn
import OddMath.Frontier.EQOnhDGAcyclic

/-!
# Ellis–Qi, Definition 4.18 and Corollary 4.19: the embedding functor `J`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.18 and Corollary 4.19 (rank `N = n + 2 ≥ 2`).

* `znRightBasis N`: the reversed staircase monomials `x^A 1_z` (`A_i ≤ i`, degree `|A|`) form a
  homogeneous basis of `Z_N` as a right `OΛ_N`-module ((3.38), Proposition 3.16 (1)), with the
  differential lowering the key `-|A|` ((3.37), `znRightBasis_key`).
* `ZnDual n = Z_{n+2}^∨ = HOM_{OΛ_{n+2}}(Z_{n+2}, OΛ_{n+2})`, a dg `(OΛ_{n+2}, ONH_{n+2})`-bimodule;
  `znDualTriangular`, `znDual_isKProjective`: it is finite-cell, hence K-projective, as a left dg
  `OΛ_{n+2}`-module (dual basis, as for Corollary 4.11).
* **Definition 4.18**: `J n = Z_{n+2}^∨ ⊗^L_{ONH_{n+2}} (-) : D(ONH_{n+2}) → D(OΛ_{n+2})`, a
  triangulated functor.
* **Corollary 4.19** for `N ≥ 2`: `J n` is fully faithful (`jFullyFaithful`), since
  `D(ONH_{n+2}) = 0` (Proposition 3.16 (2), `EQOnhDG.ONH.isZero_derivedCategory`), as in the
  printed proof.

Not covered: the components `N = 0, 1` (where `ONH_N = OΛ_N` and `J_N` is the identity up to
isomorphism) and the Grothendieck group statement of Corollary 4.19.
-/

open CategoryTheory Limits

universe w w₁ w₂ w₃ w₄

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial monomial)
open OddMath.Frontier.EQSkewDifferential (osymDG totalDeg twistRev Zn)
open OddMath.Frontier.EQFix (zb zb_mem zc zc_spec zc_unique zcoeff ofOsym toSkew toSkew_mem
  ofOsym_toSkew symm_op_smul_osym zE opO unopO)
open OddMath.Frontier.EQZn (RevStair)
open OddMath.Frontier.EQOnhDG (ONH)
open DG MulOpposite

noncomputable section

/-! ## `Z_N` as a right `OΛ_N`-module with a finite basis -/

/-- **(3.38), Proposition 3.16 (1)**: the `x^A 1_z`, `A_i ≤ i`, of degree `|A|`, form a homogeneous
basis of the right dg `OΛ_N`-module `Z_N`. -/
def znRightBasis (N : ℕ) : RightBasis (osymDG N) (Zn N) (RevStair N) where
  b := zb
  deg A := totalDeg A.val
  b_mem := zb_mem
  coeff x A := ofOsym (zc x A)
  sum_coeff x := by
    apply (zE N).symm.injective
    rw [map_sum, zc_spec x]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [symm_op_smul_osym]
    rfl
  coeff_sum a := by
    set y := ∑ A, op (a A) • zb A
    have hy : (zE N).symm y = ∑ A, monomial A.val 1 *
        twistRev N ((⟨toSkew (a A), toSkew_mem _⟩ : EQSkewDifferential.osym N) :
          SkewPolynomial N) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun A _ => by rw [symm_op_smul_osym]; rfl
    have hc := zc_unique y _ hy
    funext A
    rw [← hc]
    rfl

/-- **(3.37)**: `d(x^A 1_z)` only involves the `x^B 1_z` with `|B| = |A| + 1`. -/
theorem znRightBasis_key {N : ℕ} (A B : RevStair N)
    (h : (znRightBasis N).coeff (DG.d ((znRightBasis N).b A)) B ≠ 0) :
    -totalDeg B.val < -totalDeg A.val := by
  refine EQFix.zn_key A B fun h0 => h ?_
  have h1 := congrArg (fun x => Shift.twist (osymDG N) (totalDeg B.val) (unopO N x)) h0
  change Shift.twist (osymDG N) (totalDeg B.val) (unopO N (opO N
    (Shift.twist (osymDG N) (totalDeg B.val) (ofOsym (zc (DG.d (zb A)) B))))) =
    Shift.twist (osymDG N) (totalDeg B.val) (unopO N 0) at h1
  rw [GradedOpposite.unop_op, Shift.twist_twist_self, map_zero, map_zero] at h1
  exact h1

/-! ## The dual bimodule `Z_N^∨` -/

/-- **`Z_{n+2}^∨ = HOM_{OΛ_{n+2}}(Z_{n+2}, OΛ_{n+2})`**: the graded dual of the right dg
`OΛ_{n+2}`-module `Z_{n+2}`. -/
abbrev ZnDual (n : ℕ) : Type := RightDual (osymDG (n+2)) (Zn (n+2))

/-- `Z_{n+2}^∨` is a dg `(OΛ_{n+2}, ONH_{n+2})`-bimodule: `(c f)(z) = c f(z)`,
`(f p)(z) = f(p z)`. -/
instance ZnDual.instDGBimodule (n : ℕ) : DGBimodule (osymDG (n+2)) (ONH n) (ZnDual n) :=
  RightDual.instDGBimodule

/-- The dual basis of `Z_N^∨`, ordered by increasing `|A|`, is triangular. -/
def znDualTriangular (N : ℕ) : DG.TriangularBasis (osymDG N) (RightDual (osymDG N) (Zn N)) :=
  (znRightBasis N).dualTriangular (fun A => -totalDeg A.val) fun l i h => znRightBasis_key l i h

/-- `Z_N^∨` is K-projective (finite-cell) as a left dg `OΛ_N`-module. -/
theorem znDual_isKProjective (N : ℕ) :
    IsKProjective.{w} (osymDG N) (RightDual (osymDG N) (Zn N)) :=
  (znDualTriangular N).isKProjective

/-! ## The functor `J` -/

variable (n : ℕ) [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (ONH n))]
  [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymDG (n+2)))]
  [DG.HasDerivedCategory.{w₃, 0} (ONH n)] [DG.HasDerivedCategory.{w₄, 0} (osymDG (n+2))]

/-- **Ellis–Qi, Definition 4.18**: `J_{n+2} = Z_{n+2}^∨ ⊗^L_{ONH_{n+2}} (-) :
D(ONH_{n+2}) → D(OΛ_{n+2})`. -/
abbrev J : DG.DerivedCategory (ONH n) ⥤ DG.DerivedCategory (osymDG (n+2)) :=
  DGBimodule.derivedTensor.{w₁, w₂, w₃, w₄} (osymDG (n+2)) (ONH n) (ZnDual n)
    (znDual_isKProjective (n+2))

/-- **Ellis–Qi, Corollary 4.19** (`N = n + 2 ≥ 2`): `J_{n+2}` is fully faithful, because
`D(ONH_{n+2})` is zero. -/
def jFullyFaithful : (J.{w₁, w₂, w₃, w₄} n).FullyFaithful where
  preimage {X Y} _ := (EQOnhDG.ONH.isZero_derivedCategory X).to_ Y
  map_preimage {X _} _ :=
    ((J.{w₁, w₂, w₃, w₄} n).map_isZero (EQOnhDG.ONH.isZero_derivedCategory X)).eq_of_src _ _
  preimage_map {X _} _ := (EQOnhDG.ONH.isZero_derivedCategory X).eq_of_src _ _

end

end OddMath.Frontier.EQFunctor
