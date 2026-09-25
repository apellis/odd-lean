import OddMath.Frontier.OddSymmetrizer
import OddMath.Frontier.NilCoxeterWords
import OddMath.Frontier.PbwEquivalence
import OddMath.Frontier.NilHeckeBasis
import OddMath.Frontier.ZeroHecke

/-! # Polynomials inside the odd nilHecke ring

EKL arXiv:1111.1320v1, §2.2 and (2.64), §4.1.2 (4.8).  The polynomial subring `OPol_a ⊂ ONH_a`
(dots) as a ring hom `polyElem`, acting by left multiplication, and two identities used for thick
calculus: `D_a g D_a = D_a(g) D_a` for every polynomial `g`, and the ring form of (2.64),
`D_a f = f^{w_0} D_a` for `f ∈ OΛ_a`. -/
namespace OddMath.Frontier.OnhPolynomial
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords LongestDivided

variable {n : ℕ}

/-- The dot subring: `OPol_{n+2} → ONH_{n+2}`. -/
noncomputable def polyElem (n : ℕ) : SkewPolynomial (n+2) →+* Presented n :=
  (NilHeckeBasis.dotMap n).comp (PbwEquivalence.presentedEquiv (n+2)).symm.toRingHom

/-- Left multiplication as a ring hom into the endomorphism ring. -/
noncomputable def lmulHom (n : ℕ) : SkewPolynomial (n+2) →+* Module.End ℤ (SkewPolynomial (n+2)) where
  toFun g := LinearMap.mulLeft ℤ g
  map_one' := LinearMap.ext fun f => one_mul f
  map_mul' g h := LinearMap.ext fun f => mul_assoc g h f
  map_zero' := LinearMap.ext fun f => zero_mul f
  map_add' g h := LinearMap.ext fun f => add_mul g h f

@[simp] theorem lmulHom_apply (g f : SkewPolynomial (n+2)) : lmulHom n g f = g * f := rfl

theorem action_comp_polyElem (n : ℕ) : (action n).comp (polyElem n) = lmulHom n := by
  have h : (action n).comp (NilHeckeBasis.dotMap n) =
      (lmulHom n).comp (PbwEquivalence.presentedEquiv (n+2)).toRingHom := by
    apply SignedPermutation.presentedHom_ext
    intro j
    apply LinearMap.ext
    intro f
    simp only [RingHom.coe_comp, Function.comp_apply, NilHeckeBasis.dotMap_q,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, PbwEquivalence.presentedEquiv_apply,
      PbwL3.Phi_q, lmulHom_apply, action_dot_apply]
  ext g : 1
  obtain ⟨x, rfl⟩ := (PbwEquivalence.presentedEquiv (n+2)).surjective g
  have := congrArg (fun φ => φ x) h
  simpa [polyElem] using this

theorem action_polyElem (g f : SkewPolynomial (n+2)) :
    action n (polyElem n g) f = g * f := by
  have := congrArg (fun φ => φ g f) (action_comp_polyElem n)
  simpa using this

theorem polyElem_monomial (A : Fin (n+2) → ℕ) :
    polyElem n (monomial A 1) = NilHeckeBasis.dotMonomial A := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  rw [action_polyElem, NilHeckeBasis.action_dotMonomial]

theorem polyElem_generator (j : Fin (n+2)) : polyElem n (generator j) = dot n j := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  rw [action_polyElem, action_dot_apply]

/-- `D_a g D_a = D_a(g) D_a` in `ONH_a`, for every polynomial `g`. -/
theorem DElem_poly_DElem (g : SkewPolynomial (n+2)) :
    ZeroHecke.DElem n * polyElem n g * ZeroHecke.DElem n =
      polyElem n (D (n+2) g) * ZeroHecke.DElem n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  simp only [map_mul, Module.End.mul_apply, action_polyElem, ZeroHecke.action_DElem]
  exact D_right_kernel n g _ (LongestKernel.D_mem_kernel n f)

/-- EKL (2.64) in `ONH_a`: `D_a f = f^{w_0} D_a` for `f ∈ OΛ_a`. -/
theorem DElem_poly_kernel (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    ZeroHecke.DElem n * polyElem n f =
      polyElem n (SignedPermutation.skewAction (LongestElementary.longest (n+2)) f) *
        ZeroHecke.DElem n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro g
  simp only [map_mul, Module.End.mul_apply, action_polyElem, ZeroHecke.action_DElem]
  exact OddSymmetrizer.D_left_kernel n f g hf

end OddMath.Frontier.OnhPolynomial
