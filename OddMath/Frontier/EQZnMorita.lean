import OddMath.Frontier.EQMoritaBasis
import OddMath.Frontier.EQFunctorEmbedding
import OddMath.Frontier.EQOnhDGEndIso
import OddMath.Frontier.EQFunctorEmbeddingSmall

/-!
# `Z_n ⊗_{OΛ_n} Z_n^∨ ≅ ONH_n` and `Z_n^∨ ⊗_{ONH_n} Z_n ≅ OΛ_n`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, the bimodule isomorphisms stated after Corollary 4.19 (behind (4.30)–(4.31)), rank
`N = n + 2`.

* `ONH.ofRightLinear φ`: every right `OΛ_N`-linear additive endomorphism `φ` of `Z_N` is the action
  of an element of `ONH_N` (Corollary 3.9 in the form of EKL's `ONH_N ≅ End_{OΛ̃_N}(OPol_N)`,
  `EQZn.onhEndEquiv`), without any homogeneity assumption.
* `ONH.fullAction n`: `ONH_N` acts fully on `Z_N` in the sense of `EQFunctor.FullAction`
  (faithfully, by all right `OΛ_N`-linear endomorphisms, detecting degrees).
* `znTensorDualEquiv n : Z_N ⊗_{OΛ_N} Z_N^∨ ≅ ONH_N`, `z ⊗ f ↦ (w ↦ z f(w))`, an isomorphism of dg
  `(ONH_N, ONH_N)`-bimodules (`znTensorDualEquiv_op_smul`);
* `znDualTensorEquiv n : Z_N^∨ ⊗_{ONH_N} Z_N ≅ OΛ_N`, `f ⊗ z ↦ f(z)`, an isomorphism of dg
  `(OΛ_N, OΛ_N)`-bimodules (`znDualTensorEquiv_op_smul`).

These are the isomorphisms printed after Corollary 4.19, with `Z_n^∨ = HOM_{OΛ_n}(Z_n, OΛ_n)`
(`EQFunctor.ZnDual`).
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.EQSkewDifferential (OPol OPolAlpha Zn osymDG twistRev)
open NilHeckeAction

variable {n : ℕ}

namespace ONH

/-- The additive endomorphism of `OPol_{n+2}` underlying an additive endomorphism of `Z_{n+2}`. -/
def rightLinEnd (φ : Zn (n + 2) →+ Zn (n + 2)) : Module.End ℤ (SkewPolynomial (n + 2)) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun g => (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
        (φ (OPolAlpha.equiv _ _ g))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun g g' => by rw [map_add, map_add, map_add] }

theorem rightLinEnd_mem (φ : Zn (n + 2) →+ Zn (n + 2))
    (hφ : ∀ (c : osymDG (n + 2)) (z : Zn (n + 2)),
      φ (MulOpposite.op c • z) = MulOpposite.op c • φ z) :
    rightLinEnd φ ∈ EQZn.rightOsymEnd (n + 2) := by
  intro g c hc
  let c' : osymDG (n + 2) :=
    ⟨OPol.equiv (n + 2) c, EQSkewDifferential.mem_osymDG.mpr (by rwa [RingEquiv.symm_apply_apply])⟩
  have hsmul : ∀ y : Zn (n + 2), (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
      (MulOpposite.op c' • y) =
        (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm y * twistRev (n + 2) c :=
    fun y => EQSkewDifferential.Zn.symm_op_smul (OPol.equiv (n + 2) c) y
  have h1 : (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2)) (g * twistRev (n + 2) c) :
      Zn (n + 2)) = MulOpposite.op c' • OPolAlpha.equiv _ _ g := by
    apply (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm.injective
    rw [hsmul]
    rfl
  change (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
      (φ (OPolAlpha.equiv _ _ (g * twistRev (n + 2) c))) =
    (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
      (φ (OPolAlpha.equiv _ _ g)) * twistRev (n + 2) c
  rw [h1, hφ, hsmul]

/-- The element of `ONH_{n+2}` acting on `Z_{n+2}` as a given right `OΛ`-linear endomorphism. -/
def ofRightLinear (φ : Zn (n + 2) →+ Zn (n + 2))
    (hφ : ∀ (c : osymDG (n + 2)) (z : Zn (n + 2)),
      φ (MulOpposite.op c • z) = MulOpposite.op c • φ z) : ONH n :=
  equiv n ((EQZn.onhEndEquiv n).symm ⟨rightLinEnd φ, rightLinEnd_mem φ hφ⟩)

theorem ofRightLinear_smul (φ : Zn (n + 2) →+ Zn (n + 2))
    (hφ : ∀ (c : osymDG (n + 2)) (z : Zn (n + 2)),
      φ (MulOpposite.op c • z) = MulOpposite.op c • φ z) (z : Zn (n + 2)) :
    ofRightLinear φ hφ • z = φ z := by
  have h := congrArg Subtype.val
    ((EQZn.onhEndEquiv n).apply_symm_apply ⟨rightLinEnd φ, rightLinEnd_mem φ hφ⟩)
  apply (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm.injective
  have h2 := LinearMap.congr_fun h ((OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm z)
  rw [EQZn.onhEndEquiv_apply] at h2
  change action n ((EQZn.onhEndEquiv n).symm ⟨rightLinEnd φ, rightLinEnd_mem φ hφ⟩)
    ((OPolAlpha.equiv _ _).symm z) = _
  rw [h2]
  rfl

/-- `ONH_{n+2}` acts fully on `Z_{n+2}` (Corollary 3.9). -/
theorem fullAction (n : ℕ) : EQFunctor.FullAction (ONH n) (osymDG (n + 2)) (Zn (n + 2)) where
  faithful _ h := eq_zero_of_forall_smul_eq_zero h
  full φ hφ := ⟨ofRightLinear φ hφ, ofRightLinear_smul φ hφ⟩
  mem_grading _ _ h := mem_grading_of_smul_mem fun {j z} hz => h j z hz

end ONH

end OddMath.Frontier.EQOnhDG

namespace OddMath.Frontier.EQFunctor

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQOnhDG (ONH)
open DG MulOpposite TensorProductOver.RightAction

instance (N : ℕ) : Nonempty (EQZn.RevStair N) := ⟨⟨fun _ => 0, fun _ => Nat.zero_le _⟩⟩

/-- **`Z_N ⊗_{OΛ_N} Z_N^∨ ≅ ONH_N`** (`N = n + 2`) as dg `ONH_N`-modules, `z ⊗ f ↦ (w ↦ z f(w))`;
also right `ONH_N`-linear (`znTensorDualEquiv_op_smul`). -/
def znTensorDualEquiv (n : ℕ) :
    TensorProductOver (osymDG (n + 2)) (Zn (n + 2)) (ZnDual n) ≃ᵈᵍ[ONH n] ONH n :=
  (ONH.fullAction n).mulEquiv (znRightBasis (n + 2))

theorem znTensorDualEquiv_smul (n : ℕ) (z : Zn (n + 2)) (f : ZnDual n) (w : Zn (n + 2)) :
    znTensorDualEquiv n (TensorProductOver.tmul _ z f) • w = op (RightDual.toHom f w) • z :=
  (ONH.fullAction n).rho_smul z f w

theorem znTensorDualEquiv_op_smul (n : ℕ) (p : ONH n)
    (t : TensorProductOver (osymDG (n + 2)) (Zn (n + 2)) (ZnDual n)) :
    znTensorDualEquiv n (op p • t) = op p • znTensorDualEquiv n t :=
  (ONH.fullAction n).mulEquiv_op_smul _ p t

/-- **`Z_N^∨ ⊗_{ONH_N} Z_N ≅ OΛ_N`** (`N = n + 2`) as dg `OΛ_N`-modules, `f ⊗ z ↦ f(z)`; also right
`OΛ_N`-linear (`znDualTensorEquiv_op_smul`). -/
def znDualTensorEquiv (n : ℕ) :
    TensorProductOver (ONH n) (ZnDual n) (Zn (n + 2)) ≃ᵈᵍ[osymDG (n + 2)] osymDG (n + 2) :=
  (ONH.fullAction n).evEquiv (znRightBasis (n + 2))

@[simp] theorem znDualTensorEquiv_tmul (n : ℕ) (f : ZnDual n) (z : Zn (n + 2)) :
    znDualTensorEquiv n (TensorProductOver.tmul _ f z) = RightDual.toHom f z := rfl

theorem znDualTensorEquiv_op_smul (n : ℕ) (c : osymDG (n + 2))
    (t : TensorProductOver (ONH n) (ZnDual n) (Zn (n + 2))) :
    znDualTensorEquiv n (op c • t) = op c • znDualTensorEquiv n t :=
  (ONH.fullAction n).evEquiv_op_smul _ c t

/-! ### Ranks `N ≤ 1`: `ONH_N = OPol_N` -/

section Small

open OddMath.Frontier.EQSkewDifferential (OPol)

variable {N : ℕ} (hN : N ≤ 1)
include hN

theorem toOsym_val (p : OPol N) : ((toOsym hN p : osymDG N) : OPol N) = p := rfl

omit hN in
theorem coeff_op_smul_bz (a : osymDG N) : (znRightBasis N).coeff (op a • bz) stair0 = a := by
  rw [RightBasis.coeff_op_smul, coeff_bz, one_mul]

/-- `OPol_N` (`= ONH_N`, `N ≤ 1`) acts fully on `Z_N`. -/
theorem fullActionSmall : FullAction (OPol N) (osymDG N) (Zn N) where
  faithful p h := by
    have h0 := h bz
    rw [smul_bz hN] at h0
    have h1 := congrArg (fun z => (znRightBasis N).coeff z stair0) h0
    simp only [coeff_op_smul_bz, RightBasis.coeff_zero, Pi.zero_apply] at h1
    rw [← toOsym_val hN p, h1]
    rfl
  full φ hφ := by
    refine ⟨(((znRightBasis N).coeff (φ bz) stair0 : osymDG N) : OPol N), fun z => ?_⟩
    conv_lhs => rw [eq_op_smul_bz hN z]
    conv_rhs => rw [eq_op_smul_bz hN z, hφ, eq_op_smul_bz hN (φ bz)]
    rw [smul_comm, smul_bz hN]
    rfl
  mem_grading p i h := by
    have h0 := h 0 bz bz_mem
    rw [smul_bz hN, add_zero] at h0
    have h1 := (znRightBasis N).coeff_mem h0 stair0
    rw [coeff_op_smul_bz] at h1
    have e : (znRightBasis N).deg stair0 = 0 := by
      simp [znRightBasis, stair0, EQSkewDifferential.totalDeg]
    rw [e, sub_zero] at h1
    exact h1

/-- `Z_N ⊗_{OΛ_N} Z_N^∨ ≅ OPol_N` (`= ONH_N`, `N ≤ 1`) as dg bimodules. -/
def znTensorDualEquivSmall :
    TensorProductOver (osymDG N) (Zn N) (RightDual (osymDG N) (Zn N)) ≃ᵈᵍ[OPol N] OPol N :=
  (fullActionSmall hN).mulEquiv (znRightBasis N)

theorem znTensorDualEquivSmall_op_smul (p : OPol N)
    (t : TensorProductOver (osymDG N) (Zn N) (RightDual (osymDG N) (Zn N))) :
    znTensorDualEquivSmall hN (op p • t) = op p • znTensorDualEquivSmall hN t :=
  (fullActionSmall hN).mulEquiv_op_smul _ p t

/-- `Z_N^∨ ⊗_{OPol_N} Z_N ≅ OΛ_N` (`N ≤ 1`) as dg bimodules. -/
def znDualTensorEquivSmall :
    TensorProductOver (OPol N) (RightDual (osymDG N) (Zn N)) (Zn N) ≃ᵈᵍ[osymDG N] osymDG N :=
  (fullActionSmall hN).evEquiv (znRightBasis N)

theorem znDualTensorEquivSmall_op_smul (c : osymDG N)
    (t : TensorProductOver (OPol N) (RightDual (osymDG N) (Zn N)) (Zn N)) :
    znDualTensorEquivSmall hN (op c • t) = op c • znDualTensorEquivSmall hN t :=
  (fullActionSmall hN).evEquiv_op_smul _ c t

end Small

end OddMath.Frontier.EQFunctor
