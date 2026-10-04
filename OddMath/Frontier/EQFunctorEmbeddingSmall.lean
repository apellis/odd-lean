import OddMath.Frontier.EQFunctorEmbedding
import DG.Category.Derived.TensorIso
import OddMath.Frontier.EQBorelPresentation

/-!
# Ellis–Qi, Corollary 4.19 in ranks `N ≤ 1`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.18 and Corollary 4.19 ("one only has to prove the result for the components
`J_0` and `J_1`, in which cases the result is clear").

* generic (`catBimoduleIsoOfFunctor`, `bimoduleDerivedTensorIsoInduction`): if a dg
  `(A, B)`-bimodule `M` is isomorphic to `A` with right action through a morphism of dg rings
  `φ : B → A`, then `M ⊗^L_B - ≅ φ^*` (derived induction), via dg-lean's
  `DG.CatModule.DerivedCategory.derivedTensorIso`;
* for `N ≤ 1`: `ONH_N = OPol_N`, `OΛ_N = OPol_N` (`osym_mem_of_le_one`, `toOsym`, an isomorphism of
  dg rings), and `Z_N^∨ ≅ OΛ_N` by evaluation at `1_z` (`znDualEquiv`);
* **Corollary 4.19 for `N ≤ 1`** (`jSmall_isEquivalence`, `jSmallFullyFaithful`):
  `J_N = Z_N^∨ ⊗^L_{OPol_N} - : D(OPol_N) → D(OΛ_N)` is an equivalence, in particular fully
  faithful. Together with `jFullyFaithful` (`N ≥ 2`), `J_N` is fully faithful for every `N`.
-/

open CategoryTheory

universe v w₂ w₃ w₄

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential (OPol OPolAlpha Zn osym osymDG mem_osymDG twistRev
  oddStrands)
open DG MulOpposite

noncomputable section

/-! ## Bimodules isomorphic to a ring through a ring morphism -/

section Generic

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (φ : B →ᵈᵍ+* A) {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [DGBimodule A B M]

/-- An isomorphism of `M` with `A` (left action by multiplication, right action through `φ`)
as an isomorphism of dg bimodules over the one-object dg categories. -/
def catBimoduleIsoOfFunctor (e : M ≃+ A)
    (he : ∀ {n : ℤ} {m : M}, e m ∈ grading n ↔ m ∈ grading n)
    (hd : ∀ m : M, e (d m) = d (e m)) (hl : ∀ (a : A) (m : M), e (a • m) = a * e m)
    (hr : ∀ (b : B) (m : M), e (op b • m) = e m * φ b) :
    CatBimodule.Iso (catBimodule A B M) (CatBimodule.ofFunctor φ.singleObjFunctor) where
  left _ := CatModule.isoMk (fun _ => e) he hd (fun f m => hl f m)
  ract g _ x := hr g x

variable [CatModule.HasDerivedCategory.{v, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- **`M ⊗^L_B - ≅ φ^*`** for `M ≅ A` as above. -/
def bimoduleDerivedTensorIsoInduction (hM : DG.IsKProjective.{v} A M) (e : M ≃+ A)
    (he : ∀ {n : ℤ} {m : M}, e m ∈ grading n ↔ m ∈ grading n)
    (hd : ∀ m : M, e (d m) = d (e m)) (hl : ∀ (a : A) (m : M), e (a • m) = a * e m)
    (hr : ∀ (b : B) (m : M), e (op b • m) = e m * φ b) :
    bimoduleDerivedTensor.{v, w₂, w₃, w₄} A B M hM ≅ φ.derivedInduction.{v, w₂, w₃, w₄} :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (CatModule.DerivedCategory.derivedTensorIso (catBimoduleIsoOfFunctor φ e he hd hl hr) _ _) _) ≪≫
    (φ.derivedInductionIsoDerivedTensor).symm

end Generic

/-! ## Ranks `N ≤ 1` -/

section Small

variable {N : ℕ} (hN : N ≤ 1)

include hN in
theorem osym_mem_of_le_one (f : SkewPolynomial N) : f ∈ osym N := by
  induction f using EQBorel.skew_induction with
  | hgen j =>
    obtain rfl : N = 1 := by have := j.isLt; omega
    obtain rfl : j = 0 := Subsingleton.elim _ _
    have h := EQZab.elementary_mem 1 1
    rwa [EQSkewDifferential.elementary, EQZab.strictSum_one, Fin.sum_univ_one] at h
  | hint z => exact intCast_mem _ z
  | hadd f g hf hg => exact add_mem hf hg
  | hmul f g hf hg => exact mul_mem hf hg

/-- `OPol_N → OΛ_N`, an isomorphism of dg rings for `N ≤ 1`. -/
def toOsym : OPol N →ᵈᵍ+* osymDG N where
  toFun f := ⟨f, mem_osymDG.mpr (osym_mem_of_le_one hN _)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mem' h := h
  map_d' _ := rfl

theorem toOsym_isQuasiIso : (toOsym hN).IsQuasiIso :=
  DGRingHom.isQuasiIso_of_leftInverse_rightInverse (toOsym hN) (DGSubring.subtype (osymDG N))
    (fun _ => rfl) (fun _ => rfl)

include hN in
theorem twistRev_eq (f : SkewPolynomial N) : twistRev N f = f := by
  have h : twistRev N = RingHom.id _ := EQSkewDifferential.ringHom_ext fun j => by
    obtain rfl : N = 1 := by have := j.isLt; omega
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  rw [h]; rfl

/-- The unique reversed staircase exponent in rank `N ≤ 1`. -/
def stair0 : EQZn.RevStair N := ⟨0, fun _ => Nat.zero_le _⟩

include hN in
theorem eq_stair0 (A : EQZn.RevStair N) : A = stair0 := by
  apply Subtype.ext; funext i
  have := A.2 i
  have : i.val = 0 := by have := i.isLt; omega
  simp only [stair0, Pi.zero_apply]; omega

/-- The generator `1_z` of `Z_N`. -/
abbrev bz : Zn N := (znRightBasis N).b stair0

include hN in
theorem eq_op_smul_bz (m : Zn N) : m = op ((znRightBasis N).coeff m stair0) • bz := by
  conv_lhs => rw [← (znRightBasis N).sum_coeff m]
  rw [Finset.sum_eq_single stair0 (fun A _ h => absurd (eq_stair0 hN A) h)
    (fun h => absurd (Finset.mem_univ _) h)]

theorem coeff_bz : (znRightBasis N).coeff bz stair0 = 1 := by
  classical
  rw [(znRightBasis N).coeff_basis, Pi.single_eq_same]

include hN in
theorem d_bz : DG.d (bz : Zn N) = 0 := by
  change DG.d ((EQFix.zE N) (monomial (0 : Fin N → ℕ) 1)) = 0
  rw [EQSkewDifferential.OPolAlpha.d_equiv, EQSkewDifferential.dAlpha_apply]
  have hs : EQSkewDifferential.sAlpha (EQSkewDifferential.indicator (oddStrands N)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : i.val = 0 := by have := i.isLt; omega
    simp [EQSkewDifferential.indicator, oddStrands, this]
  rw [hs, EQBorel.sp_mul_zero, add_zero]
  change (EQFix.zE N) (EQSkewDifferential.d N 1) = 0
  rw [EQSkewDifferential.d_one, map_zero]

/-- **`Z_N^∨ ≅ OΛ_N`** for `N ≤ 1`, by evaluation at `1_z`. -/
def znDualEquiv : RightDual (osymDG N) (Zn N) ≃+ osymDG N where
  toFun f := RightDual.toHom f bz
  invFun a := (znRightBasis N).ofRightLinear
    ((AddMonoidHom.mulLeft a).comp ((znRightBasis N).coeffHom stair0)) fun c m => by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, RightBasis.coeffHom_apply,
        RightBasis.coeff_op_smul, mul_assoc]
  left_inv f := by
    apply RightDual.toHom_injective
    ext m
    rw [RightBasis.toHom_ofRightLinear]
    conv_rhs => rw [eq_op_smul_bz hN m, RightDual.map_op_smul]
    rfl
  right_inv a := by
    show a * (znRightBasis N).coeff bz stair0 = a
    rw [coeff_bz, mul_one]
  map_add' f g := rfl

theorem znDualEquiv_apply (f : RightDual (osymDG N) (Zn N)) :
    znDualEquiv hN f = RightDual.toHom f bz := rfl

theorem bz_mem : (bz : Zn N) ∈ grading 0 := by
  have h := (znRightBasis N).b_mem stair0
  have e : (znRightBasis N).deg stair0 = 0 := by
    simp [znRightBasis, stair0, EQSkewDifferential.totalDeg]
  rwa [e] at h

theorem znDualEquiv_mem_iff {n : ℤ} {f : RightDual (osymDG N) (Zn N)} :
    znDualEquiv hN f ∈ grading n ↔ f ∈ grading n := by
  rw [znDualEquiv_apply]
  constructor
  · intro h i m hm
    rw [eq_op_smul_bz hN m, RightDual.map_op_smul, add_comm]
    refine DG.mul_mem_grading h ?_
    have := (znRightBasis N).coeff_mem hm stair0
    simpa [znRightBasis, stair0, EQSkewDifferential.totalDeg] using this
  · intro h
    simpa using RightDual.apply_mem_grading h bz_mem

theorem znDualEquiv_d (f : RightDual (osymDG N) (Zn N)) :
    znDualEquiv hN (DG.d f) = DG.d (znDualEquiv hN f) := by
  rw [znDualEquiv_apply, znDualEquiv_apply, RightDual.toHom_d, dualD_apply, d_bz hN,
    map_zero, map_zero, map_zero, sub_zero]

theorem znDualEquiv_smul (a : osymDG N) (f : RightDual (osymDG N) (Zn N)) :
    znDualEquiv hN (a • f) = a * znDualEquiv hN f := rfl

theorem smul_bz (p : OPol N) : p • (bz : Zn N) = op (toOsym hN p) • bz := by
  have h := EQSkewDifferential.Zn.op_smul_one (n := N) p
  rw [twistRev_eq hN, RingEquiv.apply_symm_apply] at h
  exact h.symm

theorem znDualEquiv_op_smul (p : OPol N) (f : RightDual (osymDG N) (Zn N)) :
    znDualEquiv hN (op p • f) = znDualEquiv hN f * toOsym hN p := by
  rw [znDualEquiv_apply, znDualEquiv_apply]
  change RightDual.toHom f (p • bz) = _
  rw [smul_bz hN, RightDual.map_op_smul]

end Small

/-- **Ellis–Qi, Definition 4.18** in rank `N ≤ 1` (`ONH_N = OPol_N`):
`J_N = Z_N^∨ ⊗^L_{OPol_N} - : D(OPol_N) → D(OΛ_N)`. -/
abbrev JSmall (N : ℕ) [CatModule.HasDerivedCategory.{0, 0} (SingleObj (OPol N))]
    [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymDG N))]
    [DG.HasDerivedCategory.{w₃, 0} (OPol N)] [DG.HasDerivedCategory.{w₄, 0} (osymDG N)] :
    DG.DerivedCategory (OPol N) ⥤ DG.DerivedCategory (osymDG N) :=
  bimoduleDerivedTensor.{0, w₂, w₃, w₄} (osymDG N) (OPol N) (RightDual (osymDG N) (Zn N))
    (znDual_isKProjective N)

section Small2

variable {N : ℕ} (hN : N ≤ 1) [CatModule.HasDerivedCategory.{0, 0} (SingleObj (OPol N))]
  [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymDG N))]
  [DG.HasDerivedCategory.{w₃, 0} (OPol N)] [DG.HasDerivedCategory.{w₄, 0} (osymDG N)]

/-- `J_N ≅ φ^*` for the isomorphism of dg rings `φ : OPol_N → OΛ_N`, `N ≤ 1`. -/
def jSmallIsoInduction : JSmall.{w₂, w₃, w₄} N ≅ (toOsym hN).derivedInduction.{0, w₂, w₃, w₄} :=
  bimoduleDerivedTensorIsoInduction (toOsym hN) (znDual_isKProjective N) (znDualEquiv hN)
    (znDualEquiv_mem_iff hN) (znDualEquiv_d hN) (znDualEquiv_smul hN) (znDualEquiv_op_smul hN)

include hN in
/-- **Ellis–Qi, Corollary 4.19** for `N ≤ 1`: `J_N` is an equivalence. -/
theorem jSmall_isEquivalence : (JSmall.{w₂, w₃, w₄} N).IsEquivalence := by
  have : ((toOsym hN).derivedInduction.{0, w₂, w₃, w₄}).IsEquivalence :=
    DGRingHom.derivedInduction_isEquivalence _ (toOsym_isQuasiIso hN)
  exact Functor.isEquivalence_of_iso (jSmallIsoInduction hN).symm

include hN in
/-- **Ellis–Qi, Corollary 4.19** for `N ≤ 1`: `J_N` is fully faithful. -/
def jSmallFullyFaithful : (JSmall.{w₂, w₃, w₄} N).FullyFaithful := by
  haveI := jSmall_isEquivalence.{w₂, w₃, w₄} hN
  exact Functor.FullyFaithful.ofFullyFaithful _

end Small2

end

end OddMath.Frontier.EQFunctor
