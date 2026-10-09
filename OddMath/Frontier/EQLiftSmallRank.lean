import OddMath.Frontier.EQLiftOneOne

/-!
# Ranks `a + b ≤ 1`: the bimodules of Corollary 4.21 are rings

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2, §4.4, for
`a + b ≤ 1` (so `ONH_a = OPol_a`, `ONH_b = OPol_b`, `ONH_{a+b} = OPol_{a+b}`).

* `blockRev_small`, `phiAB_small`: `w₀ × w₀` and `φ` are the identity in at most one variable;
* `zabDualEquivSmall`: `Z_{A,B}^∨ ≅ OΛ_{A+B}` by evaluation at `z`, with `OΛ_A ⊗ OΛ_B` acting on the right through
  `psiSmall : OΛ_A ⊗ OΛ_B → OΛ_{A+B}`, `f ⊗ g ↦ f(x) g(y)`;
* `zzDualEquivSmall`: `Z_A^∨ ⊠ Z_B^∨ ≅ OΛ_A ⊗ OΛ_B`, with `OPol_A ⊗ OPol_B` acting on the right through
  `tChi = χ_A ⊗ χ_B`, for any dg rings `E_A`, `E_B` acting on `Z_A`, `Z_B` (`chiE`: `e 1_z = 1_z χ(e)`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQLift

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY osymAB)
open OddMath.Frontier.EQFunctor
open DG MulOpposite TensorProductOver.RightAction

section Small

theorem fin_rev_eq_self_of_le_one {N : ℕ} (hN : N ≤ 1) (i : Fin N) : i.rev = i :=
  Fin.ext (by have := i.isLt; simp [Fin.val_rev]; omega)

variable {A B : ℕ} (hAB : A + B ≤ 1)
include hAB

theorem blockRev_small (f : SkewPolynomial (A + B)) : blockRev A B f = f := by
  have h : blockRev A B = RingHom.id _ := ringHom_ext fun j => by
    rw [blockRev_generator, RingHom.id_apply]
    congr 1
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [blockRevPerm_castAdd, fin_rev_eq_self_of_le_one (by omega) i]
    · rw [blockRevPerm_natAdd, fin_rev_eq_self_of_le_one (by omega) i]
  rw [h]; rfl

theorem phiAB_small (f : SkewPolynomial (A + B)) : EQZab.phiAB A B f = f := by
  have h : EQZab.phiAB A B = RingHom.id _ := ringHom_ext fun j => by
    rw [EQZab.phiAB, RingHom.comp_apply, longestPerm_generator, fin_rev_eq_self_of_le_one hAB j,
      EQZab.epsAB, EQZab.diagHom_generator, RingHom.id_apply]
    have : EQZab.epsCoeff A B j = 1 := by
      unfold EQZab.epsCoeff
      split_ifs with hj
      · have := j.isLt
        rw [show A = 0 by omega, pow_zero]
      · rfl
    rw [this, one_smul]
  rw [h]; rfl

theorem mem_osym_small (f : SkewPolynomial (A + B)) : f ∈ osym (A + B) := osym_mem_of_le_one hAB f

/-! ### `Z_{A,B}^∨ ≅ OΛ_{A+B}` -/

omit hAB in
/-- `z ∈ Z_{A,B}`. -/
abbrev zG (A B : ℕ) : ZabTwG A B := gZabOne A B

/-- The coordinate of `F ∈ Z_{A,B} = OΛ_{A+B} z`. -/
def coordAB (F : ZabTwG A B) : osymDG (A + B) :=
  ⟨OPol.equiv _ (gTwVal F), mem_osymDG.mpr (by rw [RingEquiv.symm_apply_apply]; exact mem_osym_small hAB _)⟩

theorem toSkew_coordAB (F : ZabTwG A B) : EQFix.toSkew (coordAB hAB F) = gTwVal F := by
  change (OPol.equiv _).symm (OPol.equiv _ (gTwVal F)) = _
  rw [RingEquiv.symm_apply_apply]

theorem eq_op_coordAB_smul (F : ZabTwG A B) : F = op (coordAB hAB F) • zG A B := by
  apply EQFix.Zab.ext
  change gTwVal F = 1 * EQZab.phiAB A B (EQFix.toSkew (coordAB hAB F))
  rw [toSkew_coordAB, phiAB_small hAB, sp_one_mul']

/-- The coordinate as an additive map, right `OΛ_{A+B}`-linear. -/
def coordABHom : ZabTwG A B →+ osymDG (A + B) where
  toFun := coordAB hAB
  map_zero' := Subtype.ext (by simp [coordAB, gTwVal])
  map_add' F F' := Subtype.ext (by simp only [coordAB, gTwVal_add, map_add]; rfl)

theorem coordAB_op_smul (h : osymDG (A + B)) (F : ZabTwG A B) :
    coordAB hAB (op h • F) = coordAB hAB F * h := by
  apply Subtype.ext
  change OPol.equiv _ (gTwVal F * EQZab.phiAB A B (EQFix.toSkew h)) = OPol.equiv _ (gTwVal F) * (h : OPol _)
  rw [phiAB_small hAB, map_mul]
  rfl

/-- `OΛ_A ⊗ OΛ_B → OΛ_{A+B}`, `f ⊗ g ↦ f(x) g(y)`, for `A + B ≤ 1`. -/
def psiSmall : LABg A B →ᵈᵍ+* osymDG (A + B) :=
  (toOsym (N := A + B) hAB).comp ((DGSubring.subtype (osymABDG A B)).comp (tensorToOsymAB A B))

theorem coe_psiSmall (r : LABg A B) : ((psiSmall hAB r : osymDG (A + B)) : OPol (A + B)) = tensorToOPol A B r := by
  rw [psiSmall, DGRingHom.comp_apply, DGRingHom.comp_apply, toOsym_val, DGSubring.subtype_apply,
    coe_tensorToOsymAB]

theorem toSkew_psiSmall (r : LABg A B) : EQFix.toSkew (psiSmall hAB r) = gRHat r := by
  rw [EQFix.toSkew, coe_psiSmall]
  rfl

theorem smul_zG (r : LABg A B) : r • zG A B = op (psiSmall hAB r) • zG A B := by
  apply EQFix.Zab.ext
  change blockRev A B (gRHat r) * 1 = 1 * EQZab.phiAB A B (EQFix.toSkew (psiSmall hAB r))
  rw [toSkew_psiSmall, phiAB_small hAB, blockRev_small hAB, sp_mul_one', sp_one_mul']

theorem d_zG : DG.d (zG A B) = 0 := by
  apply EQFix.Zab.ext
  change EQZab.dZ A B 1 = 0
  rw [EQZab.dZ_apply, EQSkewDifferential.d_one, zero_add]
  rcases Nat.eq_zero_or_pos A with hA | hA
  · subst hA
    rw [show EQZab.par 0 = 0 from rfl, zero_smul, EQBorel.sp_mul_zero]
  · obtain rfl : B = 0 := by omega
    rw [show elementary 0 1 = 0 by rw [elementary, EQZab.strictSum_one, Finset.univ_eq_empty,
      Finset.sum_empty], map_zero, smul_zero, EQBorel.sp_mul_zero]

theorem zG_mem : zG A B ∈ DG.grading (0 : ℤ) := EQFix.Zab.mem_grading_iff.mpr one_mem_grading'

theorem coordAB_zG : coordAB hAB (zG A B) = 1 := Subtype.ext (by
  change OPol.equiv _ (1 : SkewPolynomial (A + B)) = 1
  exact map_one _)

theorem coordAB_mem {i : ℤ} {F : ZabTwG A B} (hF : F ∈ DG.grading i) : coordAB hAB F ∈ DG.grading i :=
  (DGSubring.mem_grading_iff _).mpr (OPol.equiv_mem_grading_iff.mpr (gTwVal_mem_grading hF))

/-- **`Z_{A,B}^∨ ≅ OΛ_{A+B}`** for `A + B ≤ 1`, by evaluation at `z`. -/
def zabDualEquivSmall : ZabDualG A B ≃+ osymDG (A + B) where
  toFun f := RightDual.toHom f (zG A B)
  invFun a := (zabRightBasisG A B).ofRightLinear ((AddMonoidHom.mulLeft a).comp (coordABHom hAB))
    fun c m => by
      change a * coordAB hAB (op c • m) = a * coordAB hAB m * c
      rw [coordAB_op_smul, mul_assoc]
  left_inv f := by
    apply RightDual.toHom_injective
    refine AddMonoidHom.ext fun m => ?_
    rw [RightBasis.toHom_ofRightLinear]
    conv_rhs => rw [eq_op_coordAB_smul hAB m, RightDual.map_op_smul]
    rfl
  right_inv a := by
    change a * coordAB hAB (zG A B) = a
    rw [coordAB_zG, mul_one]
  map_add' f g := rfl

theorem zabDualEquivSmall_apply (f : ZabDualG A B) : zabDualEquivSmall hAB f = RightDual.toHom f (zG A B) := rfl

theorem zabDualEquivSmall_mem_iff {n : ℤ} {f : ZabDualG A B} :
    zabDualEquivSmall hAB f ∈ DG.grading n ↔ f ∈ DG.grading n := by
  rw [zabDualEquivSmall_apply]
  constructor
  · intro h i m hm
    rw [eq_op_coordAB_smul hAB m, RightDual.map_op_smul]
    have := DG.mul_mem_grading h (coordAB_mem hAB hm)
    rwa [add_comm n i] at this
  · intro h
    simpa using RightDual.apply_mem_grading h (zG_mem hAB)

theorem zabDualEquivSmall_d (f : ZabDualG A B) :
    zabDualEquivSmall hAB (DG.d f) = DG.d (zabDualEquivSmall hAB f) := by
  rw [zabDualEquivSmall_apply, zabDualEquivSmall_apply, RightDual.toHom_d, dualD_apply, d_zG hAB,
    map_zero, map_zero, map_zero, sub_zero]

theorem zabDualEquivSmall_smul (a : osymDG (A + B)) (f : ZabDualG A B) :
    zabDualEquivSmall hAB (a • f) = a * zabDualEquivSmall hAB f := rfl

theorem zabDualEquivSmall_op_smul (r : LABg A B) (f : ZabDualG A B) :
    zabDualEquivSmall hAB (op r • f) = zabDualEquivSmall hAB f * psiSmall hAB r := by
  rw [zabDualEquivSmall_apply, zabDualEquivSmall_apply, RightDual.toHom_op_smul, smul_zG hAB,
    RightDual.map_op_smul]

end Small

/-! ### The action of `E` on `Z_N`, `N ≤ 1`, is through a morphism `χ : E → OΛ_N` -/

section Chi

variable {N : ℕ} (hN : N ≤ 1) (E : Type) [Ring E] [DGAddCommGroup E] [DGRing E] [Module E (Zn N)]
  [DGBimodule E (osymDG N) (Zn N)]

variable (N) in
/-- `e ↦` the coordinate of `e 1_z` in `Z_N = 1_z OΛ_N`. -/
def chiFun (e : E) : osymDG N := (znRightBasis N).coeff (e • (bz : Zn N)) stair0

include hN in
theorem smul_bz_chiFun (e : E) : e • (bz : Zn N) = op (chiFun N E e) • bz := eq_op_smul_bz hN _

omit [DGRing E] [DGBimodule E (osymDG N) (Zn N)] in
theorem chiFun_add (e e' : E) : chiFun N E (e + e') = chiFun N E e + chiFun N E e' := by
  rw [chiFun, add_smul, RightBasis.coeff_add]; rfl

theorem deg_stair0 : (znRightBasis N).deg stair0 = 0 := by
  simp [znRightBasis, stair0, EQSkewDifferential.totalDeg]

include hN in
/-- **`χ : E → OΛ_N`**, `e 1_z = 1_z χ(e)`, a morphism of dg rings for any dg ring `E` acting on `Z_N`, `N ≤ 1`. -/
def chiE : E →ᵈᵍ+* osymDG N where
  toFun := chiFun N E
  map_one' := by rw [chiFun, one_smul, coeff_bz]
  map_mul' e e' := by
    change (znRightBasis N).coeff ((e * e') • bz) stair0 = chiFun N E e * chiFun N E e'
    rw [mul_smul, smul_bz_chiFun hN E e', DGBimodule.smul_op_smul, RightBasis.coeff_op_smul]
    rfl
  map_zero' := by rw [chiFun, zero_smul, RightBasis.coeff_zero]; rfl
  map_add' e e' := chiFun_add E e e'
  map_mem' {n e} he := by
    have := (znRightBasis N).coeff_mem (DG.smul_mem_grading he bz_mem) stair0
    rwa [deg_stair0, add_zero, sub_zero] at this
  map_d' e := by
    induction e using DG.induction_on with
    | h_zero => rw [d_zero, chiFun, zero_smul, RightBasis.coeff_zero, Pi.zero_apply, d_zero]
    | @h_homogeneous n e =>
      have h1 : DG.d ((e : E) • (bz : Zn N)) = DG.d (e : E) • bz := by
        rw [DG.d_smul e.2, d_bz hN, smul_zero, smul_zero, add_zero]
      have h2 : DG.d (op (chiFun N E (e : E)) • (bz : Zn N)) = op (DG.d (chiFun N E (e : E))) • bz := by
        rw [DG.d_op_smul_of_mem_zero bz_mem, d_bz hN, smul_zero, zero_add]
      change (znRightBasis N).coeff (DG.d (e : E) • bz) stair0 = DG.d (chiFun N E (e : E))
      rw [← h1, smul_bz_chiFun hN E, h2, coeff_op_smul_bz]
    | h_add e e' he he' =>
      change chiFun N E (DG.d (e + e')) = DG.d (chiFun N E (e + e'))
      rw [d_add, chiFun_add, chiFun_add, he, he', d_add]

theorem chiE_apply (e : E) : chiE hN E e = chiFun N E e := rfl

theorem smul_bz_chiE (e : E) : e • (bz : Zn N) = op (chiE hN E e) • bz := smul_bz_chiFun hN E e

theorem znDualEquiv_op_smul_chiE (e : E) (f : RightDual (osymDG N) (Zn N)) :
    znDualEquiv hN (op e • f) = znDualEquiv hN f * chiE hN E e := by
  rw [znDualEquiv_apply, znDualEquiv_apply]
  change RightDual.toHom f (e • bz) = _
  rw [smul_bz_chiE hN E, RightDual.map_op_smul]

end Chi

/-! ### `Z_A^∨ ⊠ Z_B^∨ ≅ OΛ_A ⊗ OΛ_B` -/

section ZZ

variable {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1)

variable (EA EB : Type) [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)]

/-- `χ_A ⊗ χ_B : E_A ⊗ E_B → OΛ_A ⊗ OΛ_B`. -/
def tChi : EAB EA EB →ᵈᵍ+* LABg A B :=
  (GradedTensorProduct.map (OddMath.Frontier.EQK0.intDGAlgHom (chiE hA EA))
    (OddMath.Frontier.EQK0.intDGAlgHom (chiE hB EB))).toDGRingHom

theorem tChi_tmul (p : EA) (q : EB) :
    tChi hA hB EA EB (p ᵍ⊗ₜ[ℤ] q) = (chiE hA EA p) ᵍ⊗ₜ[ℤ] (chiE hB EB q) :=
  GradedTensorProduct.map_tmul _ _ p q

theorem gt_zsmul_tmul (k : ℤ) (x : osymDG A) (y : osymDG B) :
    ((k • x) ᵍ⊗ₜ[ℤ] y : LABg A B) = k • (x ᵍ⊗ₜ[ℤ] y) := by
  unfold GradedTensorProduct.tmul
  rw [← map_zsmul, TensorProduct.smul_tmul']

/-- `f ⊗ g ↦ f(1_z) ⊗ g(1_z)`. -/
def zzDualEquivSmall : ZZDualg A B ≃+ LABg A B :=
  ((TensorProduct.congr (znDualEquiv hA).toIntLinearEquiv (znDualEquiv hB).toIntLinearEquiv).trans
    (GradedTensorProduct.of ℤ (DGAlgebra.gradingSubmodule ℤ (osymDG A))
      (DGAlgebra.gradingSubmodule ℤ (osymDG B)))).toAddEquiv

theorem zzDualEquivSmall_tmul (f : RightDual (osymDG A) (Zn A)) (g : RightDual (osymDG B) (Zn B)) :
    zzDualEquivSmall hA hB (f ⊗ₜ[ℤ] g) = (znDualEquiv hA f) ᵍ⊗ₜ[ℤ] (znDualEquiv hB g) := rfl

theorem zzDualEquivSmall_symm_tmul (x : osymDG A) (y : osymDG B) :
    (zzDualEquivSmall hA hB).symm (x ᵍ⊗ₜ[ℤ] y) = (znDualEquiv hA).symm x ⊗ₜ[ℤ] (znDualEquiv hB).symm y := rfl

theorem zzDualEquivSmall_mem {n : ℤ} {m : ZZDualg A B} (hm : m ∈ DG.grading n) :
    zzDualEquivSmall hA hB m ∈ DG.grading n := by
  have := DG.map_mem_grading_of_tmul (zzDualEquivSmall hA hB).toAddMonoidHom 0 (fun {i j f g} hf hg => by
    rw [add_zero]
    exact GradedTensorProduct.tmul_mem_grading ((znDualEquiv_mem_iff hA).mpr hf)
      ((znDualEquiv_mem_iff hB).mpr hg)) hm
  rwa [add_zero] at this

theorem zzDualEquivSmall_symm_mem {n : ℤ} {x : LABg A B} (hx : x ∈ DG.grading n) :
    (zzDualEquivSmall hA hB).symm x ∈ DG.grading n := by
  refine GradedTensorProduct.grading_induction _ _ hx
    (motive := fun x => (zzDualEquivSmall hA hB).symm x ∈ DG.grading n) ?_ ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · rintro i j a b rfl
    rw [zzDualEquivSmall_symm_tmul]
    refine DG.tmul_mem_grading ((znDualEquiv_mem_iff hA).mp ?_) ((znDualEquiv_mem_iff hB).mp ?_)
    · rw [AddEquiv.apply_symm_apply]; exact a.2
    · rw [AddEquiv.apply_symm_apply]; exact b.2
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy

theorem zzDualEquivSmall_mem_iff {n : ℤ} {m : ZZDualg A B} :
    zzDualEquivSmall hA hB m ∈ DG.grading n ↔ m ∈ DG.grading n :=
  ⟨fun h => by simpa using zzDualEquivSmall_symm_mem hA hB h, zzDualEquivSmall_mem hA hB⟩

theorem zzDualEquivSmall_d (m : ZZDualg A B) :
    zzDualEquivSmall hA hB (DG.d m) = DG.d (zzDualEquivSmall hA hB m) := by
  induction m using DG.tensor_induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | @tmul i j f g =>
    rw [DG.d_tmul, map_add, zzDualEquivSmall_tmul, zzDualEquivSmall_tmul, zzDualEquivSmall_tmul,
      GradedTensorProduct.d_tmul ((znDualEquiv_mem_iff hA).mpr f.2), znDualEquiv_d, znDualEquiv_d,
      gradeInvolution_of_mem f.2, Units.smul_def, map_zsmul, gt_zsmul_tmul, Units.smul_def]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

theorem zzDualEquivSmall_smul (r : LABg A B) (m : ZZDualg A B) :
    zzDualEquivSmall hA hB (r • m) = r * zzDualEquivSmall hA hB m := by
  induction r using GradedTensorProduct.induction_on_tmul with
  | zero => rw [ExternalTensor.zero_smul', map_zero, zero_mul]
  | @tmul i j a ha b hb =>
    induction m using DG.tensor_induction_on with
    | zero => rw [ExternalTensor.smul_zero', map_zero, mul_zero]
    | @tmul k l u v =>
      rw [ExternalTensor.tmul_smul_tmul a hb u.2 (v : RightDual (osymDG B) (Zn B)), Units.smul_def, map_zsmul,
        zzDualEquivSmall_tmul, zzDualEquivSmall_tmul, znDualEquiv_smul, znDualEquiv_smul]
      have hu : (znDualEquiv hA (u : RightDual (osymDG A) (Zn A))) ∈ DG.grading k :=
        (znDualEquiv_mem_iff hA).mpr u.2
      have := GradedTensorProduct.tmul_coe_mul_coe_tmul (DGAlgebra.gradingSubmodule ℤ (osymDG A))
        (DGAlgebra.gradingSubmodule ℤ (osymDG B)) a (⟨b, hb⟩ : DGAlgebra.gradingSubmodule ℤ (osymDG B) j)
        (⟨_, hu⟩ : DGAlgebra.gradingSubmodule ℤ (osymDG A) k) (znDualEquiv hB (v : RightDual (osymDG B) (Zn B)))
      rw [this, Units.smul_def]
      rfl
    | add x y hx hy => rw [ExternalTensor.smul_add', map_add, hx, hy, map_add, mul_add]
  | add r r' hr hr' => rw [ExternalTensor.add_smul', map_add, hr, hr', add_mul]

theorem zzDualEquivSmall_op_smul (q : EAB EA EB) (m : ZZDualg A B) :
    zzDualEquivSmall hA hB (op q • m) = zzDualEquivSmall hA hB m * tChi hA hB EA EB q := by
  induction q using GradedTensorProduct.induction_on_tmul with
  | zero => rw [ExternalTensor.zero_op_smul', map_zero, map_zero, mul_zero]
  | @tmul i j p hp q hq =>
    induction m using DG.tensor_induction_on with
    | zero => rw [smul_zero, map_zero, zero_mul]
    | @tmul k l u v =>
      rw [ExternalTensor.tmul_op_smul_tmul hp q (u : RightDual (osymDG A) (Zn A)) v.2, Units.smul_def, map_zsmul,
        zzDualEquivSmall_tmul, zzDualEquivSmall_tmul, znDualEquiv_op_smul_chiE, znDualEquiv_op_smul_chiE,
        tChi_tmul]
      have hv : (znDualEquiv hB (v : RightDual (osymDG B) (Zn B))) ∈ DG.grading l :=
        (znDualEquiv_mem_iff hB).mpr v.2
      have hp' : chiE hA EA p ∈ DG.grading i := (chiE hA EA).map_mem hp
      have := GradedTensorProduct.tmul_coe_mul_coe_tmul (DGAlgebra.gradingSubmodule ℤ (osymDG A))
        (DGAlgebra.gradingSubmodule ℤ (osymDG B)) (znDualEquiv hA (u : RightDual (osymDG A) (Zn A)))
        (⟨_, hv⟩ : DGAlgebra.gradingSubmodule ℤ (osymDG B) l) (⟨_, hp'⟩ : DGAlgebra.gradingSubmodule ℤ (osymDG A) i)
        (chiE hB EB q)
      rw [this, Units.smul_def, mul_comm l i]
      rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, add_mul]
  | add q q' hq hq' => rw [ExternalTensor.add_op_smul', map_add, hq, hq', map_add, mul_add]

end ZZ

/-! ### `ι` in ranks `a + b ≤ 1`: `χ_{a+b} ∘ ι = ψ ∘ (χ_a ⊗ χ_b)` -/

section Iota

variable {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) (hAB : A + B ≤ 1)
  {EA EB EN : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] [Ring EN] [DGAddCommGroup EN] [DGRing EN] [Module EN (Zn (A + B))]
  [DGBimodule EN (osymDG (A + B)) (Zn (A + B))] (HN : FullAction EN (osymDG (A + B)) (Zn (A + B)))

variable (A B) in
/-- `1_z ⊠ 1_z ⊗ z ∈ (Z_A ⊠ Z_B) ⊗ Z_{A,B}`. -/
abbrev tzOne : TZ A B :=
  TensorProductOver.tmul (LABg A B) ((bz : Zn A) ⊗ₜ[ℤ] (bz : Zn B)) (zG A B)

theorem gIndHom_tzOne : gIndHom (tzOne A B) = (bz : Zn (A + B)) := by
  change zE (A + B) (inclX A B ((zE A).symm (zE A 1)) * inclY A B ((zE B).symm (zE B 1)) *
    EQZab.tauAB A B (gTwVal (gZabOne A B))) = zE (A + B) 1
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, map_one, map_one, gTwVal_one, map_one,
    sp_mul_one', sp_mul_one']

include hA hB hAB in
theorem smul_tzOne (s : EAB EA EB) :
    s • tzOne A B = op (psiSmall hAB (tChi hA hB EA EB s)) • tzOne A B := by
  induction s using GradedTensorProduct.induction_on_tmul with
  | zero => rw [tz_zero_smul, map_zero, map_zero, op_zero, zero_smul]
  | @tmul i j a ha b hb =>
    change TensorProductOver.tmul (LABg A B) ((a ᵍ⊗ₜ[ℤ] b : EAB EA EB) • ((bz : Zn A) ⊗ₜ[ℤ] (bz : Zn B))) (zG A B) =
      TensorProductOver.tmul (LABg A B) ((bz : Zn A) ⊗ₜ[ℤ] (bz : Zn B))
        (op (psiSmall hAB (tChi hA hB EA EB (a ᵍ⊗ₜ[ℤ] b))) • zG A B)
    rw [← smul_zG hAB, ← TensorProductOver.op_smul_tmul, ExternalTensor.tmul_smul_tmul a hb bz_mem,
      tChi_tmul, ExternalTensor.tmul_op_smul_tmul ((chiE hA EA).map_mem ha) _ _ bz_mem, mul_zero, mul_zero,
      smul_bz_chiE hA EA, smul_bz_chiE hB EB]
  | add s s' hs hs' => rw [tz_add_smul, hs, hs', map_add, map_add, MulOpposite.op_add, add_smul]

include hA hB hAB in
/-- `ι(s) 1_z = 1_z ψ((χ_a ⊗ χ_b)(s))`. -/
theorem gIota_smul_bz (s : EAB EA EB) :
    gIota EA EB HN s • (bz : Zn (A + B)) = op (psiSmall hAB (tChi hA hB EA EB s)) • bz := by
  rw [gIota_smul, conjMap_apply, ← gIndHom_tzOne, gIndInv_indHom, smul_tzOne hA hB hAB, gIndHom_op_smul]

include hA hB in
/-- **`χ_{a+b} ∘ ι = ψ ∘ (χ_a ⊗ χ_b)`** for `a + b ≤ 1`. -/
theorem chiE_comp_gIota :
    (chiE hAB EN).comp (gIota EA EB HN) = (psiSmall hAB).comp (tChi hA hB EA EB) :=
  DGRingHom.ext fun s => by
    rw [DGRingHom.comp_apply, DGRingHom.comp_apply, chiE_apply, chiFun, gIota_smul_bz hA hB hAB,
      coeff_op_smul_bz]

end Iota

/-! ### Bijectivity in ranks `a + b ≤ 1` -/

section Inv

variable {R S : Type*} [Ring R] [DGAddCommGroup R] [Ring S] [DGAddCommGroup S] (f : R →ᵈᵍ+* S)
  (hf : Function.Bijective f)

/-- The inverse of a bijective morphism of dg rings. -/
def dgRingHomInv : S →ᵈᵍ+* R where
  toFun := Function.surjInv hf.2
  map_one' := hf.1 (by rw [Function.surjInv_eq hf.2, map_one])
  map_mul' x y := hf.1 (by rw [Function.surjInv_eq hf.2, map_mul, Function.surjInv_eq hf.2, Function.surjInv_eq hf.2])
  map_zero' := hf.1 (by rw [Function.surjInv_eq hf.2, map_zero])
  map_add' x y := hf.1 (by rw [Function.surjInv_eq hf.2, map_add, Function.surjInv_eq hf.2, Function.surjInv_eq hf.2])
  map_mem' {n x} hx := DG.mem_grading_of_injective f.toRingHom.toAddMonoidHom (fun h => f.map_mem h) hf.1
    (by change f (Function.surjInv hf.2 x) ∈ _; rwa [Function.surjInv_eq hf.2])
  map_d' x := hf.1 (by rw [Function.surjInv_eq hf.2, f.map_d, Function.surjInv_eq hf.2])

theorem apply_dgRingHomInv (x : S) : f (dgRingHomInv f hf x) = x := Function.surjInv_eq hf.2 x

theorem dgRingHomInv_apply (a : R) : dgRingHomInv f hf (f a) = a := hf.1 (apply_dgRingHomInv f hf _)

end Inv

section ChiBij

variable {N : ℕ} (hN : N ≤ 1) {E : Type} [Ring E] [DGAddCommGroup E] [DGRing E] [Module E (Zn N)]
  [DGBimodule E (osymDG N) (Zn N)] (H : FullAction E (osymDG N) (Zn N))

include H in
/-- `χ : E → OΛ_N` is bijective when `E` acts fully and faithfully on `Z_N`. -/
theorem chiE_bijective : Function.Bijective (chiE hN E) := by
  refine ⟨fun e e' h => H.ext fun z => ?_, fun c => ?_⟩
  · rw [eq_op_smul_bz hN z, DGBimodule.smul_op_smul, DGBimodule.smul_op_smul, smul_bz_chiE hN E, smul_bz_chiE hN E, h]
  · let φ : Zn N →+ Zn N := AddMonoidHom.mk' (fun z => op (c * (znRightBasis N).coeff z stair0) • (bz : Zn N))
      fun z z' => by rw [RightBasis.coeff_add, Pi.add_apply, mul_add, MulOpposite.op_add, add_smul]
    obtain ⟨e, he⟩ := H.full φ fun h z => by
      change op (c * (znRightBasis N).coeff (op h • z) stair0) • (bz : Zn N) =
        op h • op (c * (znRightBasis N).coeff z stair0) • (bz : Zn N)
      rw [RightBasis.coeff_op_smul, smul_smul, ← op_mul, mul_assoc]
    refine ⟨e, ?_⟩
    rw [chiE_apply, chiFun, he]
    change (znRightBasis N).coeff (op (c * (znRightBasis N).coeff (bz : Zn N) stair0) • (bz : Zn N)) stair0 = c
    rw [coeff_bz, mul_one, coeff_op_smul_bz]

end ChiBij

section TChiBij

variable {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) {EA EB : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA]
  [Module EA (Zn A)] [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB]
  [Module EB (Zn B)] [DGBimodule EB (osymDG B) (Zn B)]
  (HA : FullAction EA (osymDG A) (Zn A)) (HB : FullAction EB (osymDG B) (Zn B))

include HA HB in
/-- `χ_A ⊗ χ_B` is bijective. -/
theorem tChi_bijective : Function.Bijective (tChi hA hB EA EB) := by
  let iA := dgRingHomInv _ (chiE_bijective hA HA)
  let iB := dgRingHomInv _ (chiE_bijective hB HB)
  let t' : LABg A B →ᵈᵍ+* EAB EA EB :=
    (GradedTensorProduct.map (OddMath.Frontier.EQK0.intDGAlgHom iA)
      (OddMath.Frontier.EQK0.intDGAlgHom iB)).toDGRingHom
  have ht' : ∀ (x : osymDG A) (y : osymDG B), t' (x ᵍ⊗ₜ[ℤ] y) = iA x ᵍ⊗ₜ[ℤ] iB y := fun x y =>
    GradedTensorProduct.map_tmul _ _ x y
  refine Function.bijective_iff_has_inverse.mpr ⟨t', fun s => ?_, fun r => ?_⟩
  · induction s using GradedTensorProduct.induction_on_tmul with
    | zero => rw [map_zero, map_zero]
    | @tmul i j a ha b hb =>
      rw [tChi_tmul, ht', dgRingHomInv_apply, dgRingHomInv_apply]
    | add s s' hs hs' => rw [map_add, map_add, hs, hs']
  · induction r using GradedTensorProduct.induction_on_tmul with
    | zero => rw [map_zero, map_zero]
    | @tmul i j a ha b hb =>
      rw [ht', tChi_tmul, apply_dgRingHomInv, apply_dgRingHomInv]
    | add r r' hr hr' => rw [map_add, map_add, hr, hr']

end TChiBij

section Swap

variable {A B : ℕ} (hAB : A + B ≤ 1)
include hAB

theorem swapPoly_small (f : SkewPolynomial (A + B)) : swapPoly A B f = f := by
  have h : swapPoly A B = RingHom.id _ := ringHom_ext fun j => by
    rw [swapPoly_generator, RingHom.id_apply]
    congr 1
    exact Fin.ext (by have := j.isLt; unfold swapFin; split_ifs <;> simp <;> omega)
  rw [h]; rfl

theorem swapOsym_psiSmall (r : LABg A B) : swapOsym A B (psiSmall hAB r) = tensorToOsymAB A B r := by
  apply Subtype.ext
  change OPol.equiv _ (swapPoly A B ((OPol.equiv _).symm (psiSmall hAB r : OPol (A + B)))) = _
  rw [swapPoly_small hAB, RingEquiv.apply_symm_apply, coe_psiSmall, coe_tensorToOsymAB]

/-- `swap ∘ ψ = id` on `OΛ_A ⊗ OΛ_B`. -/
theorem swapDGG_psiSmall (r : LABg A B) : swapDGG A B (psiSmall hAB r) = r := by
  change (tensorEquivOsymAB A B).symm (swapOsym A B (psiSmall hAB r)) = r
  rw [swapOsym_psiSmall hAB]
  exact (tensorEquivOsymAB A B).symm_apply_apply r

/-- `ψ ∘ swap = id` on `OΛ_{A+B}`. -/
theorem psiSmall_swapDGG (h : osymDG (A + B)) : psiSmall hAB (swapDGG A B h) = h := by
  apply Subtype.ext
  rw [coe_psiSmall, ← coe_tensorToOsymAB]
  change ((tensorEquivOsymAB A B ((tensorEquivOsymAB A B).symm (swapOsym A B h)) : osymABDG A B) : OPol (A + B)) = _
  rw [(tensorEquivOsymAB A B).apply_symm_apply]
  change OPol.equiv _ (swapPoly A B ((OPol.equiv _).symm (h : OPol (A + B)))) = _
  rw [swapPoly_small hAB, RingEquiv.apply_symm_apply]

theorem psiSmall_bijective : Function.Bijective (psiSmall hAB) :=
  Function.bijective_iff_has_inverse.mpr ⟨swapDGG A B, swapDGG_psiSmall hAB, psiSmall_swapDGG hAB⟩

end Swap

section IotaBij

variable {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) (hAB : A + B ≤ 1)
  {EA EB EN : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] [Ring EN] [DGAddCommGroup EN] [DGRing EN] [Module EN (Zn (A + B))]
  [DGBimodule EN (osymDG (A + B)) (Zn (A + B))]
  (HA : FullAction EA (osymDG A) (Zn A)) (HB : FullAction EB (osymDG B) (Zn B))
  (HN : FullAction EN (osymDG (A + B)) (Zn (A + B)))

include hA hB hAB HA HB in
/-- **`ι` is bijective for `a + b ≤ 1`.** -/
theorem gIota_bijective : Function.Bijective (gIota EA EB HN) := by
  have h : ⇑(chiE hAB EN) ∘ ⇑(gIota EA EB HN) = ⇑(psiSmall hAB) ∘ ⇑(tChi hA hB EA EB) :=
    congrArg DFunLike.coe (chiE_comp_gIota hA hB hAB HN)
  refine (Function.Bijective.of_comp_iff' (chiE_bijective hAB HN) _).mp ?_
  rw [h]
  exact (psiSmall_bijective hAB).comp (tChi_bijective hA hB HA HB)

include hA hB hAB HA HB in
/-- `ι⁻¹ : E_{A+B} → E_A ⊗ E_B`. -/
def gIotaInv : EN →ᵈᵍ+* EAB EA EB := dgRingHomInv _ (gIota_bijective hA hB hAB HA HB HN)

/-- `swap ∘ χ_{A+B} = (χ_A ⊗ χ_B) ∘ ι⁻¹`. -/
theorem swapDGG_comp_chiE :
    (swapDGG A B).comp (chiE hAB EN) = (tChi hA hB EA EB).comp (gIotaInv hA hB hAB HA HB HN) :=
  DGRingHom.ext fun e => by
    obtain ⟨s, rfl⟩ := (gIota_bijective hA hB hAB HA HB HN).2 e
    rw [DGRingHom.comp_apply, DGRingHom.comp_apply, gIotaInv, dgRingHomInv_apply]
    have := congrArg (fun φ => swapDGG A B (φ s)) (chiE_comp_gIota hA hB hAB HN)
    simp only [DGRingHom.comp_apply] at this
    rw [this, swapDGG_psiSmall]

end IotaBij

/-! ### `ONH^♮` in ranks `a + b ≤ 1`: `ι` regarded as a bimodule -/

section NatSmall

variable {A B : ℕ} (hA : A ≤ 1) (hB : B ≤ 1) (hAB : A + B ≤ 1)
  {EA EB EN : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] [Ring EN] [DGAddCommGroup EN] [DGRing EN] [Module EN (Zn (A + B))]
  [DGBimodule EN (osymDG (A + B)) (Zn (A + B))]
  (HA : FullAction EA (osymDG A) (Zn A)) (HB : FullAction EB (osymDG B) (Zn B))
  (HN : FullAction EN (osymDG (A + B)) (Zn (A + B)))

include hAB in
theorem PAG_small : PAG A B = 1 := by
  rcases Nat.eq_zero_or_pos A with h | h
  · subst h; exact pow_zero _
  · obtain rfl : B = 0 := by omega
    change inclY A 0 (elementary 0 0) ^ A = 1
    rw [elementary, FiniteCompleteElementary.FiniteWords.strictSum_zero, map_one, one_pow]

include hAB in
/-- `P^A = 1` for `a + b ≤ 1`. -/
theorem PwG_small : PwG A B HN = 1 :=
  HN.ext fun z => by rw [PwG_smul HN, PAG_small hAB, sp_one_mul', AddEquiv.apply_symm_apply, one_smul]

include hAB in
theorem degPG_small : degPG A B = 0 := by
  rcases (show A = 0 ∨ B = 0 by omega) with h | h <;> simp [degPG, h]

include hAB in
theorem twist_degPG_small (g : EN) : Shift.twist EN (degPG A B) g = g := by
  rw [degPG_small hAB, Shift.twist_zero]

include hAB in
theorem mem_natSubG_small (x : IONHG A B EA EB HN) : x ∈ natSubG A B EA EB HN :=
  ⟨x, by rw [PwG_small hAB HN, one_mul]⟩

theorem gIota_gIotaInv (e : EN) : gIota EA EB HN (gIotaInv hA hB hAB HA HB HN e) = e :=
  apply_dgRingHomInv _ _ e

theorem gIotaInv_gIota (s : EAB EA EB) : gIotaInv hA hB hAB HA HB HN (gIota EA EB HN s) = s :=
  dgRingHomInv_apply _ _ s

/-- `ONH^♮ ≅ E_A ⊗ E_B`, `x ↦ ι⁻¹(x)`, for `a + b ≤ 1` (`P^A = 1`, `ι` bijective). -/
def natEquivSmall : ONHNatG A B EA EB HN ≃+ EAB EA EB where
  toFun x := gIotaInv hA hB hAB HA HB HN
    (show EN from ((show natSubG A B EA EB HN from x) : IONHG A B EA EB HN))
  invFun s := Regrade.mk (degPG A B) ⟨show IONHG A B EA EB HN from gIota EA EB HN s, mem_natSubG_small hAB HN _⟩
  left_inv _ := Subtype.ext (gIota_gIotaInv hA hB hAB HA HB HN _)
  right_inv s := gIotaInv_gIota hA hB hAB HA HB HN s
  map_add' _ _ := map_add (gIotaInv hA hB hAB HA HB HN) _ _

theorem natEquivSmall_apply (x : ONHNatG A B EA EB HN) :
    natEquivSmall hA hB hAB HA HB HN x = gIotaInv hA hB hAB HA HB HN
      (show EN from ((show natSubG A B EA EB HN from x) : IONHG A B EA EB HN)) := rfl

theorem natEquivSmall_mem_iff {n : ℤ} {x : ONHNatG A B EA EB HN} :
    natEquivSmall hA hB hAB HA HB HN x ∈ DG.grading n ↔ x ∈ DG.grading n := by
  rw [show x ∈ DG.grading n ↔ ((show natSubG A B EA EB HN from x) : IONHG A B EA EB HN) ∈
      DG.grading (n + degPG A B) from DGSubmodule.mem_grading_iff _, degPG_small hAB, add_zero,
    natEquivSmall_apply]
  constructor
  · intro h
    have := (gIota EA EB HN).map_mem h
    rwa [gIota_gIotaInv] at this
  · intro h
    exact (gIotaInv hA hB hAB HA HB HN).map_mem h

theorem natEquivSmall_d (x : ONHNatG A B EA EB HN) :
    natEquivSmall hA hB hAB HA HB HN (DG.d x) = DG.d (natEquivSmall hA hB hAB HA HB HN x) :=
  (gIotaInv hA hB hAB HA HB HN).map_d _

theorem natEquivSmall_smul (s : EAB EA EB) (x : ONHNatG A B EA EB HN) :
    natEquivSmall hA hB hAB HA HB HN (s • x) = s * natEquivSmall hA hB hAB HA HB HN x := by
  change gIotaInv hA hB hAB HA HB HN (gIota EA EB HN s * _) = _
  rw [map_mul, gIotaInv_gIota]
  rfl

theorem natEquivSmall_op_smul (g : EN) (x : ONHNatG A B EA EB HN) :
    natEquivSmall hA hB hAB HA HB HN (op g • x) =
      natEquivSmall hA hB hAB HA HB HN x * gIotaInv hA hB hAB HA HB HN g := by
  change gIotaInv hA hB hAB HA HB HN (_ * Shift.twist EN (degPG A B) g) = _
  rw [twist_degPG_small hAB, map_mul]
  rfl

/-- `ONH^♮ ≅ E_A ⊗ E_B` as dg left `E_A ⊗ E_B`-modules. -/
def natDGEquivSmall : ONHNatG A B EA EB HN ≃ᵈᵍ[EAB EA EB] EAB EA EB where
  toFun := natEquivSmall hA hB hAB HA HB HN
  invFun := (natEquivSmall hA hB hAB HA HB HN).symm
  left_inv := (natEquivSmall hA hB hAB HA HB HN).left_inv
  right_inv := (natEquivSmall hA hB hAB HA HB HN).right_inv
  map_add' := map_add _
  map_smul' s x := natEquivSmall_smul hA hB hAB HA HB HN s x
  map_mem' h := (natEquivSmall_mem_iff hA hB hAB HA HB HN).mpr h
  map_d' := natEquivSmall_d hA hB hAB HA HB HN

include hA hB hAB HA HB in
/-- **`ONH^♮` is K-projective for `a + b ≤ 1`** (it is free of rank one). -/
theorem onhNatG_isKProjective_small : IsKProjective.{0} (EAB EA EB) (ONHNatG A B EA EB HN) :=
  (isKProjective_self (EAB EA EB)).of_dgModuleEquiv (natDGEquivSmall hA hB hAB HA HB HN)

end NatSmall

end OddMath.Frontier.EQLift
