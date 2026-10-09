import OddMath.Frontier.EQLiftRestrictionPoly

/-!
# The restriction half of Corollary 4.21 in all ranks: the bimodule isomorphism

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.15 (`Z^♮_{A,B}`), (4.32) (`ONH^♮_{A+B}`) and the proof of Corollary 4.21, for all
ranks `A`, `B` and dg rings `E_A`, `E_B`, `E_{A+B}` acting fully on `Z_A`, `Z_B`, `Z_{A+B}`, with
`ι = gIota` (`EQLiftInduction`).

* `PwG`: the element of `E_{A+B}` acting as left multiplication by `P^A`, `P = y_1 ⋯ y_B`;
* `natSubG`: the right ideal `P^A E_{A+B}` as a dg left `E_A ⊗ E_B`-submodule of `ι^* E_{A+B}` (stable
  under `ι(E_A ⊗ E_B)`, by the bimodule map below), and `ONHNatG`: it regraded so that `P^A` has degree `0`;
* `ZNatG`: `Z^♮_{A,B}` with `OΛ_{A+B}` acting through the block swap `h ↦ h(y, x)` (`swapDGG`);
* **`gEquivG : ((Z_A ⊠ Z_B) ⊗ Z^♮_{A,B}) ⊗_{OΛ_{A+B}} Z_{A+B}^∨ ≅ ONH^♮_{A+B}`** as dg
  `(E_A ⊗ E_B, E_{A+B})`-bimodules (`gEquiv_op_smulG HN`).

This is `EQFunctor.gEquiv` (ranks `a + 2`, `b + 2`) with the `ONH`-specific inputs replaced by the full action.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQLift

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY osymAB par)
open OddMath.Frontier.EQFunctor
open DG MulOpposite TensorProductOver.RightAction

variable {A B : ℕ} {EA EB EN : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] [Ring EN] [DGAddCommGroup EN] [DGRing EN] [Module EN (Zn (A + B))]
  [DGBimodule EN (osymDG (A + B)) (Zn (A + B))]
  (HN : FullAction EN (osymDG (A + B)) (Zn (A + B)))

variable (A B) in
/-- `AB` (the degree of `P^A`). -/
abbrev degPG : ℤ := (B : ℤ) * (A : ℤ)

/-! ### `ι` and polynomials -/

theorem zE_gPolyHom_smul (s : EAB EA EB) (y : ZZg A B) :
    zE (A + B) (gPolyHom (s • y)) = gIota EA EB HN s • zE (A + B) (gPolyHom y) := by
  have h1 : gIndInv (zE (A + B) (gPolyHom y)) = TensorProductOver.tmul _ y (gZabOne A B) := by
    change TensorProductOver.tmul _ (gPolyEquiv.symm ((zE _).symm (zE _ (gPolyHom y)))) _ = _
    rw [AddEquiv.symm_apply_apply, ← gPolyEquiv_apply, AddEquiv.symm_apply_apply]
  rw [gIota_smul, conjMap_apply, h1]
  change _ = zE _ (gPolyHom (s • y) * EQZab.tauAB A B (gTwVal (gZabOne A B)))
  rw [gTwVal_one, map_one, sp_mul_one']

/-- `ι(s)` commutes with right multiplication by `(θ_A ⊗ θ_B)(G)`, `G ∈ OΛ_{A,B}`. -/
theorem zE_symm_gIota_smul_mul_tau (s : EAB EA EB) (F G : SkewPolynomial (A + B)) (hG : G ∈ osymAB A B) :
    (zE (A + B)).symm (gIota EA EB HN s • zE (A + B) (F * EQZab.tauAB A B G)) =
      (zE (A + B)).symm (gIota EA EB HN s • zE (A + B) F) * EQZab.tauAB A B G := by
  obtain ⟨y, rfl⟩ : ∃ y, gPolyHom y = F := ⟨gPolyEquiv.symm F, by
    rw [← gPolyEquiv_apply, AddEquiv.apply_symm_apply]⟩
  let FG : ZabTwG A B := show EQFix.Zab A B from EQFix.Zab.mk G hG
  have hΨ : zE (A + B) (gPolyHom y * EQZab.tauAB A B G) = gIndHom (TensorProductOver.tmul _ y FG) := rfl
  rw [hΨ, show gIota EA EB HN s • gIndHom (TensorProductOver.tmul _ y FG) =
      gIndHom (s • TensorProductOver.tmul _ y FG) from iotaFun_smul_indHom HN s _,
    ← zE_gPolyHom_smul HN s y, AddEquiv.symm_apply_apply, TensorProductOver.smul_tmul]
  rfl

theorem tauAB_PAG_mem : EQZab.tauAB A B (PAG A B) ∈ osymAB A B := by
  rw [PAG, map_pow, topY, EQZab.tauAB_inclY]
  exact pow_mem (EQZab.inclY_mem (by
    rw [theta_eq_diagHom, diagHom_elementary_top]
    exact zsmul_mem (EQZab.elementary_mem B B) _)) _

theorem zE_symm_gIota_smul_mul_PA (s : EAB EA EB) (F : SkewPolynomial (A + B)) :
    (zE (A + B)).symm (gIota EA EB HN s • zE (A + B) (F * PAG A B)) =
      (zE (A + B)).symm (gIota EA EB HN s • zE (A + B) F) * PAG A B := by
  have h := zE_symm_gIota_smul_mul_tau HN s F _ (tauAB_PAG_mem (A := A) (B := B))
  rwa [EQZab.tauAB_tauAB] at h

/-! ### `P^A` in `E_{A+B}` -/

theorem PAG_mul_op_smul (c : osymDG (A + B)) (z : Zn (A + B)) :
    zE (A + B) (PAG A B * (zE (A + B)).symm (op c • z)) = op c • zE (A + B) (PAG A B * (zE (A + B)).symm z) := by
  apply (zE (A + B)).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change PAG A B * ((zE (A + B)).symm z * twistRev (A + B) (EQFix.toSkew c)) =
    (zE (A + B)).symm (zE (A + B) (PAG A B * (zE (A + B)).symm z)) * twistRev (A + B) (EQFix.toSkew c)
  rw [AddEquiv.symm_apply_apply, EQBorel.sp_mul_assoc]

/-- `z ↦ P^A z` on `Z_{A+B}`. -/
def pwMap : Zn (A + B) →+ Zn (A + B) :=
  AddMonoidHom.mk' (fun z => zE (A + B) (PAG A B * (zE (A + B)).symm z)) fun z z' => by
    rw [map_add, mul_add, map_add]

variable (A B) in
/-- `P^A ∈ E_{A+B}`. -/
def PwG : EN := (HN.full pwMap fun c z => PAG_mul_op_smul c z).choose

theorem PwG_smul (z : Zn (A + B)) : PwG A B HN • z = zE (A + B) (PAG A B * (zE (A + B)).symm z) :=
  (HN.full pwMap fun c z => PAG_mul_op_smul c z).choose_spec z

theorem zE_symm_PwG_smul (z : Zn (A + B)) :
    (zE (A + B)).symm (PwG A B HN • z) = PAG A B * (zE (A + B)).symm z := by
  rw [PwG_smul HN, AddEquiv.symm_apply_apply]

theorem PwG_smul_eq_zero {z : Zn (A + B)} (h : PwG A B HN • z = 0) : z = 0 := by
  apply (zE (A + B)).symm.injective
  rw [map_zero]
  apply topY_pow_mul_eq_zero (A := A) (B := B) A
  rw [← zE_symm_PwG_smul HN, h, map_zero]

theorem PwG_mul_eq_zero {h : EN} (hh : PwG A B HN * h = 0) : h = 0 :=
  HN.faithful h fun z => PwG_smul_eq_zero HN (by rw [← mul_smul, hh, zero_smul])

theorem PwG_mem : PwG A B HN ∈ DG.grading (degPG A B) :=
  HN.mem_grading _ _ fun j z hz => by
    rw [PwG_smul HN]
    refine OPolAlpha.mem_grading_iff.mpr ?_
    rw [AddEquiv.symm_apply_apply]
    have h := topY_pow_mem_grading (A := A) (B := B) A
    exact mul_mem_grading' h (OPolAlpha.mem_grading_iff.mp hz)

section Theta



variable (A B) in
/-- `OΛ_{a+b} → OΛ_a ⊗ OΛ_b`, `h ↦ h(y, x)`. -/
def swapDGG : osymDG (A + B) →ᵈᵍ+* (LABg A B) :=
  (tensorEquivOsymAB A B).symm.toDGAlgHom.toDGRingHom.comp (swapOsym A B)

variable (A B) in
/-- **`Z^♮_{a,b}`** (Definition 4.15): `OΛ_a ⊗ OΛ_b` as a dg `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule, with
`OΛ_{a+b}` acting on the right through `h ↦ h(y, x)`. -/
abbrev ZNatG : Type := (swapDGG A B).Bimodule


theorem rHat_swapDGG (h : osymDG (A + B)) :
    gRHat (swapDGG A B h) = swapPoly A B (EQFix.toSkew h) := by
  have h1 : tensorToOsymAB A B (swapDGG A B h) = swapOsym A B h :=
    (tensorEquivOsymAB_apply _).symm.trans ((tensorEquivOsymAB A B).apply_symm_apply _)
  rw [gRHat, ← coe_tensorToOsymAB, h1]
  rfl

/-- `y ⊗ r ↦ (y · r)(x, y)`, without `P^a`. -/
def thetaCFunG : ZZg A B →+ ZNatG A B →+ SkewPolynomial (A + B) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun r => gPolyHom (op ((swapDGG A B).bimoduleEquiv.symm r) • y))
      fun r r' => by rw [map_add, MulOpposite.op_add, add_smul, map_add])
    fun y y' => AddMonoidHom.ext fun r => by
      change gPolyHom (op _ • (y + y')) = gPolyHom (op _ • y) + gPolyHom (op _ • y')
      rw [smul_add, map_add]

theorem thetaCFun_balancedG (r' : LABg A B) (y : ZZg A B) (r : ZNatG A B) :
    thetaCFunG (op r' • y) r = thetaCFunG y (r' • r) := by
  change gPolyHom (op _ • op r' • y) = gPolyHom (op ((swapDGG A B).bimoduleEquiv.symm (r' • r)) • y)
  rw [← mul_smul, ← op_mul]
  rfl

/-- `Θ_c : (Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b} → OPol_{a+b}`, `y ⊗ r ↦ (y r)(x, y)`. -/
def thetaCG : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B) →+ SkewPolynomial (A + B) :=
  TensorProductOver.lift thetaCFunG thetaCFun_balancedG

theorem thetaC_tmulG (y : ZZg A B) (r : ZNatG A B) :
    thetaCG (TensorProductOver.tmul _ y r) = gPolyHom (op ((swapDGG A B).bimoduleEquiv.symm r) • y) := rfl

/-- The right action of `h ∈ OΛ_{a+b}` on `Z^♮` becomes right multiplication by
`(θ_a ⊗ θ_b)((w₀ × w₀)(h(y, x)))`. -/
theorem thetaC_op_smulG (h : osymDG (A + B))
    (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    thetaCG (op h • t) = thetaCG t * EQZab.tauAB A B
      (blockRev A B (swapPoly A B (EQFix.toSkew h))) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, EQBorel.sp_zero_mul]
  | tmul y r =>
    rw [TensorProductOver.op_smul_tmul_right, thetaC_tmulG, thetaC_tmulG]
    change gPolyHom (op ((swapDGG A B).bimoduleEquiv.symm r * swapDGG A B h) • y) = _
    rw [op_mul, mul_smul, gPolyHom_op_smul, rHat_swapDGG]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', add_mul]

theorem thetaC_surjectiveG : Function.Surjective (thetaCG (A := A) (B := B)) := fun F => by
  obtain ⟨y, hy⟩ := gPolyHom_bijective.2 F
  exact ⟨TensorProductOver.tmul _ y ((swapDGG A B).bimoduleEquiv 1), by
    rw [thetaC_tmulG, DGRingHom.Bimodule.bimoduleEquiv_symm_apply, op_one, one_smul, hy]⟩

theorem thetaC_memG {k : ℤ} {t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)}
    (ht : t ∈ DG.grading k) : thetaCG t ∈ grading (A + B) k := by
  refine TensorProductOver.induction_on_mem_grading (P := fun t => thetaCG t ∈ grading _ k) ?_ ?_ ?_ ?_ ht
  · rw [map_zero]; exact zero_mem _
  · intro i j y r hy hr hij
    rw [thetaC_tmulG, ← hij]
    exact gPolyHom_mem (op_smul_mem_grading (M := ZZg A B) hr hy)
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

theorem zE_thetaC_smulG (s : EAB EA EB) (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    zE (A + B) (thetaCG (s • t)) = gIota EA EB HN s • zE (A + B) (thetaCG t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
  | tmul y r =>
    rw [TensorProductOver.smul_tmul, thetaC_tmulG, thetaC_tmulG, ← DGBimodule.smul_op_smul, zE_gPolyHom_smul HN]
  | add t t' ht ht' =>
    rw [show s • (t + t') = s • t + s • t' from smul_add s t t', map_add, map_add, ht, ht', map_add,
      map_add, smul_add]

theorem thetaC_tmul_dG (y : ZZg A B) {i : ℤ} (hy : y ∈ DG.grading i) (r : LABg A B) :
    thetaCG (DG.d (TensorProductOver.tmul _ y ((swapDGG A B).bimoduleEquiv r))) =
      dAlpha (zAB A B) (thetaCG (TensorProductOver.tmul _ y ((swapDGG A B).bimoduleEquiv r))) := by
  have h1 := TensorProductOver.d_tmul_of_mem (A := LABg A B) hy ((swapDGG A B).bimoduleEquiv r)
  have e1 : gPolyHom (DG.d (op r • y)) = dAlpha (zAB A B) (gPolyHom (op r • y)) := gPolyHom_d _
  have e2 : DG.d (op r • y) = op r • DG.d y + koszulSign i • (op (DG.d r) • y) := d_op_smul hy r
  rw [h1, map_add, map_units_zsmul]
  change gPolyHom (op r • DG.d y) + koszulSign i • gPolyHom (op (DG.d r) • y) =
    dAlpha (zAB A B) (gPolyHom (op r • y))
  rw [← map_units_zsmul, ← map_add, ← e2, e1]

theorem thetaC_dG (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    thetaCG (DG.d t) = dAlpha (zAB A B) (thetaCG t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [d_zero, map_zero, map_zero]
  | tmul y r =>
    obtain ⟨r, rfl⟩ := (swapDGG A B).bimoduleEquiv.surjective r
    induction y using DG.induction_on with
    | h_zero => rw [TensorProductOver.zero_tmul, d_zero, map_zero, map_zero]
    | @h_homogeneous i y => exact thetaC_tmul_dG (y : ZZg A B) y.2 _
    | h_add y y' hy hy' => simp only [TensorProductOver.add_tmul, map_add, hy, hy']
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The inverse of `Θ_c`: `F ↦ (u ⊠ v) ⊗ 1` for `F = u(x) v(y)`. -/
def thetaCInvG : SkewPolynomial (A + B) →+ TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B) :=
  AddMonoidHom.mk' (fun F => TensorProductOver.tmul _ (gPolyEquiv.symm F) ((swapDGG A B).bimoduleEquiv 1))
    fun F F' => by rw [map_add, TensorProductOver.add_tmul]

theorem thetaC_thetaCInvG (F : SkewPolynomial (A + B)) : thetaCG (thetaCInvG F) = F := by
  change thetaCG (TensorProductOver.tmul _ _ _) = F
  rw [thetaC_tmulG, DGRingHom.Bimodule.bimoduleEquiv_symm_apply, op_one, one_smul, ← gPolyEquiv_apply,
    AddEquiv.apply_symm_apply]

theorem thetaCInv_thetaCG (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    thetaCInvG (thetaCG t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y r =>
    rw [thetaC_tmulG]
    change TensorProductOver.tmul _ (gPolyEquiv.symm (gPolyEquiv _)) _ = _
    rw [AddEquiv.symm_apply_apply]
    conv_rhs => rw [show r = (swapDGG A B).bimoduleEquiv.symm r • (swapDGG A B).bimoduleEquiv 1 from by
      rw [DGRingHom.Bimodule.smul_bimoduleEquiv, mul_one]; rfl]
    rw [← TensorProductOver.op_smul_tmul]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

theorem thetaC_injectiveG : Function.Injective (thetaCG (A := A) (B := B)) :=
  Function.LeftInverse.injective thetaCInv_thetaCG


end Theta

section ThetaP



/-- `Θ(t) = Θ_c(t) P^a ∈ Z_{a+b}`. -/
def thetaPG : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B) →+ Zn (A + B) :=
  AddMonoidHom.mk' (fun t => zE _ (thetaCG t * PAG A B)) fun t t' => by rw [map_add, add_mul, map_add]

theorem thetaP_applyG (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    thetaPG t = zE _ (thetaCG t * PAG A B) := rfl

theorem thetaP_smulG (s : EAB EA EB) (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    thetaPG (s • t) = gIota EA EB HN s • thetaPG t := by
  rw [thetaP_applyG, thetaP_applyG]
  apply (zE _).symm.injective
  rw [zE_symm_gIota_smul_mul_PA HN s _, ← zE_thetaC_smulG HN, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

theorem thetaP_dG (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    thetaPG (DG.d t) = DG.d (thetaPG t) := by
  rw [thetaP_applyG, thetaP_applyG, thetaC_dG]
  apply (zE _).symm.injective
  rw [OPolAlpha.symm_d, indicator_oddStrands, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    dAlpha_mul_PAG]

theorem thetaP_memG {k : ℤ} {t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)}
    (ht : t ∈ DG.grading k) : thetaPG t ∈ DG.grading (k + degPG A B) := by
  rw [thetaP_applyG]
  refine OPolAlpha.mem_grading_iff.mpr ?_
  rw [AddEquiv.symm_apply_apply]
  have h := topY_pow_mem_grading (A := A) (B := B) A
  exact mul_mem_grading' (thetaC_memG ht) h

theorem thetaP_op_smulG {k : ℤ} {h : osymDG (A + B)} (hh : h ∈ DG.grading k)
    (t : TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)) :
    thetaPG (op h • t) = ((koszulSign k : ℤ) ^ (A * B)) • (op h • thetaPG t) := by
  rw [thetaP_applyG, thetaP_applyG, thetaC_op_smulG]
  apply (zE _).symm.injective
  have hk : twistRev (A + B) (EQFix.toSkew h) ∈ grading _ k :=
    EQFunctor.twistRev_mem_grading (EQFix.Zab.toSkew_mem_grading (a := A) (b := B) hh)
  have hτ := RingHom.congr_fun (tau_blockRev_swapG (A := A) (B := B)) (EQFix.toSkew h)
  simp only [RingHom.comp_apply] at hτ
  rw [hτ, pow_parityInv_of_mem _ (chiG_mem_grading hk), AddEquiv.symm_apply_apply, map_zsmul,
    EQSkewDifferential.Zn.op_smul_osym, EQSkewDifferential.Zn.symm_op_smul, AddEquiv.symm_apply_apply,
    mul_smul_comm, smul_mul_assoc, EQBorel.sp_mul_assoc, mul_PAG_eq, chiG_chiG, ← EQBorel.sp_mul_assoc]
  rfl


end ThetaP

section Compare



variable (A B) in
/-- `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b}`. -/
abbrev TTG : Type := TensorProductOver (LABg A B) (ZZg A B) (ZNatG A B)

variable (A B) in
/-- `Z_{a+b}^∨`. -/
abbrev ZDG : Type := RightDual (osymDG (A + B)) (Zn (A + B))

theorem koszulSign_degP_mulG (k : ℤ) : (koszulSign (degPG A B * k) : ℤ) = (koszulSign k : ℤ) ^ (A * B) := by
  rw [← koszulSign_natCast_mul]
  congr 2
  push_cast
  ring

theorem rho_zsmul_leftG (n : ℤ) (z : Zn (A + B)) (f : ZDG A B) :
    (HN).rho (n • z) f = n • (HN).rho z f := by
  change (HN).rhoHom (n • z) f = n • (HN).rhoHom z f
  rw [map_zsmul, AddMonoidHom.smul_apply]

theorem rho_units_smul_rightG (u : ℤˣ) (z : Zn (A + B)) (f : ZDG A B) :
    (HN).rho z (u • f) = (u : ℤ) • (HN).rho z f := by
  change (HN).rhoHom z (u • f) = (u : ℤ) • (HN).rhoHom z f
  rw [Units.smul_def, map_zsmul]

/-- `t ⊗ f ↦ Θ(t) ε^{ab}(f) ∈ ONH_{a+b}`, through the full action of `ONH_{a+b}` on `Z_{a+b}`. -/
def gFunG : TTG A B →+ ZDG A B →+ EN :=
  ((HN).rhoHom.comp thetaPG).compl₂ (signTwist (ZDG A B) (degPG A B))

theorem gFun_applyG (t : TTG A B) (f : ZDG A B) :
    gFunG HN t f = (HN).rho (thetaPG t) (signTwist (ZDG A B) (degPG A B) f) := rfl

theorem gFun_balancedG (h : osymDG (A + B)) (t : TTG A B) (f : ZDG A B) :
    gFunG HN (op h • t) f = gFunG HN t (h • f) := by
  induction h using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
  | @h_homogeneous k h =>
    rw [gFun_applyG HN, gFun_applyG HN, thetaP_op_smulG h.2, rho_zsmul_leftG HN, (HN).rho_balanced,
      signTwist_smul_of_mem _ h.2, rho_units_smul_rightG HN, koszulSign_degP_mulG]
  | h_add h h' ih ih' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, ih, ih', add_smul, map_add]

/-- `G₀ : ((Z_a ⊠ Z_b) ⊗ Z^♮) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ → ONH_{a+b}`, `t ⊗ f ↦ Θ(t) ε^{ab}(f)`. -/
def gHomG : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B) →+ EN :=
  TensorProductOver.lift (gFunG HN) (gFun_balancedG HN)

theorem gHom_tmulG (t : TTG A B) (f : ZDG A B) :
    gHomG HN (TensorProductOver.tmul _ t f) = (HN).rho (thetaPG t) (signTwist (ZDG A B) (degPG A B) f) :=
  rfl

set_option maxHeartbeats 1600000 in
theorem gHom_smulG (s : EAB EA EB) (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    gHomG HN (s • x) = gIota EA EB HN s * gHomG HN x := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul t f => rw [TensorProductOver.smul_tmul, gHom_tmulG HN, gHom_tmulG HN, thetaP_smulG HN, (HN).rho_smul_left]
  | add x y hx hy =>
    rw [show s • (x + y) = s • x + s • y from smul_add s x y, map_add, map_add, hx, hy, mul_add]

set_option maxHeartbeats 1600000 in
theorem gHom_op_smulG {i : ℤ} {g : EN} (hg : g ∈ DG.grading i)
    (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    gHomG HN (op g • x) = koszulSign (degPG A B * i) • (gHomG HN x * g) := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, zero_mul, smul_zero]
  | tmul t f =>
    rw [TensorProductOver.op_smul_tmul_right, gHom_tmulG HN, gHom_tmulG HN, signTwist_op_smul_of_mem _ hg,
      rho_units_smul_rightG HN, (HN).rho_op_smul, Units.smul_def]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, add_mul, smul_add]

set_option maxHeartbeats 1600000 in
theorem gHom_memG {k : ℤ} {x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)}
    (hx : x ∈ DG.grading k) : gHomG HN x ∈ DG.grading (k + degPG A B) := by
  refine TensorProductOver.induction_on_mem_grading (P := fun x => gHomG HN x ∈ DG.grading (k + degPG A B))
    ?_ ?_ ?_ ?_ hx
  · rw [map_zero]; exact zero_mem _
  · intro i j t f ht hf hij
    rw [gHom_tmulG HN, ← hij, show i + j + degPG A B = i + degPG A B + j by ring]
    exact (HN).rho_mem (thetaP_memG ht) (signTwist_mem _ hf)
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

set_option maxHeartbeats 1600000 in
theorem gHom_tmul_dG {i j : ℤ} {t : TTG A B} (ht : t ∈ DG.grading i) {f : ZDG A B} (hf : f ∈ DG.grading j) :
    gHomG HN (DG.d (TensorProductOver.tmul _ t f)) = DG.d (gHomG HN (TensorProductOver.tmul _ t f)) := by
  have h1 := TensorProductOver.d_tmul_of_mem (A := osymDG (A + B)) (N := ZDG A B) ht f
  rw [h1]
  rw [map_add]
  rw [map_units_zsmul]
  rw [gHom_tmulG HN]
  rw [gHom_tmulG HN]
  rw [gHom_tmulG HN]
  have h2 := thetaP_memG ht
  have h3 := signTwist_mem (degPG A B) hf
  have h4 := (HN).d_rho h2 h3
  rw [h4]
  rw [d_signTwist, rho_units_smul_rightG HN, thetaP_dG]
  rw [Units.smul_def, Units.smul_def, smul_smul, ← Units.val_mul, ← koszulSign_add]
  have e : koszulSign (i + degPG A B + degPG A B) = koszulSign i := by
    rw [add_assoc, ← two_mul, koszulSign_add, show koszulSign (2 * degPG A B) = 1 from Int.negOnePow_two_mul _,
      mul_one]
  rw [e]

set_option maxHeartbeats 1600000 in
theorem gHom_dG (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    gHomG HN (DG.d x) = DG.d (gHomG HN x) := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | tmul t f =>
    induction t using DG.induction_on with
    | h_zero => rw [TensorProductOver.zero_tmul, d_zero, map_zero, d_zero]
    | @h_homogeneous i t =>
      induction f using DG.induction_on with
      | h_zero => rw [TensorProductOver.tmul_zero, d_zero, map_zero, d_zero]
      | @h_homogeneous j f => exact gHom_tmul_dG HN t.2 f.2
      | h_add f f' hf hf' => rw [TensorProductOver.tmul_add, d_add, map_add, hf, hf', map_add, d_add]
    | h_add t t' ht ht' => rw [TensorProductOver.add_tmul, d_add, map_add, ht, ht', map_add, d_add]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]


end Compare

section Bij


/-- `Θ₁(t) = χ(Θ_c t)`, so that `Θ = P^a Θ₁` (`thetaP_eqG HN`). -/
def theta1G : TTG A B →+ Zn (A + B) :=
  AddMonoidHom.mk' (fun t => zE _ (chiG A B (thetaCG t))) fun t t' => by rw [map_add, map_add, map_add]

theorem theta1_applyG (t : TTG A B) : theta1G t = zE _ (chiG A B (thetaCG t)) := rfl

theorem thetaP_eqG (t : TTG A B) : thetaPG t = PwG A B HN • theta1G t := by
  apply (zE (A + B)).symm.injective
  rw [zE_symm_PwG_smul HN, thetaP_applyG, theta1_applyG, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    mul_PAG_eq]

theorem Pw_smul_zsmulG (n : ℤ) (z : Zn (A + B)) : PwG A B HN • (n • z) = n • (PwG A B HN • z) :=
  map_zsmul (DistribSMul.toAddMonoidHom (Zn (A + B)) (PwG A B HN)) n z

theorem theta1_op_smulG {k : ℤ} {h : osymDG (A + B)} (hh : h ∈ DG.grading k) (t : TTG A B) :
    theta1G (op h • t) = ((koszulSign k : ℤ) ^ (A * B)) • (op h • theta1G t) := by
  have e := congrArg (zE (A + B)).symm (thetaP_op_smulG hh t)
  rw [thetaP_applyG, thetaP_applyG, AddEquiv.symm_apply_apply, map_zsmul] at e
  change thetaCG (op h • t) * PAG A B = (koszulSign k : ℤ) ^ (A * B) •
    ((zE (A + B)).symm (zE (A + B) (thetaCG t * PAG A B)) * twistRev (A + B) (EQFix.toSkew h)) at e
  rw [AddEquiv.symm_apply_apply, mul_PAG_eq (thetaCG (op h • t)), mul_PAG_eq (thetaCG t),
    EQBorel.sp_mul_assoc, ← mul_smul_comm] at e
  apply (zE (A + B)).symm.injective
  rw [theta1_applyG, AddEquiv.symm_apply_apply, map_zsmul]
  change chiG A B (thetaCG (op h • t)) = (koszulSign k : ℤ) ^ (A * B) •
    ((zE (A + B)).symm (zE (A + B) (chiG A B (thetaCG t))) * twistRev (A + B) (EQFix.toSkew h))
  rw [AddEquiv.symm_apply_apply]
  have e2 : PAG A B * (chiG A B (thetaCG (op h • t)) - (koszulSign k : ℤ) ^ (A * B) •
      (chiG A B (thetaCG t) * twistRev (A + B) (EQFix.toSkew h))) = 0 := by
    rw [show ∀ X Y Z : SkewPolynomial (A + B), X * (Y - Z) = X * Y - X * Z from
      fun X Y Z => by rw [sub_eq_add_neg, mul_add, mul_neg, ← sub_eq_add_neg], e, sub_self]
  exact sub_eq_zero.mp (topY_pow_mul_eq_zero A e2)

/-- The inverse of `Θ₁`. -/
def theta1InvG : Zn (A + B) →+ TTG A B :=
  AddMonoidHom.mk' (fun z => thetaCInvG (chiG A B ((zE _).symm z))) fun z z' => by
    rw [map_add, map_add, map_add]

theorem theta1_theta1InvG (z : Zn (A + B)) : theta1G (theta1InvG z) = z := by
  change zE _ (chiG A B (thetaCG (thetaCInvG (chiG A B ((zE _).symm z))))) = z
  rw [thetaC_thetaCInvG, chiG_chiG, AddEquiv.apply_symm_apply]

theorem theta1Inv_theta1G (t : TTG A B) : theta1InvG (theta1G t) = t := by
  change thetaCInvG (chiG A B ((zE _).symm (zE _ (chiG A B (thetaCG t))))) = t
  rw [AddEquiv.symm_apply_apply, chiG_chiG, thetaCInv_thetaCG]

theorem theta1Inv_op_smulG {k : ℤ} {h : osymDG (A + B)} (hh : h ∈ DG.grading k)
    (z : Zn (A + B)) :
    theta1InvG (op h • z) = ((koszulSign k : ℤ) ^ (A * B)) • (op h • theta1InvG z) := by
  apply Function.LeftInverse.injective theta1Inv_theta1G
  rw [theta1_theta1InvG, map_zsmul, theta1_op_smulG hh, theta1_theta1InvG, smul_smul, sign_pow_mul_self, one_smul]

/-- `t ⊗ f ↦ Θ₁(t) ⊗ ε^{ab}(f)`. -/
def oneFunG : TTG A B →+ ZDG A B →+ TensorProductOver (osymDG (A + B)) (Zn (A + B)) (ZDG A B) :=
  ((TensorProductOver.tmulAddHom _ _ _).comp theta1G).compl₂ (signTwist (ZDG A B) (degPG A B))

theorem oneFun_applyG (t : TTG A B) (f : ZDG A B) :
    oneFunG t f = TensorProductOver.tmul _ (theta1G t) (signTwist (ZDG A B) (degPG A B) f) := rfl

theorem oneFun_balancedG (h : osymDG (A + B)) (t : TTG A B) (f : ZDG A B) :
    oneFunG (op h • t) f = oneFunG t (h • f) := by
  induction h using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
  | @h_homogeneous k h =>
    rw [oneFun_applyG, oneFun_applyG, theta1_op_smulG h.2, TensorProductOver.zsmul_tmul,
      TensorProductOver.op_smul_tmul, signTwist_smul_of_mem _ h.2, TensorProductOver.tmul_units_smul,
      Units.smul_def, koszulSign_degP_mulG]
  | h_add h h' ih ih' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, ih, ih', add_smul, map_add]

/-- `Θ₁ ⊗ ε^{ab}`. -/
def oneHomG : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B) →+
    TensorProductOver (osymDG (A + B)) (Zn (A + B)) (ZDG A B) :=
  TensorProductOver.lift oneFunG oneFun_balancedG

/-- `z ⊗ f ↦ Θ₁⁻¹(z) ⊗ ε^{ab}(f)`. -/
def invFunG : Zn (A + B) →+ ZDG A B →+ TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B) :=
  ((TensorProductOver.tmulAddHom _ _ _).comp theta1InvG).compl₂ (signTwist (ZDG A B) (degPG A B))

theorem invFun_applyG (z : Zn (A + B)) (f : ZDG A B) :
    invFunG z f = TensorProductOver.tmul _ (theta1InvG z) (signTwist (ZDG A B) (degPG A B) f) := rfl

set_option maxHeartbeats 1600000 in
theorem invFun_balancedG (h : osymDG (A + B)) (z : Zn (A + B)) (f : ZDG A B) :
    invFunG (op h • z) f = invFunG z (h • f) := by
  induction h using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
  | @h_homogeneous k h =>
    rw [invFun_applyG, invFun_applyG, theta1Inv_op_smulG h.2, TensorProductOver.zsmul_tmul,
      TensorProductOver.op_smul_tmul, signTwist_smul_of_mem _ h.2, TensorProductOver.tmul_units_smul,
      Units.smul_def, koszulSign_degP_mulG]
  | h_add h h' ih ih' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, ih, ih', add_smul, map_add]

def invHomG : TensorProductOver (osymDG (A + B)) (Zn (A + B)) (ZDG A B) →+
    TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B) :=
  TensorProductOver.lift invFunG invFun_balancedG

theorem invHom_oneHomG (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    invHomG (oneHomG x) = x := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t f =>
    change TensorProductOver.tmul _ (theta1InvG (theta1G t))
      (signTwist (ZDG A B) (degPG A B) (signTwist (ZDG A B) (degPG A B) f)) = _
    rw [theta1Inv_theta1G, signTwist_signTwist]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem oneHom_invHomG (y : TensorProductOver (osymDG (A + B)) (Zn (A + B)) (ZDG A B)) :
    oneHomG (invHomG y) = y := by
  induction y using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z f =>
    change TensorProductOver.tmul _ (theta1G (theta1InvG z))
      (signTwist (ZDG A B) (degPG A B) (signTwist (ZDG A B) (degPG A B) f)) = _
    rw [theta1_theta1InvG, signTwist_signTwist]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

set_option maxHeartbeats 800000 in
theorem gHom_eqG (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    gHomG HN x = PwG A B HN * (HN).mulHom (oneHomG x) := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, mul_zero]
  | tmul t f =>
    rw [gHom_tmulG HN, thetaP_eqG HN, (HN).rho_smul_left]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, mul_add]

theorem gHom_injectiveG : Function.Injective (gHomG HN) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [gHom_eqG HN] at hx
  have h1 := (HN).mulHom_injective (znRightBasis (A + B))
    ((PwG_mul_eq_zero HN hx).trans (map_zero _).symm)
  rw [← invHom_oneHomG x, h1, map_zero]

theorem exists_gHom_eqG (g : EN) : ∃ x, gHomG HN x = PwG A B HN * g := by
  obtain ⟨y, hy⟩ := (HN).mulHom_surjective (znRightBasis (A + B)) g
  exact ⟨invHomG y, by rw [gHom_eqG HN, oneHom_invHomG, hy]⟩


end Bij

section GEquiv

variable (A B EA EB) in
/-- `ι^* E_{A+B}`. -/
abbrev IONHG : Type := RestrictScalars (gIota EA EB HN) EN

theorem gIota_smul_IONHG (s : EAB EA EB) (x : IONHG A B EA EB HN) :
    s • x = (show IONHG A B EA EB HN from gIota EA EB HN s * (show EN from x)) := rfl

theorem gHomG_smul_mul (s : EAB EA EB) (h : EN) : ∃ h' : EN, gIota EA EB HN s * (PwG A B HN * h) = PwG A B HN * h' := by
  obtain ⟨x, hx⟩ := exists_gHom_eqG HN h
  exact ⟨HN.mulHom (oneHomG (s • x)), by rw [← hx, ← gHom_smulG HN, gHom_eqG HN]⟩

variable (A B EA EB) in
/-- **The right ideal `P^A E_{A+B}`** as a dg left `E_A ⊗ E_B`-submodule of `ι^* E_{A+B}`. -/
def natSubG : DGSubmodule (EAB EA EB) (IONHG A B EA EB HN) where
  carrier := {x | ∃ h : EN, (show EN from x) = PwG A B HN * h}
  add_mem' := by
    rintro x y ⟨h, hx⟩ ⟨h', hy⟩
    exact ⟨h + h', by rw [mul_add, ← hx, ← hy]⟩
  zero_mem' := ⟨0, by rw [mul_zero]⟩
  smul_mem' s x := by
    rintro ⟨h, hx⟩
    obtain ⟨h', hh'⟩ := gHomG_smul_mul HN s h
    exact ⟨h', by rw [gIota_smul_IONHG]; change gIota EA EB HN s * _ = _; rw [hx, hh']⟩
  d_mem' {x} := by
    rintro ⟨h, hx⟩
    obtain ⟨y, hy⟩ := exists_gHom_eqG HN h
    refine ⟨(HN.mulHom (oneHomG (DG.d y))), ?_⟩
    change DG.d (show EN from x) = _
    rw [hx, ← hy, ← gHom_dG HN, gHom_eqG HN]
  decompose_mem' k {x} hx := by
    obtain ⟨h, hx⟩ := hx
    change ∃ h', (DirectSum.decompose (DG.grading (M := EN)) (show EN from x) k : EN) = PwG A B HN * h'
    rw [hx]
    clear hx
    induction h using DG.induction_on generalizing k with
    | h_zero => exact ⟨0, by simp⟩
    | @h_homogeneous j h =>
      have hm : PwG A B HN * (h : EN) ∈ DG.grading (degPG A B + j) := DG.mul_mem_grading (PwG_mem HN) h.2
      by_cases hk : degPG A B + j = k
      · subst hk
        exact ⟨h, by rw [DirectSum.decompose_of_mem_same _ hm]⟩
      · exact ⟨0, by rw [DirectSum.decompose_of_mem_ne _ hm hk, mul_zero]⟩
    | h_add h h' ih ih' =>
      obtain ⟨u, hu⟩ := ih k
      obtain ⟨u', hu'⟩ := ih' k
      exact ⟨u + u', by rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, AddSubgroup.coe_add,
        hu, hu', mul_add]⟩

theorem mem_natSubG_mul {x : IONHG A B EA EB HN} (hx : x ∈ natSubG A B EA EB HN) (g : EN) :
    (show IONHG A B EA EB HN from (show EN from x) * g) ∈ natSubG A B EA EB HN := by
  obtain ⟨h, hx⟩ := hx
  exact ⟨h * g, by change (show EN from x) * g = _; rw [hx, mul_assoc]⟩

instance natSubGSMulOp : SMul ENᵐᵒᵖ (natSubG A B EA EB HN) :=
  ⟨fun g x => ⟨_, mem_natSubG_mul HN x.2 g.unop⟩⟩

instance natSubGModuleOp : Module ENᵐᵒᵖ (natSubG A B EA EB HN) :=
  Function.Injective.module ENᵐᵒᵖ (AddSubmonoidClass.subtype (natSubG A B EA EB HN))
    Subtype.val_injective fun _ _ => rfl

instance natSubGDGRightModule : DGRightModule EN (natSubG A B EA EB HN) where
  op_smul_mem' {i j g x} hg hx :=
    (DGSubmodule.mem_grading_iff _).mpr (op_smul_mem_grading (M := IONHG A B EA EB HN) hg
      ((DGSubmodule.mem_grading_iff _).mp hx))
  d_op_smul' {j x} hx g := Subtype.ext (by
    change DG.d ((op g • (x : IONHG A B EA EB HN))) = op g • DG.d (x : IONHG A B EA EB HN) +
      koszulSign j • (op (DG.d g) • (x : IONHG A B EA EB HN))
    exact d_op_smul (M := IONHG A B EA EB HN) ((DGSubmodule.mem_grading_iff _).mp hx) g)

instance natSubGSMulCommClass : SMulCommClass (EAB EA EB) ENᵐᵒᵖ (natSubG A B EA EB HN) where
  smul_comm s g x := Subtype.ext (smul_comm s g (x : IONHG A B EA EB HN))

instance natSubGDGBimodule : DGBimodule (EAB EA EB) EN (natSubG A B EA EB HN) := DGBimodule.mk'

variable (A B EA EB) in
/-- **`ONH^♮_{A+B}`**: the right ideal `P^A E_{A+B}`, regraded so that `P^A` has degree `0`. -/
abbrev ONHNatG : Type := Regrade (degPG A B) (natSubG A B EA EB HN)



theorem gHom_mem_natSubG (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    (show IONHG A B EA EB HN from gHomG HN x) ∈ natSubG A B EA EB HN :=
  ⟨_, gHom_eqG HN x⟩

variable (EA EB) in
/-- `G₀` as a map into `P^a ONH_{a+b}`. -/
def gNatG : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B) →+ natSubG A B EA EB HN :=
  AddMonoidHom.mk' (fun x => ⟨gHomG HN x, gHom_mem_natSubG HN x⟩) fun x y => Subtype.ext (map_add (gHomG HN) x y)

theorem coe_gNatG (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    ((gNatG EA EB HN x : natSubG A B EA EB HN) : IONHG A B EA EB HN) = gHomG HN x := rfl

theorem gNat_injectiveG : Function.Injective (gNatG EA EB HN) := fun _ _ h =>
  gHom_injectiveG HN (congrArg Subtype.val h)

theorem gNat_surjectiveG : Function.Surjective (gNatG EA EB HN) := fun m => by
  obtain ⟨g, hg⟩ := m.2
  obtain ⟨x, hx⟩ := exists_gHom_eqG HN g
  exact ⟨x, Subtype.ext (hx.trans hg.symm)⟩

variable (EA EB) in
/-- `G₀` as a linear map into `ONH^♮`. -/
def gLinG : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B) →ₗ[EAB EA EB] ONHNatG A B EA EB HN where
  toFun x := Regrade.mk (degPG A B) (gNatG EA EB HN x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' s x := by
    change (gNatG EA EB HN (s • x) : natSubG A B EA EB HN) = s • gNatG EA EB HN x
    exact Subtype.ext (gHom_smulG HN s x)

variable (EA EB) in
/-- **The bimodule isomorphism behind the restriction half of Corollary 4.21**:
`((Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b}) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ ≅ ONH^♮_{a+b}` as dg
`(ONH_a ⊗ ONH_b, ONH_{a+b})`-bimodules (`gEquiv_op_smulG HN`), `t ⊗ f ↦ Θ(t) ε^{ab}(f)`. -/
def gEquivG : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B) ≃ᵈᵍ[EAB EA EB]
    ONHNatG A B EA EB HN where
  toLinearEquiv := LinearEquiv.ofBijective (gLinG EA EB HN) ⟨fun _ _ h => gNat_injectiveG HN h, fun m => gNat_surjectiveG HN m⟩
  map_mem' {k x} hx :=
    show (gNatG EA EB HN x : natSubG A B EA EB HN) ∈ DG.grading (k + degPG A B) from
      (DGSubmodule.mem_grading_iff _).mpr (gHom_memG HN hx)
  map_d' x := show (gNatG EA EB HN (DG.d x) : natSubG A B EA EB HN) = DG.d (gNatG EA EB HN x) from Subtype.ext (gHom_dG HN x)

theorem gEquiv_applyG (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    gEquivG EA EB HN x = Regrade.mk (degPG A B) (gNatG EA EB HN x) := rfl

set_option maxHeartbeats 800000 in
theorem gEquiv_op_smulG (g : EN)
    (x : TensorProductOver (osymDG (A + B)) (TTG A B) (ZDG A B)) :
    gEquivG EA EB HN (op g • x) = op g • gEquivG EA EB HN x := by
  induction g using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, map_zero, zero_smul]
  | @h_homogeneous i g =>
    rw [gEquiv_applyG HN, gEquiv_applyG HN, Regrade.op_smul_mk_of_mem g.2]
    congr 1
    apply Subtype.ext
    rw [coe_gNatG HN, gHom_op_smulG HN g.2]
    rfl
  | h_add g g' hg hg' => rw [MulOpposite.op_add, add_smul, map_add, hg, hg', add_smul]


end GEquiv

end OddMath.Frontier.EQLift
