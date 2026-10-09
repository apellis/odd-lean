import OddMath.Frontier.EQActionCompareRes

/-!
# The induction bimodule of Corollary 4.21 in all ranks

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6 ((3.39), the inclusion `ι_{m,n} : ONH_m ⊗ ONH_n ↪ ONH_{m+n}`), §4.3 (Definition 4.6) and §4.4 (the
induction half of Corollary 4.21), for all ranks `A`, `B` (including `0` and `1`).

The polynomial part of `EQFunctor.indEquiv` holds in every rank: with `Z_{A,B}` the bimodule of
Definition 4.6 (`OΛ_A ⊗ OΛ_B` acting through `w₀ × w₀`, `ZabTwG`), the map
`Ψ : (Z_A ⊠ Z_B) ⊗_{OΛ_A ⊗ OΛ_B} Z_{A,B} → Z_{A+B}`, `y ⊗ F ↦ y (θ_A ⊗ θ_B)(F)` (`gIndHom`), is a bijection
(`gIndInv`) compatible with the gradings, the differentials and the right actions of `OΛ_{A+B}`.

Let `E_A`, `E_B`, `E_N` (`N = A + B`) be dg rings acting fully on `Z_A`, `Z_B`, `Z_N` (`DG.FullAction`;
for `E_N = ONH_N` this is Corollary 3.9, for `N ≤ 1` it is `OPol_N`). Since `E_N` consists of all right
`OΛ_N`-linear endomorphisms of `Z_N`, transporting the left action of `E_A ⊗ E_B` along `Ψ` defines a morphism of
dg rings `gIota : E_A ⊗ E_B → E_N` (`ι(s) z = Ψ(s · Ψ⁻¹(z))`), and `Ψ` is an isomorphism of dg
`(E_A ⊗ E_B, OΛ_N)`-bimodules `(Z_A ⊠ Z_B) ⊗ Z_{A,B} ≅ ι^* Z_N` (`gIndEquiv`). For `E = ONH` this `ι` is the
inclusion of Ellis–Qi (3.39) (comparison theorems in `EQLiftCompare`).
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

section Poly

variable (A B : ℕ)

local notation "ΛA" => DGAlgebra.gradingSubmodule ℤ (osymDG A)
local notation "ΛB" => DGAlgebra.gradingSubmodule ℤ (osymDG B)

/-- `Z_A ⊠ Z_B`. -/
abbrev ZZg : Type := Zn A ⊗[ℤ] Zn B

/-- `Z_{A,B}` of Definition 4.6, a dg `(OΛ_A ⊗ OΛ_B, OΛ_{A+B})`-bimodule (`f ⊗ g` acting by `(w₀ × w₀)(f(x) g(y))`). -/
abbrev ZabTwG : Type := RestrictScalars (tensorToOsymAB A B) (EQFix.Zab A B)

variable {A B}

/-- `u 1_z ⊠ v 1_z ↦ u(x) v(y)`. -/
def gPolyHom : ZZg A B →+ SkewPolynomial (A + B) :=
  (OPol.equiv _).symm.toAddMonoidHom.comp (opolMul A B).toAddMonoidHom

theorem gPolyHom_tmul (u : Zn A) (v : Zn B) :
    gPolyHom (u ⊗ₜ[ℤ] v) = inclX A B ((zE _).symm u) * inclY A B ((zE _).symm v) :=
  rfl

theorem gPolyHom_mem {k : ℤ} {y : ZZg A B} (hy : y ∈ DG.grading k) :
    gPolyHom y ∈ grading (A + B) k := by
  have key : ∀ {i j : ℤ} {u : Zn A} {v : Zn B}, u ∈ DG.grading i →
      v ∈ DG.grading j → zE _ (gPolyHom (u ⊗ₜ[ℤ] v)) ∈ DG.grading (i + j) := fun hu hv =>
    OPolAlpha.mem_grading_iff.mpr (by
      rw [AddEquiv.symm_apply_apply, gPolyHom_tmul]
      exact mul_mem_grading' (inclX_mem_grading (OPolAlpha.mem_grading_iff.mp hu))
        (inclY_mem_grading (OPolAlpha.mem_grading_iff.mp hv)))
  have := DG.map_mem_grading_of_tmul ((zE _).toAddMonoidHom.comp gPolyHom) 0
    (fun hu hv => by simpa using key hu hv) hy
  simpa using OPolAlpha.mem_grading_iff.mp this

theorem g_inclX_mul_inclY_of_mem_one {u : SkewPolynomial A} (hu : u ∈ grading A 1)
    (g : SkewPolynomial B) :
    inclX A B u * inclY A B g =
      inclY A B (parityInv B g) * inclX A B u := by
  rw [inclY_mul_inclX_pow_parityInv hu, show (1 : ℤ).natAbs = 1 from rfl, pow_one,
    parityInv_parityInv]

theorem g_sAlpha_zAB :
    sAlpha (zAB A B) =
      inclX A B (sAlpha (zAlpha A)) + inclY A B (sAlpha (zAlpha B)) := by
  rw [sAlpha, Fin.sum_univ_add, sAlpha, sAlpha, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [zAB, zAlpha, i.isLt]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zAB, zAlpha, Fin.val_natAdd, map_zsmul, EQZab.inclY_generator]
    simp only [show ¬(A + j.val < A) by omega, ↓reduceIte,
      show A + j.val - A = j.val by omega]

/-- `d(u ⊠ v) ↦ d_β(u(x) v(y))`, `β = (0,1,0,1,…) ⊔ (0,1,0,1,…)`. -/
theorem gPolyHom_d (y : ZZg A B) :
    gPolyHom (DG.d y) = dAlpha (zAB A B) (gPolyHom y) := by
  induction y using TensorProduct.inductionOn with
  | tmul u v =>
    rw [DG.d_tmul, map_add, gPolyHom_tmul, gPolyHom_tmul, gPolyHom_tmul, OPolAlpha.symm_d,
      OPolAlpha.symm_d, zE_symm_gradeInvolution, indicator_oddStrands, indicator_oddStrands,
      dAlpha_apply, dAlpha_apply, dAlpha_apply, EQSkewDifferential.d_mul, map_add, map_add, map_mul, map_mul,
      EQZab.d_inclX, EQZab.d_inclY, map_mul, EQZab.parityInv_inclX, EQZab.parityInv_inclY,
      g_sAlpha_zAB]
    set u' := (zE A).symm u
    set v' := (zE B).symm v
    have hc := g_inclX_mul_inclY_of_mem_one (B := B) (sAlpha_mem_grading (zAlpha A)) v'
    simp only [add_mul, mul_add]
    rw [EQBorel.sp_mul_assoc, hc, ← EQBorel.sp_mul_assoc, ← EQBorel.sp_mul_assoc]
    abel
  | add y y' hy hy' => rw [DG.d_add, map_add, map_add, hy, hy', map_add]

/-- The skew polynomial `f(x) g(y)` of `f ⊗ g ∈ OΛ_a ⊗ OΛ_b`. -/
def gRHat (r : ΛA ᵍ⊗[ℤ] ΛB) : SkewPolynomial (A + B) :=
  (OPol.equiv _).symm (tensorToOPol A B r)

theorem gRHat_add (r r' : ΛA ᵍ⊗[ℤ] ΛB) : gRHat (r + r') = gRHat r + gRHat r' := by
  rw [gRHat, map_add, map_add]
  rfl

theorem gRHat_tmul (f : osymDG A) (g : osymDG B) :
    gRHat (f ᵍ⊗ₜ[ℤ] g) = inclX A B ((OPol.equiv _).symm f) *
      inclY A B ((OPol.equiv _).symm g) := by
  rw [gRHat, tensorToOPol_tmul]
  rfl

/-- The right action of `f ⊗ g ∈ OΛ_a ⊗ OΛ_b` on `Z_a ⊠ Z_b` is right multiplication by
`(θ ∘ w₀)(f)(x) (θ ∘ w₀)(g)(y) = (θ_a ⊗ θ_b)((w₀ × w₀)(f(x) g(y)))`. -/
theorem gPolyHom_op_smul (r : ΛA ᵍ⊗[ℤ] ΛB) (y : ZZg A B) :
    gPolyHom (op r • y) = gPolyHom y * EQZab.tauAB A B (blockRev A B (gRHat r)) := by
  induction r using GradedTensorProduct.induction_on_tmul with
  | zero => rw [ExternalTensor.zero_op_smul', map_zero, gRHat, map_zero, map_zero, map_zero,
      map_zero, EQBorel.sp_mul_zero]
  | @tmul i j f hf g hg =>
    induction y using DG.tensor_induction_on with
    | zero => rw [smul_zero, map_zero, EQBorel.sp_zero_mul]
    | @tmul k l u v =>
      rw [ExternalTensor.tmul_op_smul_tmul hf g (u : Zn A) v.2, map_units_zsmul, gPolyHom_tmul,
        gPolyHom_tmul, gRHat_tmul, map_mul, map_mul, blockRev_inclX, blockRev_inclY, EQZab.tauAB_inclX,
        EQZab.tauAB_inclY]
      have hf' : twistRev A ((OPol.equiv _).symm (f : OPol A)) ∈ grading A i :=
        EQFunctor.twistRev_mem_grading (OPol.equiv_mem_grading_iff.mp ((DGSubring.mem_grading_iff _).mp hf))
      have hv : (zE B).symm (v : Zn B) ∈ grading B l :=
        OPolAlpha.mem_grading_iff.mp v.2
      have hc := inclY_mul_inclX_of_mem (a := A) (b := B) hf' hv
      change (koszulSign (i * l)) • (inclX A B ((zE _).symm (u : Zn A) *
          twistRev A ((OPol.equiv _).symm (f : OPol A))) *
        inclY A B ((zE _).symm (v : Zn B) *
          twistRev B ((OPol.equiv _).symm (g : OPol B)))) = _
      rw [show ∀ F, theta A (longestPerm A F) = twistRev A F from fun _ => rfl,
        show ∀ F, theta B (longestPerm B F) = twistRev B F from fun _ => rfl,
        map_mul, map_mul]
      set X := inclX A B ((zE _).symm (u : Zn A))
      set Fx := inclX A B (twistRev A ((OPol.equiv _).symm (f : OPol A)))
      set Y := inclY A B ((zE _).symm (v : Zn B))
      set Gy := inclY A B (twistRev B ((OPol.equiv _).symm (g : OPol B)))
      have hc' : Fx * Y = (koszulSign (l * i) : ℤ) • (Y * Fx) := by
        rw [hc, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
      rw [Units.smul_def, EQBorel.sp_mul_assoc X Fx, ← EQBorel.sp_mul_assoc Fx Y Gy, hc',
        smul_mul_assoc, mul_smul_comm, smul_smul, ← Units.val_mul, mul_comm i l, Int.units_mul_self,
        Units.val_one, one_smul, EQBorel.sp_mul_assoc Y Fx Gy, ← EQBorel.sp_mul_assoc X Y]
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, add_mul]
  | add r r' hr hr' =>
    rw [ExternalTensor.add_op_smul', map_add, hr, hr', gRHat_add, map_add, map_add, mul_add]

theorem gPolyHom_bijective : Function.Bijective (gPolyHom (A := A) (B := B)) := by
  refine ⟨(OPol.equiv _).symm.injective.comp (opolMul_injective (a := A) (b := B)), fun F => ?_⟩
  obtain ⟨z, hz⟩ := opolTensorDG_surjective (a := A) (b := B) (OPol.equiv _ F)
  rw [opolTensorDG_eq_opolMul] at hz
  exact ⟨_, (congrArg (OPol.equiv _).symm hz).trans (RingEquiv.symm_apply_apply _ F)⟩

/-- `Z_a ⊠ Z_b ≅ OPol_{a+b}` as abelian groups. -/
def gPolyEquiv : ZZg A B ≃+ SkewPolynomial (A + B) :=
  AddEquiv.ofBijective gPolyHom gPolyHom_bijective

theorem gPolyEquiv_apply (y : ZZg A B) : gPolyEquiv y = gPolyHom y := rfl

/-! ### The bimodules -/

/-- The underlying skew polynomial of an element of `Z^{tw}_{a,b}`. -/
def gTwVal (F : ZabTwG A B) : SkewPolynomial (A + B) :=
  EQFix.Zab.val (show EQFix.Zab A B from F)

theorem gTwVal_add (F F' : ZabTwG A B) : gTwVal (F + F') = gTwVal F + gTwVal F' := rfl

theorem gTwVal_mem (F : ZabTwG A B) : gTwVal F ∈ osymAB A B := EQFix.Zab.mem _

theorem g_val_smul (r : ΛA ᵍ⊗[ℤ] ΛB) (F : ZabTwG A B) :
    gTwVal (r • F) = blockRev A B (gRHat r) * gTwVal F :=
  rfl

theorem gTwVal_op_smul (h : osymDG (A + B)) (F : ZabTwG A B) :
    gTwVal (op h • F) = gTwVal F * EQZab.phiAB _ _ (EQFix.toSkew h) := rfl

theorem gTwVal_d (F : ZabTwG A B) : gTwVal (DG.d F) = EQZab.dZ _ _ (gTwVal F) := rfl

theorem gTwVal_mem_grading {k : ℤ} {F : ZabTwG A B} (hF : F ∈ DG.grading k) :
    gTwVal F ∈ grading (A + B) k :=
  EQFix.Zab.mem_grading_iff.mp hF

/-- `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)`. -/
def gIndFun : ZZg A B →+ ZabTwG A B →+ Zn (A + B) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun F => zE (A + B)
      (gPolyHom y * EQZab.tauAB A B (gTwVal F)))
      fun F F' => by rw [gTwVal_add, map_add, mul_add, map_add])
    fun y y' => AddMonoidHom.ext fun F => by
      change zE _ (gPolyHom (y + y') * _) = zE _ (gPolyHom y * _) + zE _ (gPolyHom y' * _)
      rw [map_add, add_mul, map_add]

theorem gIndFun_apply (y : ZZg A B) (F : ZabTwG A B) :
    gIndFun y F = zE (A + B) (gPolyHom y * EQZab.tauAB A B (gTwVal F)) :=
  rfl

theorem gIndFun_balanced (r : ΛA ᵍ⊗[ℤ] ΛB) (y : ZZg A B) (F : ZabTwG A B) :
    gIndFun (op r • y) F = gIndFun y (r • F) := by
  rw [gIndFun_apply, gIndFun_apply, gPolyHom_op_smul, g_val_smul, map_mul (EQZab.tauAB _ _),
    EQBorel.sp_mul_assoc]

/-- `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)` on `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^{tw}_{a,b}`. -/
def gIndHom : TensorProductOver (ΛA ᵍ⊗[ℤ] ΛB) (ZZg A B) (ZabTwG A B) →+ Zn (A + B) :=
  TensorProductOver.lift gIndFun gIndFun_balanced

theorem gIndHom_tmul (y : ZZg A B) (F : ZabTwG A B) :
    gIndHom (TensorProductOver.tmul _ y F) = gIndFun y F := rfl

theorem gIndHom_op_smul (h : osymDG (A + B))
    (t : TensorProductOver (ΛA ᵍ⊗[ℤ] ΛB) (ZZg A B) (ZabTwG A B)) :
    gIndHom (op h • t) = op h • gIndHom t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul y F =>
    rw [TensorProductOver.op_smul_tmul_right, gIndHom_tmul, gIndHom_tmul, gIndFun_apply, gIndFun_apply]
    rw [gTwVal_op_smul]
    apply (zE _).symm.injective
    rw [AddEquiv.symm_apply_apply, EQSkewDifferential.Zn.op_smul_osym, EQSkewDifferential.Zn.symm_op_smul,
      AddEquiv.symm_apply_apply, map_mul, EQZab.tauAB_phiAB, EQBorel.sp_mul_assoc]
    rfl
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

theorem gIndHom_mem {k : ℤ} {t : TensorProductOver (ΛA ᵍ⊗[ℤ] ΛB) (ZZg A B) (ZabTwG A B)}
    (ht : t ∈ DG.grading k) : gIndHom t ∈ DG.grading k :=
  TensorProductOver.lift_mem gIndFun gIndFun_balanced (fun {i j y F} hy hF => by
    rw [gIndFun_apply]
    refine OPolAlpha.mem_grading_iff.mpr ?_
    rw [AddEquiv.symm_apply_apply]
    exact mul_mem_grading' (gPolyHom_mem hy) (tauAB_mem_grading (gTwVal_mem_grading hF))) ht

theorem gIndFun_d {i : ℤ} {y : ZZg A B} (hy : y ∈ DG.grading i) (F : ZabTwG A B) :
    DG.d (gIndFun y F) = gIndFun (DG.d y) F + koszulSign i • gIndFun y (DG.d F) := by
  rw [gIndFun_apply, gIndFun_apply, gIndFun_apply]
  apply (zE _).symm.injective
  rw [OPolAlpha.symm_d, AddEquiv.symm_apply_apply, map_add, AddEquiv.symm_apply_apply, Units.smul_def,
    map_zsmul, AddEquiv.symm_apply_apply, gPolyHom_d, indicator_oddStrands, gTwVal_d]
  have hP := parityInv_of_mem (gPolyHom_mem hy)
  set P := gPolyHom y
  set G := gTwVal F
  rw [← smul_mul_assoc, ← hP, EQZab.dZ_apply, dAlpha_apply, dAlpha_apply, EQSkewDifferential.d_mul,
    d_tauAB, sAlpha_zAlpha_eq, map_add (EQZab.tauAB _ _), map_mul (EQZab.tauAB _ _) (parityInv _ G),
    map_zsmul (EQZab.tauAB _ _), EQZab.tauAB_inclY, ← EQZab.parityInv_tauAB, map_mul (parityInv _)]
  rw [show ∀ X Y Z : SkewPolynomial (A + B), X * (Y - Z) = X * Y - X * Z from
    fun X Y Z => by rw [sub_eq_add_neg, mul_add, mul_neg, ← sub_eq_add_neg]]
  simp only [mul_add, add_mul, EQBorel.sp_mul_assoc, mul_smul_comm]
  abel

variable (A B) in
/-- The generator `z` of `Z^{tw}_{a,b}`. -/
def gZabOne : ZabTwG A B := show EQFix.Zab A B from EQFix.Zab.mk 1 (one_mem _)

theorem gTwVal_one : gTwVal (gZabOne A B) = 1 := rfl

theorem g_exists_smul_one (F : ZabTwG A B) : ∃ r : ΛA ᵍ⊗[ℤ] ΛB, r • gZabOne A B = F := by
  have hF : OPol.equiv _ (blockRev A B (gTwVal F)) ∈ osymABDG A B :=
    mem_osymABDG.mpr (by rw [RingEquiv.symm_apply_apply]; exact blockRev_mem _ _ (gTwVal_mem F))
  obtain ⟨r, hr⟩ := tensorToOsymAB_surjective (a := A) (b := B) ⟨_, hF⟩
  refine ⟨r, EQFix.Zab.ext ?_⟩
  change blockRev A B (gRHat r) * 1 = gTwVal F
  have : gRHat r = blockRev A B (gTwVal F) := by
    rw [gRHat, ← coe_tensorToOsymAB, hr]
    rfl
  rw [this, blockRev_blockRev, sp_mul_one']

/-- The inverse of `gIndHom`: `p ↦ (u ⊠ v) ⊗ z` for `p = u(x) v(y)`. -/
def gIndInv : Zn (A + B) →+ TensorProductOver (ΛA ᵍ⊗[ℤ] ΛB) (ZZg A B) (ZabTwG A B) :=
  AddMonoidHom.mk' (fun z => TensorProductOver.tmul _ (gPolyEquiv.symm ((zE _).symm
      (show Zn (A + B) from z))) (gZabOne A B))
    fun z z' => by
      change TensorProductOver.tmul _ (gPolyEquiv.symm ((zE _).symm (z + z'))) _ = _
      rw [map_add, map_add, TensorProductOver.add_tmul]

theorem gIndHom_indInv (z : Zn (A + B)) : gIndHom (gIndInv z) = z := by
  change zE _ (gPolyHom (gPolyEquiv.symm _) * EQZab.tauAB _ _ (gTwVal (gZabOne A B))) = z
  rw [gTwVal_one, map_one, sp_mul_one', ← gPolyEquiv_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

theorem gIndInv_indHom (t : TensorProductOver (ΛA ᵍ⊗[ℤ] ΛB) (ZZg A B) (ZabTwG A B)) :
    gIndInv (gIndHom t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y F =>
    obtain ⟨r, rfl⟩ := g_exists_smul_one F
    rw [← TensorProductOver.op_smul_tmul, gIndHom_tmul, gIndFun_apply, gTwVal_one, map_one,
      sp_mul_one']
    change TensorProductOver.tmul _ (gPolyEquiv.symm ((zE _).symm (zE _ (gPolyHom (op r • y))))) _ = _
    rw [AddEquiv.symm_apply_apply, ← gPolyEquiv_apply, AddEquiv.symm_apply_apply]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

theorem gIndHom_d (t : TensorProductOver (ΛA ᵍ⊗[ℤ] ΛB) (ZZg A B) (ZabTwG A B)) :
    gIndHom (DG.d t) = DG.d (gIndHom t) :=
  TensorProductOver.lift_d gIndFun gIndFun_balanced (fun hy F => gIndFun_d hy F) t

theorem gIndHom_injective : Function.Injective (gIndHom (A := A) (B := B)) :=
  Function.LeftInverse.injective gIndInv_indHom

theorem gIndInv_d (z : Zn (A + B)) : gIndInv (DG.d z) = DG.d (gIndInv z) := by
  apply gIndHom_injective
  rw [gIndHom_indInv, gIndHom_d, gIndHom_indInv]

theorem gIndInv_op_smul (h : osymDG (A + B)) (z : Zn (A + B)) : gIndInv (op h • z) = op h • gIndInv z := by
  apply gIndHom_injective
  rw [gIndHom_indInv, gIndHom_op_smul, gIndHom_indInv]

theorem gIndInv_mem {k : ℤ} {z : Zn (A + B)} (hz : z ∈ DG.grading k) : gIndInv z ∈ DG.grading k := by
  refine mem_grading_of_map_mem (k := 0) gIndHom (fun hm => by rw [add_zero]; exact gIndHom_mem hm)
    (fun t ht => gIndHom_injective (by rw [ht, map_zero])) ?_
  rwa [add_zero, gIndHom_indInv]

end Poly

/-! ### The morphism `ι` and the bimodule isomorphism -/

section Iota

variable {A B : ℕ} {EA EB EN : Type} [Ring EA] [DGAddCommGroup EA] [DGRing EA] [Module EA (Zn A)]
  [DGBimodule EA (osymDG A) (Zn A)] [Ring EB] [DGAddCommGroup EB] [DGRing EB] [Module EB (Zn B)]
  [DGBimodule EB (osymDG B) (Zn B)] [Ring EN] [DGAddCommGroup EN] [DGRing EN] [Module EN (Zn (A + B))]
  [DGBimodule EN (osymDG (A + B)) (Zn (A + B))]

variable (EA EB A B) in
/-- `E_A ⊗ E_B`. -/
abbrev EAB : Type := DGAlgebra.gradingSubmodule ℤ EA ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ EB

variable (A B) in
/-- `(Z_A ⊠ Z_B) ⊗_{OΛ_A ⊗ OΛ_B} Z_{A,B}`. -/
abbrev TZ : Type := TensorProductOver (DGAlgebra.gradingSubmodule ℤ (osymDG A) ᵍ⊗[ℤ]
  DGAlgebra.gradingSubmodule ℤ (osymDG B)) (ZZg A B) (ZabTwG A B)

theorem tz_smul_add (s : EAB EA EB) (t t' : TZ A B) : s • (t + t') = s • t + s • t' := smul_add s t t'
theorem tz_one_smul (t : TZ A B) : (1 : EAB EA EB) • t = t := one_smul _ t
theorem tz_zero_smul (t : TZ A B) : (0 : EAB EA EB) • t = 0 := zero_smul (EAB EA EB) t
theorem tz_smul_zero (s : EAB EA EB) : s • (0 : TZ A B) = 0 := smul_zero s
theorem tz_add_smul (s s' : EAB EA EB) (t : TZ A B) : (s + s') • t = s • t + s' • t := add_smul s s' t
theorem tz_mul_smul (s s' : EAB EA EB) (t : TZ A B) : (s * s') • t = s • s' • t := mul_smul s s' t

theorem smul_op_smul_TZ (s : EAB EA EB) (h : osymDG (A + B)) (t : TZ A B) :
    s • (op h • t) = op h • (s • t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, tz_smul_zero, smul_zero]
  | tmul y F => rfl
  | add t t' ht ht' => rw [smul_add, tz_smul_add, ht, ht', tz_smul_add, smul_add]

variable (EA EB) in
/-- `z ↦ Ψ(s · Ψ⁻¹(z))` on `Z_{A+B}`. -/
def conjMap (s : EAB EA EB) : Zn (A + B) →+ Zn (A + B) :=
  gIndHom.comp ((AddMonoidHom.mk' (fun t : TZ A B => s • t) (fun t t' => tz_smul_add s t t')).comp gIndInv)

theorem conjMap_apply (s : EAB EA EB) (z : Zn (A + B)) : conjMap EA EB s z = gIndHom (s • gIndInv z) := rfl

theorem conjMap_op_smul (s : EAB EA EB) (h : osymDG (A + B)) (z : Zn (A + B)) :
    conjMap EA EB s (op h • z) = op h • conjMap EA EB s z := by
  rw [conjMap_apply, conjMap_apply, gIndInv_op_smul, smul_op_smul_TZ, gIndHom_op_smul]

variable (HN : FullAction EN (osymDG (A + B)) (Zn (A + B)))

variable (EA EB) in
/-- The element of `E_N` acting as `conjMap s`. -/
def iotaFun (s : EAB EA EB) : EN := (HN.full _ (fun h z => conjMap_op_smul s h z)).choose

theorem iotaFun_smul (s : EAB EA EB) (z : Zn (A + B)) : iotaFun EA EB HN s • z = conjMap EA EB s z :=
  (HN.full _ (fun h z => conjMap_op_smul s h z)).choose_spec z

theorem iotaFun_smul_indHom (s : EAB EA EB) (t : TZ A B) :
    iotaFun EA EB HN s • gIndHom t = gIndHom (s • t) := by
  rw [iotaFun_smul, conjMap_apply, gIndInv_indHom]

theorem iotaFun_mem {k : ℤ} {s : EAB EA EB} (hs : s ∈ DG.grading k) : iotaFun EA EB HN s ∈ DG.grading k :=
  HN.mem_grading _ k fun j z hz => by
    rw [iotaFun_smul, conjMap_apply]
    exact gIndHom_mem (DG.smul_mem_grading hs (gIndInv_mem hz))

variable (EA EB) in
/-- **`ι : E_A ⊗ E_B → E_{A+B}`** as a morphism of dg rings: `ι(s)` acts on `Z_{A+B}` as `s` acts on
`(Z_A ⊠ Z_B) ⊗ Z_{A,B}` through `Ψ`. -/
def gIota : EAB EA EB →ᵈᵍ+* EN where
  toFun := iotaFun EA EB HN
  map_one' := HN.ext fun z => by simp only [iotaFun_smul, conjMap_apply, tz_one_smul, gIndHom_indInv, one_smul]
  map_mul' s s' := HN.ext fun z => by
    simp only [iotaFun_smul, conjMap_apply, mul_smul, gIndInv_indHom]
  map_zero' := HN.ext fun z => by simp only [iotaFun_smul, conjMap_apply, tz_zero_smul, map_zero, zero_smul]
  map_add' s s' := HN.ext fun z => by
    simp only [iotaFun_smul, conjMap_apply, add_smul, map_add]
  map_mem' hs := iotaFun_mem HN hs
  map_d' s := by
    induction s using DG.induction_on with
    | h_zero =>
      change iotaFun EA EB HN (DG.d 0) = DG.d (iotaFun EA EB HN 0)
      have h0 : iotaFun EA EB HN 0 = 0 := HN.ext fun z => by
        simp only [iotaFun_smul, conjMap_apply, tz_zero_smul, map_zero, zero_smul]
      rw [d_zero, h0, d_zero]
    | @h_homogeneous k s =>
      apply HN.ext fun z => ?_
      have e1 := DG.d_smul (iotaFun_mem HN s.2) z
      have e2 := DG.d_smul s.2 (gIndInv z)
      change iotaFun EA EB HN (DG.d (s : EAB EA EB)) • z = DG.d (iotaFun EA EB HN s) • z
      rw [eq_sub_of_add_eq e1.symm]
      simp only [iotaFun_smul, conjMap_apply]
      rw [← gIndHom_d, e2, gIndInv_d, map_add, map_units_zsmul]
      abel
    | h_add s s' hs hs' =>
      change iotaFun EA EB HN (DG.d (s + s')) = DG.d (iotaFun EA EB HN (s + s'))
      have hadd : ∀ u v : EAB EA EB, iotaFun EA EB HN (u + v) = iotaFun EA EB HN u + iotaFun EA EB HN v :=
        fun u v => HN.ext fun z => by simp only [iotaFun_smul, conjMap_apply, add_smul, map_add]
      rw [d_add, hadd, hadd, d_add]
      exact congrArg₂ (· + ·) hs hs'

theorem gIota_smul (s : EAB EA EB) (z : Zn (A + B)) : gIota EA EB HN s • z = conjMap EA EB s z :=
  iotaFun_smul HN s z

variable (EA EB A B) in
/-- `ι^* Z_{A+B}`. -/
abbrev IZG : Type := RestrictScalars (gIota EA EB HN) (Zn (A + B))

variable (EA EB) in
/-- **`(Z_A ⊠ Z_B) ⊗_{OΛ_A ⊗ OΛ_B} Z_{A,B} ≅ ι^* Z_{A+B}`** as dg `(E_A ⊗ E_B, OΛ_{A+B})`-bimodules, in every
rank. -/
def gIndEquiv : TZ A B ≃ᵈᵍ[EAB EA EB] IZG A B EA EB HN where
  toFun := gIndHom
  invFun := gIndInv
  left_inv := gIndInv_indHom
  right_inv := gIndHom_indInv
  map_add' := map_add _
  map_smul' s t := (iotaFun_smul_indHom HN s t).symm
  map_mem' := gIndHom_mem
  map_d' := gIndHom_d

theorem gIndEquiv_op_smul (h : osymDG (A + B)) (t : TZ A B) :
    gIndEquiv EA EB HN (op h • t) = op h • gIndEquiv EA EB HN t :=
  gIndHom_op_smul h t

end Iota

end OddMath.Frontier.EQLift
