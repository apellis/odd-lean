import OddMath.Frontier.EQInductionPoly
import OddMath.Frontier.EQFunctorEmbeddingTensor
import OddMath.Frontier.EQOnhTensor
import OddMath.Frontier.EQFunctorDual
import OddMath.Frontier.EQThickSlider
import OddMath.Frontier.EQThickBlocks
import OddMath.Frontier.EQOPolTensor

/-!
# `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z_{a,b} ≅ ι^* Z_{a+b}`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3 (Definition 4.6) and §4.4 (the induction half of Corollary 4.21); ranks `a + 2`, `b + 2`.

`ι = ONH.iota a b : ONH_{a+2} ⊗ ONH_{b+2} → ONH_{a+b+4}` makes `Z_{a+b+4}` a dg
`(ONH_{a+2} ⊗ ONH_{b+2}, OΛ_{a+b+4})`-bimodule `ι^* Z` (`EQFunctor.IZ`). The bimodule
`(Z_{a+2} ⊠ Z_{b+2}) ⊗_{OΛ_{a+2} ⊗ OΛ_{b+2}} Z_{a+2,b+2}` has the same underlying differential:
moving `{a} e_1(y) ∈ OΛ_a ⊗ OΛ_b` across the tensor product turns it into
`(θ ∘ w₀)(e_1)(y) = Σ_j (-1)^{j-1} y_j`, and `s_{α_b}(y) + {a} θ_b(e_1)(y)` is exactly the `y`-part of
`s_{α_{a+b}}` (`sAlpha_zAlpha_eq`); no sign or automorphism on the variables `y` is needed for
`d`. The right actions of `OΛ_{a+b}` match only after the left action of `OΛ_a ⊗ OΛ_b` on `Z_{a,b}`
is twisted by the block reversal `w₀ × w₀` (`blockRev`):

* `toPoly : Z_a ⊠ Z_b → Z_{a+b}`, `u 1_z ⊠ v 1_z ↦ u(x) v(y) 1_z`: an isomorphism of dg left
  `ONH_a ⊗ ONH_b`-modules (`toPoly_smul`, `toPoly_d`, `toPoly_bijective`), turning the right action
  of `f ⊗ g ∈ OΛ_a ⊗ OΛ_b` into right multiplication by `(θ ∘ w₀)(f)(x) (θ ∘ w₀)(g)(y)`
  (`toPoly_op_smul`);
* `ZabTw a b`: the dg `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule `Z_{a,b}` of Definition 4.6 with the left
  action restricted along `w₀ × w₀` (`OΛ_a ⊗ OΛ_b ∋ g` acts by `(w₀ × w₀)(g)`);
* **`indEquiv a b : (Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^{tw}_{a,b} ≅ ι^* Z_{a+b}`**, `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)`,
  an isomorphism of dg `(ONH_a ⊗ ONH_b, OΛ_{a+b})`-bimodules (`indEquiv_op_smul`);
* `no_indEquiv_untwisted`: for the untwisted left action of Definition 4.6 (multiplication in
  `OΛ_a ⊠ OΛ_b`, `EQFunctor.Zab.instDGBimodule`) and `a = b = 2`, there is **no** isomorphism of dg
  `(ONH_2 ⊗ ONH_2, OΛ_4)`-bimodules `(Z_2 ⊠ Z_2) ⊗ Z_{2,2} ≅ ι^* Z_4`.

In Ellis–Qi's twisted model `Z_{a,b} = OΛ̃_a ⊠ OΛ̃_b · z` (identified with the model here by
`θ_a ⊗ θ_b`), the twisted left action is the action of `OΛ_a ⊗ OΛ_b` through `θ ∘ w₀` on each tensor
factor, the same map through which `OΛ_n` acts on `Z_n` on the right.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY osymAB)
open OddMath.Frontier.EQOnhDG (ONH)
open DG MulOpposite TensorProductOver.RightAction

/-! ### Restriction of the left action of a dg bimodule -/

section Restrict

variable {A B C : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B] [Ring C]
  [DGAddCommGroup C] (φ : A →ᵈᵍ+* B) (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module B M]
  [Module Cᵐᵒᵖ M]

instance restrictModuleOp : Module Cᵐᵒᵖ (RestrictScalars φ M) := inferInstanceAs (Module Cᵐᵒᵖ M)

instance restrictDGRightModule [DGRightModule C M] : DGRightModule C (RestrictScalars φ M) :=
  inferInstanceAs (DGRightModule C M)

instance restrictSMulCommClass [SMulCommClass B Cᵐᵒᵖ M] :
    SMulCommClass A Cᵐᵒᵖ (RestrictScalars φ M) where
  smul_comm a c m := smul_comm (φ a) c (show M from m)

/-- Restricting the left action of a dg `(B, C)`-bimodule along `φ : A →ᵈᵍ+* B`. -/
instance restrictDGBimodule [DGBimodule B C M] : DGBimodule A C (RestrictScalars φ M) :=
  DGBimodule.mk'

end Restrict

variable (a b : ℕ)

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

/-! ### The windows acting on `u(x) v(y)` -/

section Window

open NilHeckeAction OnhWindow

variable {a b}

theorem le_x : 0 + (a + 2) ≤ (a + 2 + b) + 2 := by omega
theorem le_y : (a + 2) + (b + 2) ≤ (a + 2 + b) + 2 := by omega

theorem inclX_eq_place (f : SkewPolynomial (a + 2)) :
    inclX (a + 2) (b + 2) f = ProjectorRank.place 0 le_x f := by
  have e : (inclX (a + 2) (b + 2)).comp (RingHom.id _) = ProjectorRank.place 0 (le_x (b := b)) :=
    ringHom_ext fun j => by
      rw [RingHom.comp_apply, RingHom.id_apply, EQZab.inclX_generator]
      refine Eq.trans ?_ (ProjectorRank.place_generator _ _ j).symm
      exact congrArg generator (Fin.ext (by simp))
  exact RingHom.congr_fun e f

theorem inclY_eq_place (f : SkewPolynomial (b + 2)) :
    inclY (a + 2) (b + 2) f = ProjectorRank.place (a + 2) le_y f := by
  have e : (inclY (a + 2) (b + 2)).comp (RingHom.id _) =
      ProjectorRank.place (a + 2) (le_y (a := a) (b := b)) :=
    ringHom_ext fun j => by
      rw [RingHom.comp_apply, RingHom.id_apply, EQZab.inclY_generator]
      refine Eq.trans ?_ (ProjectorRank.place_generator _ _ j).symm
      exact congrArg generator (Fin.ext (by simp; omega))
  exact RingHom.congr_fun e f

/-- The window `[0, a + 2)` acts on `u(x) v(y)` through `u`. -/
theorem action_windowX (p : NilHeckeAction.Presented a) (u : SkewPolynomial (a + 2))
    (v : SkewPolynomial (b + 2)) :
    action (a + 2 + b) (windowHom a (a + 2 + b) 0 le_x p)
        (inclX (a + 2) (b + 2) u * inclY (a + 2) (b + 2) v) =
      inclX (a + 2) (b + 2) (action a p u) * inclY (a + 2) (b + 2) v := by
  rw [inclX_eq_place, inclY_eq_place, inclX_eq_place,
    EQThick.action_windowHom_mul_kernel le_x p _ _ fun i =>
      EQThick.divided_place_eq_zero le_y _ (Or.inl (by simp; omega)) v,
    EQThick.action_windowHom_place]

/-- The window `[a + 2, a + b + 4)` acts on `v(y) u(x)` through `v`. -/
theorem action_windowY (q : NilHeckeAction.Presented b) (u : SkewPolynomial (a + 2))
    (v : SkewPolynomial (b + 2)) :
    action (a + 2 + b) (windowHom b (a + 2 + b) (a + 2) le_y q)
        (inclY (a + 2) (b + 2) v * inclX (a + 2) (b + 2) u) =
      inclY (a + 2) (b + 2) (action b q v) * inclX (a + 2) (b + 2) u := by
  rw [inclX_eq_place, inclY_eq_place, inclY_eq_place,
    EQThick.action_windowHom_mul_kernel le_y q _ _ fun i =>
      EQThick.divided_place_eq_zero le_x _ (Or.inr (by simp)) u,
    EQThick.action_windowHom_place]

end Window

/-! ### `Z_a ⊠ Z_b` as polynomials in `x`, `y` -/

/-- `Z_N` with its underlying skew polynomials. -/
abbrev zE (N : ℕ) : SkewPolynomial N ≃+ Zn N := OPolAlpha.equiv N (oddStrands N)

theorem zE_symm_gradeInvolution {N : ℕ} (z : Zn N) :
    (zE N).symm (gradeInvolution (Zn N) z) = parityInv N ((zE N).symm z) := by
  induction z using DG.induction_on with
  | h_zero => rw [map_zero, map_zero, map_zero]
  | @h_homogeneous k z =>
    rw [gradeInvolution_of_mem z.2, parityInv_of_mem (OPolAlpha.mem_grading_iff.mp z.2),
      Units.smul_def, map_zsmul]
  | h_add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

variable {a b}

/-- `u 1_z ⊠ v 1_z ↦ u(x) v(y)`. -/
def polyHom : ZZ a b →+ SkewPolynomial ((a + 2) + (b + 2)) :=
  (OPol.equiv _).symm.toAddMonoidHom.comp (opolMul (a + 2) (b + 2)).toAddMonoidHom

theorem polyHom_tmul (u : Zn (a + 2)) (v : Zn (b + 2)) :
    polyHom (u ⊗ₜ[ℤ] v) = inclX (a + 2) (b + 2) ((zE _).symm u) * inclY (a + 2) (b + 2) ((zE _).symm v) :=
  rfl

theorem polyHom_mem {k : ℤ} {y : ZZ a b} (hy : y ∈ DG.grading k) :
    polyHom y ∈ grading ((a + 2) + (b + 2)) k := by
  have key : ∀ {i j : ℤ} {u : Zn (a + 2)} {v : Zn (b + 2)}, u ∈ DG.grading i →
      v ∈ DG.grading j → zE _ (polyHom (u ⊗ₜ[ℤ] v)) ∈ DG.grading (i + j) := fun hu hv =>
    OPolAlpha.mem_grading_iff.mpr (by
      rw [AddEquiv.symm_apply_apply, polyHom_tmul]
      exact mul_mem_grading' (inclX_mem_grading (OPolAlpha.mem_grading_iff.mp hu))
        (inclY_mem_grading (OPolAlpha.mem_grading_iff.mp hv)))
  have := DG.map_mem_grading_of_tmul ((zE _).toAddMonoidHom.comp polyHom) 0
    (fun hu hv => by simpa using key hu hv) hy
  simpa using OPolAlpha.mem_grading_iff.mp this

theorem inclX_mul_inclY_of_mem_one {u : SkewPolynomial (a + 2)} (hu : u ∈ grading (a + 2) 1)
    (g : SkewPolynomial (b + 2)) :
    inclX (a + 2) (b + 2) u * inclY (a + 2) (b + 2) g =
      inclY (a + 2) (b + 2) (parityInv (b + 2) g) * inclX (a + 2) (b + 2) u := by
  rw [inclY_mul_inclX_pow_parityInv hu, show (1 : ℤ).natAbs = 1 from rfl, pow_one,
    parityInv_parityInv]

theorem sAlpha_zAB :
    sAlpha (zAB (a + 2) (b + 2)) =
      inclX (a + 2) (b + 2) (sAlpha (zAlpha (a + 2))) + inclY (a + 2) (b + 2) (sAlpha (zAlpha (b + 2))) := by
  rw [sAlpha, Fin.sum_univ_add, sAlpha, sAlpha, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [zAB, zAlpha, i.isLt]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zAB, zAlpha, Fin.val_natAdd, map_zsmul, EQZab.inclY_generator]
    simp only [show ¬(a + 2 + j.val < a + 2) by omega, ↓reduceIte,
      show a + 2 + j.val - (a + 2) = j.val by omega]

/-- `d(u ⊠ v) ↦ d_β(u(x) v(y))`, `β = (0,1,0,1,…) ⊔ (0,1,0,1,…)`. -/
theorem polyHom_d (y : ZZ a b) :
    polyHom (DG.d y) = dAlpha (zAB (a + 2) (b + 2)) (polyHom y) := by
  induction y using TensorProduct.inductionOn with
  | tmul u v =>
    rw [DG.d_tmul, map_add, polyHom_tmul, polyHom_tmul, polyHom_tmul, OPolAlpha.symm_d,
      OPolAlpha.symm_d, zE_symm_gradeInvolution, indicator_oddStrands, indicator_oddStrands,
      dAlpha_apply, dAlpha_apply, dAlpha_apply, EQSkewDifferential.d_mul, map_add, map_add, map_mul, map_mul,
      EQZab.d_inclX, EQZab.d_inclY, map_mul, EQZab.parityInv_inclX, EQZab.parityInv_inclY,
      sAlpha_zAB]
    set u' := (zE (a + 2)).symm u
    set v' := (zE (b + 2)).symm v
    have hc := inclX_mul_inclY_of_mem_one (b := b) (sAlpha_mem_grading (zAlpha (a + 2))) v'
    simp only [add_mul, mul_add]
    rw [EQBorel.sp_mul_assoc, hc, ← EQBorel.sp_mul_assoc, ← EQBorel.sp_mul_assoc]
    abel
  | add y y' hy hy' => rw [DG.d_add, map_add, map_add, hy, hy', map_add]

/-- The skew polynomial `f(x) g(y)` of `f ⊗ g ∈ OΛ_a ⊗ OΛ_b`. -/
def rHat (r : Λa ᵍ⊗[ℤ] Λb) : SkewPolynomial ((a + 2) + (b + 2)) :=
  (OPol.equiv _).symm (tensorToOPol (a + 2) (b + 2) r)

theorem rHat_add (r r' : Λa ᵍ⊗[ℤ] Λb) : rHat (r + r') = rHat r + rHat r' := by
  rw [rHat, map_add, map_add]
  rfl

theorem rHat_tmul (f : osymDG (a + 2)) (g : osymDG (b + 2)) :
    rHat (f ᵍ⊗ₜ[ℤ] g) = inclX (a + 2) (b + 2) ((OPol.equiv _).symm f) *
      inclY (a + 2) (b + 2) ((OPol.equiv _).symm g) := by
  rw [rHat, tensorToOPol_tmul]
  rfl

theorem twistRev_mem_grading {N : ℕ} {k : ℤ} {f : SkewPolynomial N} (hf : f ∈ grading N k) :
    twistRev N f ∈ grading N k :=
  ringHom_mem_grading _ (fun j => by
    rw [twistRev_generator]; exact AddSubgroup.zsmul_mem _ (generator_mem_grading _) _) hf

theorem ks_aux (j k l : ℤ) : koszulSign (l * k) * koszulSign ((j + l) * k) = koszulSign (j * k) := by
  rw [← koszulSign_add, show l * k + (j + l) * k = j * k + 2 * (l * k) by ring, koszulSign_add,
    koszulSign_even (even_two_mul _), mul_one]

/-- The right action of `f ⊗ g ∈ OΛ_a ⊗ OΛ_b` on `Z_a ⊠ Z_b` is right multiplication by
`(θ ∘ w₀)(f)(x) (θ ∘ w₀)(g)(y) = (θ_a ⊗ θ_b)((w₀ × w₀)(f(x) g(y)))`. -/
theorem polyHom_op_smul (r : Λa ᵍ⊗[ℤ] Λb) (y : ZZ a b) :
    polyHom (op r • y) = polyHom y * EQZab.tauAB (a + 2) (b + 2) (blockRev (a + 2) (b + 2) (rHat r)) := by
  induction r using GradedTensorProduct.induction_on_tmul with
  | zero => rw [ExternalTensor.zero_op_smul', map_zero, rHat, map_zero, map_zero, map_zero,
      map_zero, EQBorel.sp_mul_zero]
  | @tmul i j f hf g hg =>
    induction y using DG.tensor_induction_on with
    | zero => rw [smul_zero, map_zero, EQBorel.sp_zero_mul]
    | @tmul k l u v =>
      rw [ExternalTensor.tmul_op_smul_tmul hf g (u : Zn (a + 2)) v.2, map_units_zsmul, polyHom_tmul,
        polyHom_tmul, rHat_tmul, map_mul, map_mul, blockRev_inclX, blockRev_inclY, EQZab.tauAB_inclX,
        EQZab.tauAB_inclY]
      have hf' : twistRev (a + 2) ((OPol.equiv _).symm (f : OPol (a + 2))) ∈ grading (a + 2) i :=
        twistRev_mem_grading (OPol.equiv_mem_grading_iff.mp ((DGSubring.mem_grading_iff _).mp hf))
      have hv : (zE (b + 2)).symm (v : Zn (b + 2)) ∈ grading (b + 2) l :=
        OPolAlpha.mem_grading_iff.mp v.2
      have hc := inclY_mul_inclX_of_mem (a := a + 2) (b := b + 2) hf' hv
      change (koszulSign (i * l)) • (inclX (a + 2) (b + 2) ((zE _).symm (u : Zn (a + 2)) *
          twistRev (a + 2) ((OPol.equiv _).symm (f : OPol (a + 2)))) *
        inclY (a + 2) (b + 2) ((zE _).symm (v : Zn (b + 2)) *
          twistRev (b + 2) ((OPol.equiv _).symm (g : OPol (b + 2))))) = _
      rw [show ∀ F, theta (a + 2) (longestPerm (a + 2) F) = twistRev (a + 2) F from fun _ => rfl,
        show ∀ F, theta (b + 2) (longestPerm (b + 2) F) = twistRev (b + 2) F from fun _ => rfl,
        map_mul, map_mul]
      set X := inclX (a + 2) (b + 2) ((zE _).symm (u : Zn (a + 2)))
      set Fx := inclX (a + 2) (b + 2) (twistRev (a + 2) ((OPol.equiv _).symm (f : OPol (a + 2))))
      set Y := inclY (a + 2) (b + 2) ((zE _).symm (v : Zn (b + 2)))
      set Gy := inclY (a + 2) (b + 2) (twistRev (b + 2) ((OPol.equiv _).symm (g : OPol (b + 2))))
      have hc' : Fx * Y = (koszulSign (l * i) : ℤ) • (Y * Fx) := by
        rw [hc, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
      rw [Units.smul_def, EQBorel.sp_mul_assoc X Fx, ← EQBorel.sp_mul_assoc Fx Y Gy, hc',
        smul_mul_assoc, mul_smul_comm, smul_smul, ← Units.val_mul, mul_comm i l, Int.units_mul_self,
        Units.val_one, one_smul, EQBorel.sp_mul_assoc Y Fx Gy, ← EQBorel.sp_mul_assoc X Y]
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, add_mul]
  | add r r' hr hr' =>
    rw [ExternalTensor.add_op_smul', map_add, hr, hr', rHat_add, map_add, map_add, mul_add]

theorem zE_symm_onh_smul (p : ONH (a + 2 + b)) (z : Zn ((a + 2) + (b + 2))) :
    (zE ((a + 2) + (b + 2))).symm (p • z) =
      NilHeckeAction.action (a + 2 + b) ((ONH.equiv _).symm p) ((zE ((a + 2) + (b + 2))).symm z) :=
  ONH.symm_smul p z

/-- `ι(1 ⊗ g)` acting on `u(x) v(y)`, for `g ∈ ONH_b` of degree `j` and `u` of degree `k`. -/
theorem zE_symm_iotaR_smul {j k : ℤ} (g : ONH b) (hg : g ∈ DG.grading j) {u : Zn (a + 2)}
    (hu : u ∈ DG.grading k) (v : Zn (b + 2)) :
    (zE _).symm (ONH.iotaR a b g • zE ((a + 2) + (b + 2))
        (inclX (a + 2) (b + 2) ((zE _).symm u) * inclY (a + 2) (b + 2) ((zE _).symm v))) =
      (koszulSign (j * k) : ℤ) •
        (inclX (a + 2) (b + 2) ((zE _).symm u) * inclY (a + 2) (b + 2) ((zE _).symm (g • v))) := by
  induction v using DG.induction_on with
  | h_zero => simp only [map_zero, EQBorel.sp_mul_zero, smul_zero]
  | @h_homogeneous l v =>
    have hu' : (zE _).symm u ∈ grading (a + 2) k := OPolAlpha.mem_grading_iff.mp hu
    have hv' : (zE _).symm (v : Zn (b + 2)) ∈ grading (b + 2) l := OPolAlpha.mem_grading_iff.mp v.2
    have hgv : (zE _).symm (g • (v : Zn (b + 2))) ∈ grading (b + 2) (j + l) :=
      OPolAlpha.mem_grading_iff.mp (DG.smul_mem_grading hg v.2)
    have h1 := inclY_mul_inclX_of_mem (a := a + 2) (b := b + 2) hu' hv'
    have h2 := inclY_mul_inclX_of_mem (a := a + 2) (b := b + 2) hu' hgv
    have h1' : inclX (a + 2) (b + 2) ((zE _).symm u) * inclY (a + 2) (b + 2) ((zE _).symm (v : Zn (b + 2))) =
        (koszulSign (l * k) : ℤ) • (inclY (a + 2) (b + 2) ((zE _).symm (v : Zn (b + 2))) *
          inclX (a + 2) (b + 2) ((zE _).symm u)) := by
      rw [h1, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
    rw [zE_symm_onh_smul, AddEquiv.symm_apply_apply, h1', map_zsmul]
    change (koszulSign (l * k) : ℤ) • NilHeckeAction.action (a + 2 + b)
        (OnhWindow.windowHom b (a + 2 + b) (a + 2) le_y ((ONH.equiv b).symm g)) _ = _
    rw [action_windowY, ← ONH.symm_smul, h2, smul_smul, ← Units.val_mul, ks_aux]
  | h_add v v' hv hv' =>
    rw [map_add, map_add, mul_add, map_add, smul_add, map_add, hv, hv', smul_add, map_add, map_add,
      mul_add, smul_add]

/-- `ι(f ⊗ 1)` acting on `u(x) v(y)`. -/
theorem zE_symm_iotaL_smul (f : ONH a) (u : Zn (a + 2)) (v : Zn (b + 2)) :
    (zE _).symm (ONH.iotaL a b f • zE ((a + 2) + (b + 2))
        (inclX (a + 2) (b + 2) ((zE _).symm u) * inclY (a + 2) (b + 2) ((zE _).symm v))) =
      inclX (a + 2) (b + 2) ((zE _).symm (f • u)) * inclY (a + 2) (b + 2) ((zE _).symm v) := by
  rw [zE_symm_onh_smul, AddEquiv.symm_apply_apply]
  change NilHeckeAction.action (a + 2 + b) (OnhWindow.windowHom a (a + 2 + b) 0 le_x ((ONH.equiv a).symm f)) _ = _
  rw [action_windowX, ← ONH.symm_smul]

/-- **`Z_a ⊠ Z_b → ι^* Z_{a+b}` is left `ONH_a ⊗ ONH_b`-linear.** -/
theorem zE_polyHom_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (y : ZZ a b) :
    zE ((a + 2) + (b + 2)) (polyHom (s • y)) = ONH.iota a b s • zE ((a + 2) + (b + 2)) (polyHom y) := by
  induction s using GradedTensorProduct.induction_on_tmul with
  | zero => rw [ExternalTensor.zero_smul', map_zero, map_zero, map_zero, zero_smul]
  | @tmul i j f hf g hg =>
    induction y using DG.tensor_induction_on with
    | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
    | @tmul k l u v =>
      apply (zE _).symm.injective
      have hR := (AddEquiv.symm_apply_eq _).mp (zE_symm_iotaR_smul g hg u.2 (v : Zn (b + 2)))
      rw [ExternalTensor.tmul_smul_tmul f hg u.2 (v : Zn (b + 2)), map_units_zsmul,
        AddEquiv.symm_apply_apply, polyHom_tmul, polyHom_tmul, ONH.iota_tmul, mul_smul, hR,
        map_zsmul, smul_comm (ONH.iotaL a b f) ((koszulSign (j * k) : ℤ)), map_zsmul,
        zE_symm_iotaL_smul, Units.smul_def]
    | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', map_add, map_add, smul_add]
  | add s s' hs hs' => rw [ExternalTensor.add_smul', map_add, map_add, hs, hs', map_add, add_smul]

theorem opolTensorDG_eq_opolMul (A B : ℕ)
    (z : DGAlgebra.gradingSubmodule ℤ (OPol A) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol B)) :
    opolTensorDG A B z = opolMul A B ((GradedTensorProduct.of ℤ (DGAlgebra.gradingSubmodule ℤ (OPol A))
      (DGAlgebra.gradingSubmodule ℤ (OPol B))).symm z) := by
  induction z using GradedTensorProduct.induction_on_tmul with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul _ _ =>
    rw [opolTensorDG_apply, opolTensorAlgHom_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

theorem polyHom_bijective : Function.Bijective (polyHom (a := a) (b := b)) := by
  refine ⟨(OPol.equiv _).symm.injective.comp (opolMul_injective (a := a + 2) (b := b + 2)), fun F => ?_⟩
  obtain ⟨z, hz⟩ := opolTensorDG_surjective (a := a + 2) (b := b + 2) (OPol.equiv _ F)
  rw [opolTensorDG_eq_opolMul] at hz
  exact ⟨_, (congrArg (OPol.equiv _).symm hz).trans (RingEquiv.symm_apply_apply _ F)⟩

/-- `Z_a ⊠ Z_b ≅ OPol_{a+b}` as abelian groups. -/
def polyEquiv : ZZ a b ≃+ SkewPolynomial ((a + 2) + (b + 2)) :=
  AddEquiv.ofBijective polyHom polyHom_bijective

theorem polyEquiv_apply (y : ZZ a b) : polyEquiv y = polyHom y := rfl

/-! ### The block reversal on `OΛ_a ⊗ OΛ_b` -/

variable (a b) in
theorem parityInv_blockRev (f : SkewPolynomial (a + b)) :
    parityInv (a + b) (blockRev a b f) = blockRev a b (parityInv (a + b) f) := by
  have h : (parityInv (a + b)).comp (blockRev a b) = (blockRev a b).comp (parityInv (a + b)) :=
    ringHom_ext fun j => by simp [blockRev_generator]
  exact RingHom.congr_fun h f

variable (a b) in
theorem d_blockRev (f : SkewPolynomial (a + b)) :
    d (a + b) (blockRev a b f) = blockRev a b (d (a + b) f) := by
  let D : SkewPolynomial (a + b) →+ SkewPolynomial (a + b) :=
    (d (a + b)).comp (blockRev a b).toAddMonoidHom
  let E : SkewPolynomial (a + b) →+ SkewPolynomial (a + b) :=
    (blockRev a b).toAddMonoidHom.comp (d (a + b))
  exact EQZab.deriv_ext (D := D) (E := E) ((parityInv (a + b)).comp (blockRev a b)) (blockRev a b)
    (fun f g => by simp [D, EQSkewDifferential.d_mul])
    (fun f g => by simp [E, EQSkewDifferential.d_mul, parityInv_blockRev])
    (fun j => by simp [D, E, blockRev_generator]) f

variable (a b) in
theorem blockRev_blockRev (f : SkewPolynomial (a + b)) : blockRev a b (blockRev a b f) = f := by
  have h : (blockRev a b).comp (blockRev a b) = RingHom.id _ :=
    ringHom_ext fun j => by
      rw [RingHom.comp_apply, blockRev_generator, blockRev_generator, RingHom.id_apply]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [blockRevPerm_castAdd, blockRevPerm_castAdd, Fin.rev_rev]
      · rw [blockRevPerm_natAdd, blockRevPerm_natAdd, Fin.rev_rev]
  exact RingHom.congr_fun h f

variable (a b) in
theorem blockRev_mem {f : SkewPolynomial (a + b)} (hf : f ∈ osymAB a b) : blockRev a b f ∈ osymAB a b := by
  refine EQZab.osymAB_induction (P := fun f => blockRev a b f ∈ osymAB a b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf
  · intro k
    rw [blockRev_inclX]
    exact EQZab.inclX_mem (EQZab.longestPerm_mem_osym (EQZab.elementary_mem a k))
  · intro k
    rw [blockRev_inclY]
    exact EQZab.inclY_mem (EQZab.longestPerm_mem_osym (EQZab.elementary_mem b k))
  · rw [map_zero]; exact zero_mem _
  · rw [map_one]; exact one_mem _
  · intro f g hf hg; rw [map_add]; exact add_mem hf hg
  · intro f hf; rw [map_neg]; exact neg_mem hf
  · intro f g hf hg; rw [map_mul]; exact mul_mem hf hg

variable (a b) in
theorem blockRev_mem_grading {k : ℤ} {f : SkewPolynomial (a + b)} (hf : f ∈ grading (a + b) k) :
    blockRev a b f ∈ grading (a + b) k :=
  ringHom_mem_grading _ (fun j => by rw [blockRev_generator]; exact generator_mem_grading _) hf

variable (a b) in
/-- `w₀ × w₀` as a ring endomorphism of `OΛ_{a,b}`. -/
def blockRevRing : osymABDG a b →+* osymABDG a b where
  toFun g := ⟨OPol.equiv _ (blockRev a b ((OPol.equiv _).symm g)), mem_osymABDG.mpr (by
    rw [RingEquiv.symm_apply_apply]; exact blockRev_mem a b (mem_osymABDG.mp g.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' g g' := Subtype.ext (by simp)

variable (a b) in
/-- **`w₀ × w₀ : OΛ_{a,b} → OΛ_{a,b}`** as a morphism of dg rings (the plain permutation reversing
each block of variables). -/
def blockRevDG : osymABDG a b →ᵈᵍ+* osymABDG a b where
  __ := blockRevRing a b
  map_mem' {k g} hg := (DGSubring.mem_grading_iff _).mpr (OPol.equiv_mem_grading_iff.mpr
    (blockRev_mem_grading a b (OPol.equiv_mem_grading_iff.mp ((DGSubring.mem_grading_iff _).mp hg))))
  map_d' g := Subtype.ext (by
    change OPol.equiv _ (blockRev a b ((OPol.equiv _).symm (DG.d (g : OPol (a + b))))) =
      DG.d (OPol.equiv _ (blockRev a b ((OPol.equiv _).symm (g : OPol (a + b)))))
    rw [OPol.symm_d, ← d_blockRev]
    rfl)

theorem blockRevDG_val (g : osymABDG a b) :
    (OPol.equiv _).symm ((blockRevDG a b g : osymABDG a b) : OPol (a + b)) =
      blockRev a b ((OPol.equiv _).symm (g : OPol (a + b))) := rfl

/-! ### The bimodules -/

variable (a b) in
/-- `OΛ_a ⊗ OΛ_b → OΛ_{a,b}`, `f ⊗ g ↦ (w₀ f)(x) (w₀ g)(y)`. -/
def rhoTw : (Λa ᵍ⊗[ℤ] Λb) →ᵈᵍ+* osymABDG (a + 2) (b + 2) :=
  (blockRevDG (a + 2) (b + 2)).comp (tensorToOsymAB (a + 2) (b + 2))

variable (a b) in
/-- **`Z^{tw}_{a,b}`**: the dg `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule `Z_{a,b}` of Definition 4.6
(`EQFix.Zab`, `OΛ_a ⊠ OΛ_b · z` with `d z = {a} e_1(y) z` and `z · h = φ(h) z`), with
`f ⊗ g ∈ OΛ_a ⊗ OΛ_b` acting on the left by `(w₀ f)(x) (w₀ g)(y)`. -/
abbrev ZabTw : Type := RestrictScalars (rhoTw a b) (EQFix.Zab (a + 2) (b + 2))

variable (a b) in
/-- **`ι^* Z_{a+b}`**: `Z_{a+b+4}` as a dg `(ONH_{a+2} ⊗ ONH_{b+2}, OΛ_{a+b+4})`-bimodule through
`ι = ONH.iota a b`. -/
abbrev IZ : Type := RestrictScalars (ONH.iota a b) (Zn ((a + 2) + (b + 2)))

/-- The underlying skew polynomial of an element of `Z^{tw}_{a,b}`. -/
def twVal (F : ZabTw a b) : SkewPolynomial ((a + 2) + (b + 2)) :=
  EQFix.Zab.val (show EQFix.Zab (a + 2) (b + 2) from F)

theorem twVal_add (F F' : ZabTw a b) : twVal (F + F') = twVal F + twVal F' := rfl

theorem twVal_mem (F : ZabTw a b) : twVal F ∈ osymAB (a + 2) (b + 2) := EQFix.Zab.mem _

theorem val_rhoTw_smul (r : Λa ᵍ⊗[ℤ] Λb) (F : ZabTw a b) :
    twVal (r • F) = blockRev (a + 2) (b + 2) (rHat r) * twVal F :=
  rfl

theorem twVal_op_smul (h : osymDG ((a + 2) + (b + 2))) (F : ZabTw a b) :
    twVal (op h • F) = twVal F * EQZab.phiAB _ _ (EQFix.toSkew h) := rfl

theorem twVal_d (F : ZabTw a b) : twVal (DG.d F) = EQZab.dZ _ _ (twVal F) := rfl

theorem twVal_mem_grading {k : ℤ} {F : ZabTw a b} (hF : F ∈ DG.grading k) :
    twVal F ∈ grading ((a + 2) + (b + 2)) k :=
  EQFix.Zab.mem_grading_iff.mp hF

/-! ### The window actions are right linear over `OΛ̃_a ⊠ OΛ̃_b` -/

theorem castHom_self {m : ℕ} (h : m = m) (f : SkewPolynomial m) : EQZab.castHom h f = f := by
  have e : EQZab.castHom h = RingHom.id _ := ringHom_ext fun j => by
    rw [EQZab.castHom_generator, RingHom.id_apply]
    rfl
  rw [e, RingHom.id_apply]

/-- `(θ_a ⊗ θ_b)(F)`, `F ∈ OΛ_a ⊠ OΛ_b`, is killed by the crossings inside the two blocks. -/
theorem blockSym_tauAB {F : SkewPolynomial ((a + 2) + (b + 2))} (hF : F ∈ osymAB (a + 2) (b + 2)) :
    EQZab.BlockSym (a + 2 + b) (a + 2) (EQZab.tauAB (a + 2) (b + 2) F) := by
  have h := EQZab.blockSym_tau (n := a + 2 + b) (show (a + 2) + (b + 2) = (a + 2 + b) + 2 by omega) hF
  have key : ∀ (h' : (a + 2) + (b + 2) = (a + 2 + b) + 2) (G : SkewPolynomial ((a + 2) + (b + 2))),
      EQZab.castHom h' G = G := fun h' G => castHom_self h' G
  rwa [key] at h

theorem zE_symm_iota_smul_mul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (P q : SkewPolynomial ((a + 2) + (b + 2)))
    (hq : EQZab.BlockSym (a + 2 + b) (a + 2) q) :
    (zE _).symm (ONH.iota a b s • zE ((a + 2) + (b + 2)) (P * q)) =
      (zE _).symm (ONH.iota a b s • zE ((a + 2) + (b + 2)) P) * q := by
  have hL : ∀ (f : ONH a) (P : SkewPolynomial ((a + 2) + (b + 2))),
      (zE ((a + 2) + (b + 2))).symm (ONH.iotaL a b f • (zE ((a + 2) + (b + 2)) (P * q) : Zn ((a + 2) + (b + 2)))) =
        (zE ((a + 2) + (b + 2))).symm (ONH.iotaL a b f • (zE ((a + 2) + (b + 2)) P : Zn ((a + 2) + (b + 2)))) * q :=
      fun f P => by
    rw [zE_symm_onh_smul, zE_symm_onh_smul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    exact EQThick.action_windowHom_mul_kernel le_x _ P q fun i => hq _ (Or.inl (by simp; omega))
  have hR : ∀ (g : ONH b) (P : SkewPolynomial ((a + 2) + (b + 2))),
      (zE ((a + 2) + (b + 2))).symm (ONH.iotaR a b g • (zE ((a + 2) + (b + 2)) (P * q) : Zn ((a + 2) + (b + 2)))) =
        (zE ((a + 2) + (b + 2))).symm (ONH.iotaR a b g • (zE ((a + 2) + (b + 2)) P : Zn ((a + 2) + (b + 2)))) * q :=
      fun g P => by
    rw [zE_symm_onh_smul, zE_symm_onh_smul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    exact EQThick.action_windowHom_mul_kernel le_y _ P q fun i => hq _ (Or.inr (by simp))
  induction s using GradedTensorProduct.induction_on_tmul with
  | zero => rw [map_zero, zero_smul, zero_smul, map_zero, EQBorel.sp_zero_mul]
  | @tmul i j f hf g hg =>
    have hR' := (AddEquiv.symm_apply_eq _).mp (hR g P)
    rw [ONH.iota_tmul, mul_smul, mul_smul, hR', hL, AddEquiv.apply_symm_apply]
  | add s s' hs hs' => rw [map_add, add_smul, add_smul, map_add, map_add, hs, hs', add_mul]

/-! ### The isomorphism -/

/-- `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)`. -/
def indFun : ZZ a b →+ ZabTw a b →+ IZ a b :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun F => zE ((a + 2) + (b + 2))
      (polyHom y * EQZab.tauAB (a + 2) (b + 2) (twVal F)))
      fun F F' => by rw [twVal_add, map_add, mul_add, map_add])
    fun y y' => AddMonoidHom.ext fun F => by
      change zE _ (polyHom (y + y') * _) = zE _ (polyHom y * _) + zE _ (polyHom y' * _)
      rw [map_add, add_mul, map_add]

theorem indFun_apply (y : ZZ a b) (F : ZabTw a b) :
    indFun y F = zE ((a + 2) + (b + 2)) (polyHom y * EQZab.tauAB (a + 2) (b + 2) (twVal F)) :=
  rfl

theorem indFun_balanced (r : Λa ᵍ⊗[ℤ] Λb) (y : ZZ a b) (F : ZabTw a b) :
    indFun (op r • y) F = indFun y (r • F) := by
  rw [indFun_apply, indFun_apply, polyHom_op_smul, val_rhoTw_smul, map_mul (EQZab.tauAB _ _),
    EQBorel.sp_mul_assoc]

/-- `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)` on `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^{tw}_{a,b}`. -/
def indHom : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b) →+ IZ a b :=
  TensorProductOver.lift indFun indFun_balanced

theorem indHom_tmul (y : ZZ a b) (F : ZabTw a b) :
    indHom (TensorProductOver.tmul _ y F) = indFun y F := rfl

theorem tauAB_mem_grading {N M : ℕ} {k : ℤ} {f : SkewPolynomial (N + M)}
    (hf : f ∈ grading (N + M) k) : EQZab.tauAB N M f ∈ grading (N + M) k :=
  ringHom_mem_grading _ (fun j => by
    rw [EQZab.tauAB, EQZab.diagHom_generator]
    exact AddSubgroup.zsmul_mem _ (generator_mem_grading _) _) hf

theorem indHom_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b)) :
    indHom (s • t) = s • indHom t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul y F =>
    rw [TensorProductOver.smul_tmul, indHom_tmul, indHom_tmul, indFun_apply, indFun_apply]
    change _ = ONH.iota a b s • (zE ((a + 2) + (b + 2)) _ : Zn ((a + 2) + (b + 2)))
    apply (zE _).symm.injective
    rw [zE_symm_iota_smul_mul s _ _ (blockSym_tauAB (twVal_mem F)), ← zE_polyHom_smul,
      AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  | add t t' ht ht' =>
    rw [show s • (t + t') = s • t + s • t' from smul_add s t t', map_add, map_add, ht, ht',
      show s • (indHom t + indHom t') = s • indHom t + s • indHom t' from smul_add _ _ _]

theorem indHom_op_smul (h : osymDG ((a + 2) + (b + 2)))
    (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b)) :
    indHom (op h • t) = op h • indHom t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul y F =>
    rw [TensorProductOver.op_smul_tmul_right, indHom_tmul, indHom_tmul, indFun_apply, indFun_apply]
    rw [twVal_op_smul]
    change _ = (op h • (zE ((a + 2) + (b + 2)) _ : Zn ((a + 2) + (b + 2))))
    apply (zE _).symm.injective
    rw [AddEquiv.symm_apply_apply, EQSkewDifferential.Zn.op_smul_osym, EQSkewDifferential.Zn.symm_op_smul,
      AddEquiv.symm_apply_apply, map_mul, EQZab.tauAB_phiAB, EQBorel.sp_mul_assoc]
    rfl
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

theorem indHom_mem {k : ℤ} {t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b)}
    (ht : t ∈ DG.grading k) : indHom t ∈ DG.grading k :=
  TensorProductOver.lift_mem indFun indFun_balanced (fun {i j y F} hy hF => by
    rw [indFun_apply]
    change zE _ _ ∈ DG.grading (M := Zn ((a + 2) + (b + 2))) (i + j)
    refine OPolAlpha.mem_grading_iff.mpr ?_
    rw [AddEquiv.symm_apply_apply]
    exact mul_mem_grading' (polyHom_mem hy) (tauAB_mem_grading (twVal_mem_grading hF))) ht

theorem indFun_d {i : ℤ} {y : ZZ a b} (hy : y ∈ DG.grading i) (F : ZabTw a b) :
    DG.d (indFun y F) = indFun (DG.d y) F + koszulSign i • indFun y (DG.d F) := by
  rw [indFun_apply, indFun_apply, indFun_apply]
  change DG.d (zE ((a + 2) + (b + 2)) _ : Zn ((a + 2) + (b + 2))) = _
  apply (zE _).symm.injective
  rw [OPolAlpha.symm_d, AddEquiv.symm_apply_apply, map_add, AddEquiv.symm_apply_apply, Units.smul_def,
    map_zsmul, AddEquiv.symm_apply_apply, polyHom_d, indicator_oddStrands, twVal_d]
  have hP := parityInv_of_mem (polyHom_mem hy)
  set P := polyHom y
  set G := twVal F
  rw [← smul_mul_assoc, ← hP, EQZab.dZ_apply, dAlpha_apply, dAlpha_apply, EQSkewDifferential.d_mul,
    d_tauAB, sAlpha_zAlpha_eq, map_add (EQZab.tauAB _ _), map_mul (EQZab.tauAB _ _) (parityInv _ G),
    map_zsmul (EQZab.tauAB _ _), EQZab.tauAB_inclY, ← EQZab.parityInv_tauAB, map_mul (parityInv _)]
  rw [show ∀ X Y Z : SkewPolynomial ((a + 2) + (b + 2)), X * (Y - Z) = X * Y - X * Z from
    fun X Y Z => by rw [sub_eq_add_neg, mul_add, mul_neg, ← sub_eq_add_neg]]
  simp only [mul_add, add_mul, EQBorel.sp_mul_assoc, mul_smul_comm]
  abel

theorem sp_mul_one' {m : ℕ} (x : SkewPolynomial m) : x * 1 = x := by
  let := OddMath.PbwL3.instSemiring m
  exact mul_one x

theorem sp_one_mul' {m : ℕ} (x : SkewPolynomial m) : 1 * x = x := by
  let := OddMath.PbwL3.instSemiring m
  exact one_mul x

variable (a b) in
/-- The generator `z` of `Z^{tw}_{a,b}`. -/
def zabOneTw : ZabTw a b := show EQFix.Zab (a + 2) (b + 2) from EQFix.Zab.mk 1 (one_mem _)

theorem twVal_one : twVal (zabOneTw a b) = 1 := rfl

theorem exists_smul_one (F : ZabTw a b) : ∃ r : Λa ᵍ⊗[ℤ] Λb, r • zabOneTw a b = F := by
  have hF : OPol.equiv _ (blockRev (a + 2) (b + 2) (twVal F)) ∈ osymABDG (a + 2) (b + 2) :=
    mem_osymABDG.mpr (by rw [RingEquiv.symm_apply_apply]; exact blockRev_mem _ _ (twVal_mem F))
  obtain ⟨r, hr⟩ := tensorToOsymAB_surjective (a := a + 2) (b := b + 2) ⟨_, hF⟩
  refine ⟨r, EQFix.Zab.ext ?_⟩
  change blockRev (a + 2) (b + 2) (rHat r) * 1 = twVal F
  have : rHat r = blockRev (a + 2) (b + 2) (twVal F) := by
    rw [rHat, ← coe_tensorToOsymAB, hr]
    rfl
  rw [this, blockRev_blockRev, sp_mul_one']

/-- The inverse of `indHom`: `p ↦ (u ⊠ v) ⊗ z` for `p = u(x) v(y)`. -/
def indInv : IZ a b →+ TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b) :=
  AddMonoidHom.mk' (fun z => TensorProductOver.tmul _ (polyEquiv.symm ((zE _).symm
      (show Zn ((a + 2) + (b + 2)) from z))) (zabOneTw a b))
    fun z z' => by
      change TensorProductOver.tmul _ (polyEquiv.symm ((zE _).symm (z + z'))) _ = _
      rw [map_add, map_add, TensorProductOver.add_tmul]

theorem indHom_indInv (z : IZ a b) : indHom (indInv z) = z := by
  change zE _ (polyHom (polyEquiv.symm _) * EQZab.tauAB _ _ (twVal (zabOneTw a b))) = z
  rw [twVal_one, map_one, sp_mul_one', ← polyEquiv_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

theorem indInv_indHom (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b)) :
    indInv (indHom t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y F =>
    obtain ⟨r, rfl⟩ := exists_smul_one F
    rw [← TensorProductOver.op_smul_tmul, indHom_tmul, indFun_apply, twVal_one, map_one,
      sp_mul_one']
    change TensorProductOver.tmul _ (polyEquiv.symm ((zE _).symm (zE _ (polyHom (op r • y))))) _ = _
    rw [AddEquiv.symm_apply_apply, ← polyEquiv_apply, AddEquiv.symm_apply_apply]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

variable (a b) in
/-- **`(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^{tw}_{a,b} ≅ ι^* Z_{a+b}`** (Ellis–Qi §4.4, the bimodule behind
the induction half of Corollary 4.21; ranks `a + 2`, `b + 2`): `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)`, an
isomorphism of dg left `ONH_a ⊗ ONH_b`-modules, right `OΛ_{a+b}`-linear (`indEquiv_op_smul`). -/
def indEquiv : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b) ≃ᵈᵍ[𝒪a ᵍ⊗[ℤ] 𝒪b] IZ a b where
  toFun := indHom
  invFun := indInv
  left_inv := indInv_indHom
  right_inv := indHom_indInv
  map_add' := map_add _
  map_smul' := indHom_smul
  map_mem' := indHom_mem
  map_d' := TensorProductOver.lift_d indFun indFun_balanced fun hy F => indFun_d hy F

theorem indEquiv_tmul (y : ZZ a b) (F : ZabTw a b) :
    indEquiv a b (TensorProductOver.tmul _ y F) =
      zE ((a + 2) + (b + 2)) (polyHom y * EQZab.tauAB (a + 2) (b + 2) (twVal F)) := rfl

theorem indEquiv_op_smul (h : osymDG ((a + 2) + (b + 2)))
    (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabTw a b)) :
    indEquiv a b (op h • t) = op h • indEquiv a b t :=
  indHom_op_smul h t

/-! ### Without the twist there is no isomorphism -/

section Untwisted

variable (a b) in
/-- `Z_{a,b}` of Definition 4.6 with the untwisted left action of `OΛ_a ⊗ OΛ_b`: `f ⊗ g` acts by
multiplication by `f(x) g(y)` (`EQFunctor.Zab.instDGBimodule`, through `OΛ_a ⊗ OΛ_b ≅ OΛ_{a,b}`). -/
abbrev ZabU : Type := RestrictScalars (tensorToOsymAB (a + 2) (b + 2)) (EQFix.Zab (a + 2) (b + 2))

/-- The underlying skew polynomial of an element of `ZabU`. -/
def uVal (F : ZabU a b) : SkewPolynomial ((a + 2) + (b + 2)) :=
  EQFix.Zab.val (show EQFix.Zab (a + 2) (b + 2) from F)

theorem uVal_add (F F' : ZabU a b) : uVal (F + F') = uVal F + uVal F' := rfl

theorem uVal_smul (r : Λa ᵍ⊗[ℤ] Λb) (F : ZabU a b) : uVal (r • F) = rHat r * uVal F := rfl

theorem uVal_op_smul (h : osymDG ((a + 2) + (b + 2))) (F : ZabU a b) :
    uVal (op h • F) = uVal F * EQZab.phiAB _ _ (EQFix.toSkew h) := rfl

variable (a b) in
/-- The generator `z` of `ZabU`. -/
def uOne : ZabU a b := show EQFix.Zab (a + 2) (b + 2) from EQFix.Zab.mk 1 (one_mem _)

theorem uVal_one : uVal (uOne a b) = 1 := rfl

variable (a b) in
/-- `1_z ⊠ 1_z ∈ Z_a ⊠ Z_b`. -/
def yOne : ZZ a b := zE (a + 2) 1 ⊗ₜ[ℤ] zE (b + 2) 1

theorem polyHom_yOne : polyHom (yOne a b) = 1 := by
  rw [yOne, polyHom_tmul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, map_one, map_one,
    sp_mul_one']

/-- A balanced map out of `(Z_a ⊠ Z_b) ⊗ ZabU` (used only to see that `1 ⊗ z ≠ 0`). -/
def uFun : ZZ a b →+ ZabU a b →+ SkewPolynomial ((a + 2) + (b + 2)) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun F =>
      polyHom y * EQZab.tauAB (a + 2) (b + 2) (blockRev (a + 2) (b + 2) (uVal F)))
      fun F F' => by rw [uVal_add, map_add, map_add, mul_add])
    fun y y' => AddMonoidHom.ext fun F => by
      change polyHom (y + y') * _ = polyHom y * _ + polyHom y' * _
      rw [map_add, add_mul]

theorem uFun_balanced (r : Λa ᵍ⊗[ℤ] Λb) (y : ZZ a b) (F : ZabU a b) :
    uFun (op r • y) F = uFun y (r • F) := by
  change polyHom (op r • y) * _ = polyHom y * EQZab.tauAB _ _ (blockRev _ _ (uVal (r • F)))
  rw [polyHom_op_smul, uVal_smul, map_mul (blockRev _ _), map_mul (EQZab.tauAB _ _), EQBorel.sp_mul_assoc]

theorem tmul_yOne_uOne_ne_zero :
    TensorProductOver.tmul (Λa ᵍ⊗[ℤ] Λb) (yOne a b) (uOne a b) ≠ 0 := by
  intro h
  have := congrArg (TensorProductOver.lift uFun uFun_balanced) h
  rw [TensorProductOver.lift_tmul, map_zero] at this
  change polyHom (yOne a b) * _ = 0 at this
  rw [polyHom_yOne, uVal_one, map_one, map_one, sp_mul_one'] at this
  exact one_ne_zero (α := SkewPolynomial ((a + 2) + (b + 2))) this

end Untwisted

theorem eq_smul_one_of_mem_grading_zero {N : ℕ} {f : SkewPolynomial N} (hf : f ∈ grading N 0) :
    f = f 0 • (1 : SkewPolynomial N) := by
  ext α
  change f α = (f 0 • Finsupp.single (0 : Fin N → ℕ) (1 : ℤ)) α
  rw [Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs with hα
  · rw [← hα, smul_eq_mul, mul_one]
  · rw [smul_zero]
    by_contra hne
    have hdeg : totalDeg α = 0 := hf α (Finsupp.mem_support_iff.mpr hne)
    apply hα
    funext i
    have hsum : ∑ j, (α j : ℤ) = 0 := hdeg
    have hnn : ∀ j ∈ Finset.univ, (0 : ℤ) ≤ (α j : ℤ) := fun j _ => Int.natCast_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ _)
    simp only [Pi.zero_apply]
    omega

theorem exists_smul_yOne (y : ZZ a b) : ∃ s : 𝒪a ᵍ⊗[ℤ] 𝒪b, y = s • yOne a b := by
  induction y using DG.tensor_induction_on with
  | zero => exact ⟨0, (ExternalTensor.zero_smul' _).symm⟩
  | @tmul k l u v =>
    refine ⟨ONH.polyHom a (OPol.equiv _ ((zE _).symm (u : Zn (a + 2)))) ᵍ⊗ₜ[ℤ]
      ONH.polyHom b (OPol.equiv _ ((zE _).symm (v : Zn (b + 2)))), ?_⟩
    have hv : ONH.polyHom b (OPol.equiv _ ((zE _).symm (v : Zn (b + 2)))) ∈ DG.grading l :=
      (ONH.polyHom b).map_mem (OPol.equiv_mem_grading_iff.mpr (OPolAlpha.mem_grading_iff.mp v.2))
    have h1 : zE (a + 2) 1 ∈ DG.grading (0 : ℤ) := OPolAlpha.mem_grading_iff.mpr (by
      rw [AddEquiv.symm_apply_apply]; exact one_mem_grading')
    rw [yOne, ExternalTensor.tmul_smul_tmul _ hv h1, mul_zero, koszulSign_zero, one_smul,
      ONH.polyHom_smul, ONH.polyHom_smul]
    congr 1
    · apply (zE _).symm.injective
      rw [OPolAlpha.symm_smul, AddEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, sp_mul_one']
    · apply (zE _).symm.injective
      rw [OPolAlpha.symm_smul, AddEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, sp_mul_one']
  | add y y' hy hy' =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨s', rfl⟩ := hy'
    exact ⟨s + s', (ExternalTensor.add_smul' _ _ _).symm⟩

variable (a b) in
/-- `(1_z ⊠ 1_z) ⊗ z`. -/
def t0U : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabU a b) :=
  TensorProductOver.tmul (Λa ᵍ⊗[ℤ] Λb) (yOne a b) (uOne a b)

theorem t0U_mem : t0U a b ∈ DG.grading (0 : ℤ) := by
  have hy : yOne a b ∈ DG.grading (0 : ℤ) := by
    have := DG.tmul_mem_grading (M := Zn (a + 2)) (N := Zn (b + 2))
      (OPolAlpha.mem_grading_iff.mpr (by rw [AddEquiv.symm_apply_apply]; exact one_mem_grading'))
      (OPolAlpha.mem_grading_iff.mpr (by rw [AddEquiv.symm_apply_apply]; exact one_mem_grading'))
    rwa [add_zero] at this
  have := TensorProductOver.tmul_mem_grading (A := Λa ᵍ⊗[ℤ] Λb) hy
    (show uOne a b ∈ DG.grading (0 : ℤ) from EQFix.Zab.mem_grading_iff.mpr one_mem_grading')
  rwa [add_zero] at this

/-- An isomorphism `(Z_a ⊠ Z_b) ⊗ ZabU ≅ ι^* Z_{a+b}` of dg `(ONH_a ⊗ ONH_b, OΛ_{a+b})`-bimodules
would force `c (w₀ × w₀)(φ h) = c φ h` for some `c ≠ 0` and all `h ∈ OΛ_{a+b}`. -/
theorem untwisted_constraint
    (e : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZabU a b) ≃ᵈᵍ[𝒪a ᵍ⊗[ℤ] 𝒪b] IZ a b)
    (he : ∀ (h : osymDG ((a + 2) + (b + 2))) t, e (op h • t) = op h • e t) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ h : osymDG ((a + 2) + (b + 2)),
      c • blockRev (a + 2) (b + 2) (EQZab.phiAB _ _ (EQFix.toSkew h)) =
        c • EQZab.phiAB _ _ (EQFix.toSkew h) := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (zE ((a + 2) + (b + 2))).symm (e (t0U a b)) = c • 1 :=
    ⟨_, eq_smul_one_of_mem_grading_zero (OPolAlpha.mem_grading_iff.mp (e.map_mem t0U_mem))⟩
  have het0 : e (t0U a b) = zE _ (c • polyHom (yOne a b)) := by
    rw [polyHom_yOne, ← hc, AddEquiv.apply_symm_apply]
  refine ⟨c, fun hc0 => tmul_yOne_uOne_ne_zero (a := a) (b := b) (e.injective ?_), fun h => ?_⟩
  · change e (t0U a b) = e 0
    rw [map_zero, het0, hc0, zero_smul, map_zero]
  have key : ∀ s : 𝒪a ᵍ⊗[ℤ] 𝒪b,
      e (TensorProductOver.tmul _ (s • yOne a b) (uOne a b)) = zE _ (c • polyHom (s • yOne a b)) := by
    intro s
    rw [← TensorProductOver.smul_tmul, map_smul]
    change s • e (t0U a b) = _
    rw [het0, map_zsmul, map_zsmul]
    change ONH.iota a b s • ((c • zE _ (polyHom (yOne a b))) : Zn ((a + 2) + (b + 2))) = _
    rw [smul_comm (ONH.iota a b s) c, zE_polyHom_smul]
  have hφ : OPol.equiv _ (EQZab.phiAB _ _ (EQFix.toSkew h)) ∈ osymABDG (a + 2) (b + 2) :=
    mem_osymABDG.mpr (by
      rw [RingEquiv.symm_apply_apply]; exact EQZab.phiAB_mem (EQFix.toSkew_mem h))
  obtain ⟨r, hr⟩ := tensorToOsymAB_surjective (a := a + 2) (b := b + 2) ⟨_, hφ⟩
  have hrHat : rHat r = EQZab.phiAB _ _ (EQFix.toSkew h) := by
    rw [rHat, ← coe_tensorToOsymAB, hr]
    rfl
  have hop : op h • uOne a b = r • uOne a b := EQFix.Zab.ext (by
    change uVal (uOne a b) * _ = rHat r * uVal (uOne a b)
    rw [uVal_one, hrHat, sp_one_mul', sp_mul_one']
    rfl)
  obtain ⟨s, hs⟩ := exists_smul_yOne (op r • yOne a b)
  have hL : op h • t0U a b = TensorProductOver.tmul _ (s • yOne a b) (uOne a b) := by
    rw [t0U, TensorProductOver.op_smul_tmul_right, hop, ← TensorProductOver.op_smul_tmul, hs]
  have hlhs : (zE ((a + 2) + (b + 2))).symm (e (op h • t0U a b)) =
      c • EQZab.tauAB _ _ (blockRev _ _ (EQZab.phiAB _ _ (EQFix.toSkew h))) := by
    rw [hL, key, AddEquiv.symm_apply_apply, ← hs, polyHom_op_smul, polyHom_yOne, hrHat, sp_one_mul']
  have hrhs : (zE ((a + 2) + (b + 2))).symm (op h • e (t0U a b)) =
      c • EQZab.tauAB _ _ (EQZab.phiAB _ _ (EQFix.toSkew h)) := by
    rw [EQZab.tauAB_phiAB]
    change (zE _).symm (e (t0U a b)) * twistRev _ (EQFix.toSkew h) = _
    rw [hc, smul_mul_assoc, sp_one_mul']
  have h2 : c • EQZab.tauAB _ _ (blockRev _ _ (EQZab.phiAB _ _ (EQFix.toSkew h))) =
      c • EQZab.tauAB _ _ (EQZab.phiAB _ _ (EQFix.toSkew h)) := by
    rw [← hlhs, ← hrhs, he]
  rw [← map_zsmul (EQZab.tauAB (a + 2) (b + 2)) c, ← map_zsmul (EQZab.tauAB (a + 2) (b + 2)) c] at h2
  have h3 := congrArg (EQZab.tauAB (a + 2) (b + 2)) h2
  simpa only [EQZab.tauAB_tauAB, map_zsmul] using h3

/-! ### The witness `h = e_2`, `a = b = 2` -/

theorem strictSum_zero_fun {R : Type*} [Ring R] :
    ∀ (n k : ℕ), FiniteCompleteElementary.FiniteWords.strictSum (fun _ : Fin n => (0 : R)) (k + 1) = 0
  | 0, k => FiniteCompleteElementary.FiniteWords.strictSum_empty _ k
  | n + 1, k => by
    rw [FiniteCompleteElementary.FiniteWords.strictSum_succ, zero_mul, zero_add]
    exact strictSum_zero_fun n k

theorem elementary_two_two : elementary 2 2 = generator 0 * generator 1 := by
  simp [elementary, FiniteCompleteElementary.FiniteWords.strictSum_succ, EQBorel.sp_mul_zero]

variable (a b) in
/-- `OPol_{a+b} → OPol_a`, `x ↦ x`, `y ↦ 0`. -/
def projX (A B : ℕ) : SkewPolynomial (A + B) →+* SkewPolynomial A :=
  skewLift (fun j => if h : j.val < A then generator ⟨j.val, h⟩ else 0) (fun i j hij => by
    by_cases hi : i.val < A <;> by_cases hj : j.val < A
    · simp only [hi, hj, dite_true]
      exact OddMath.PbwL1.rel_sum _ _ (fun e => hij (Fin.ext (by simpa using congrArg Fin.val e)))
    · simp [hi, hj, EQBorel.sp_mul_zero, EQBorel.sp_zero_mul]
    · simp [hi, hj, EQBorel.sp_mul_zero, EQBorel.sp_zero_mul]
    · simp [hi, hj, EQBorel.sp_mul_zero])

theorem projX_inclX {A B : ℕ} (f : SkewPolynomial A) : projX A B (inclX A B f) = f := by
  have h : (projX A B).comp (inclX A B) = RingHom.id _ := ringHom_ext fun i => by
    simp [projX, i.isLt]
  exact RingHom.congr_fun h f

theorem projX_inclY_elementary_two {A B : ℕ} : projX A B (inclY A B (elementary B 2)) = 0 := by
  rw [elementary, EQZab.ringHom_strictSum, EQZab.ringHom_strictSum]
  have h : (fun j : Fin B => projX A B (inclY A B (generator j))) = fun _ => 0 := by
    funext j
    simp [projX]
  rw [h]
  exact strictSum_zero_fun B 1

theorem blockRev_elementary_two (A B : ℕ) :
    blockRev A B (elementary (A + B) 2) =
      elementary (A + B) 2 - (2 : ℤ) • (inclX A B (elementary A 2) + inclY A B (elementary B 2)) := by
  have hE : elementary (A + B) 2 = inclX A B (elementary A 2) +
      inclX A B (elementary A 1) * inclY A B (elementary B 1) + inclY A B (elementary B 2) := by
    rw [EQZab.elementary_add, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    have h0 : ∀ m, elementary m 0 = 1 := fun m => FiniteCompleteElementary.FiniteWords.strictSum_zero _
    simp only [zero_add, Nat.reduceAdd, h0, map_one, sp_one_mul', sp_mul_one']
    abel
  rw [hE, map_add, map_add, map_mul, blockRev_inclX, blockRev_inclX, blockRev_inclY, blockRev_inclY,
    EQFix.longestPerm_elementary, EQFix.longestPerm_elementary, EQFix.longestPerm_elementary,
    EQFix.longestPerm_elementary]
  rw [show Nat.choose 1 2 = 0 from rfl, show Nat.choose 2 2 = 1 from rfl, pow_zero, pow_one, one_smul,
    one_smul, neg_one_smul, neg_one_smul, map_neg, map_neg, two_smul]
  abel

theorem phiAB_elementary_two :
    EQZab.phiAB (0 + 2) (0 + 2) (elementary ((0 + 2) + (0 + 2)) 2) = -elementary ((0 + 2) + (0 + 2)) 2 := by
  have hε : ∀ f, EQZab.epsAB (0 + 2) (0 + 2) f = f := by
    intro f
    have h : EQZab.epsAB (0 + 2) (0 + 2) = RingHom.id _ := ringHom_ext fun j => by
      rw [EQZab.epsAB, EQZab.diagHom_generator, RingHom.id_apply]
      simp [EQZab.epsCoeff]
    rw [h, RingHom.id_apply]
  rw [EQZab.phiAB, RingHom.comp_apply, hε, EQFix.longestPerm_elementary,
    show Nat.choose 2 2 = 1 from rfl, pow_one, neg_one_smul]

/-- **No isomorphism without the twist** (`a = b = 2`): for `Z_{2,2}` of Definition 4.6 with the
untwisted left action of `OΛ_2 ⊗ OΛ_2` (multiplication in `OΛ_2 ⊠ OΛ_2`), there is no isomorphism of
dg `(ONH_2 ⊗ ONH_2, OΛ_4)`-bimodules `(Z_2 ⊠ Z_2) ⊗_{OΛ_2 ⊗ OΛ_2} Z_{2,2} ≅ ι^* Z_4`. Witness:
`h = e_2`, for which `(w₀ × w₀)(φ e_2) - φ e_2 = 2 (e_2(x) + e_2(y)) ≠ 0`. -/
theorem no_indEquiv_untwisted :
    ¬ ∃ e : TensorProductOver (DGAlgebra.gradingSubmodule ℤ (osymDG (0 + 2)) ᵍ⊗[ℤ]
        DGAlgebra.gradingSubmodule ℤ (osymDG (0 + 2))) (ZZ 0 0) (ZabU 0 0) ≃ᵈᵍ[
          DGAlgebra.gradingSubmodule ℤ (ONH 0) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (ONH 0)] IZ 0 0,
      ∀ (h : osymDG ((0 + 2) + (0 + 2))) t, e (op h • t) = op h • e t := by
  rintro ⟨e, he⟩
  obtain ⟨c, hc0, hc⟩ := untwisted_constraint e he
  have h := hc ⟨OPol.equiv _ (elementary _ 2), elementary_mem_osymDG 2⟩
  rw [show EQFix.toSkew (⟨OPol.equiv _ (elementary _ 2), elementary_mem_osymDG 2⟩ :
      osymDG ((0 + 2) + (0 + 2))) = elementary _ 2 from rfl, phiAB_elementary_two, map_neg,
    blockRev_elementary_two, smul_neg, smul_neg, neg_inj, smul_sub, sub_eq_self, smul_smul] at h
  have h2 := congrArg (projX (0 + 2) (0 + 2)) h
  rw [map_zsmul, map_add, projX_inclX, projX_inclY_elementary_two, add_zero, map_zero] at h2
  have h3 := congrArg (fun f : SkewPolynomial (0 + 2) => f (show Fin (0 + 2) → ℕ from ![1, 1])) h2
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [show elementary (0 + 2) 2 = generator 0 * generator 1 from elementary_two_two] at h3
  have h4 : (generator (0 : Fin 2) * generator 1 : SkewPolynomial 2) ![1, 1] = 1 :=
    OddMath.SkewPolynomial.ordered_rank_two_coordinate
  rw [show (generator (0 : Fin (0 + 2)) * generator 1 : SkewPolynomial (0 + 2))
      (show Fin (0 + 2) → ℕ from ![1, 1]) = 1 from h4, smul_eq_mul, mul_one] at h3
  omega

end OddMath.Frontier.EQFunctor
