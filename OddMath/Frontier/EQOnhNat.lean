import OddMath.Frontier.EQRestrictionPoly
import OddMath.Frontier.EQInductionBimodule
import OddMath.Frontier.EQRegrade
import DG.Module.Sub

/-!
# The right ideal `(x_{a+1} ⋯ x_{a+b})^a ONH_{a+b}`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, (4.32) and the sentence after it; ranks `a + 2`, `b + 2`.

With `P = y_1 ⋯ y_b` and `P^a` (`a = a' + 2`, `b = b' + 2`) as an element `Pw` of `ONH_{a+b}` (dots):

* `del_mul_polyRingHom`: `∂_i f = s_i(f) ∂_i + ∂_i(f)` in `ONH_n` for a polynomial `f`;
* `iotaL_mul_Pw`, `iotaR_mul_Pw`, `iota_mul_Pw`: `ι(g) P^a = P^a ι(τ g)` for the graded twists
  `τ = (-1)^{ab |·|}` on `ONH_a` and `(-1)^{(b-1)a |·|}` on `ONH_b`, so `P^a ONH_{a+b}` is stable under
  left multiplication by `ι(ONH_a ⊗ ONH_b)`;
* `d_Pw`: `d(P^a) = {a} e_1(y) P^a` in `ONH_{a+b}`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY par)
open OddMath.Frontier.EQOnhDG (ONH)
open DG MulOpposite

/-! ### Crossings past polynomials in `ONH` -/

theorem del_mul_polyRingHom {n : ℕ} (i : Fin (n + 1)) (f : SkewPolynomial (n + 2)) :
    ONH.del i * ONH.polyRingHom n f =
      ONH.polyRingHom n (AllRankDivided.s i f) * ONH.del i +
        ONH.polyRingHom n (AllRankDivided.divided i f) := by
  apply (EQOnhDG.ONH.equiv n).symm.injective
  apply NilHeckeBasis.action_injective n
  refine LinearMap.ext fun g => ?_
  have e1 : (EQOnhDG.ONH.equiv n).symm (ONH.del i) = NilHeckeAction.crossing n i := rfl
  have e2 : ∀ f, (EQOnhDG.ONH.equiv n).symm (ONH.polyRingHom n f) = OnhPolynomial.polyElem n f :=
    fun _ => rfl
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, e1, e2,
    NilHeckeAction.action_crossing_apply, OnhPolynomial.action_polyElem, AllRankDivided.divided_mul]
  exact add_comm _ _

/-! ### `P^a` and the windows -/

variable (a b : ℕ)

/-- `P^a = (y_1 ⋯ y_b)^a ∈ OPol_{a+b}`. -/
abbrev PA : SkewPolynomial ((a + 2) + (b + 2)) := topY (a + 2) (b + 2) ^ (a + 2)

/-- `P^a ∈ ONH_{a+b}`. -/
abbrev Pw : ONH (a + 2 + b) := ONH.polyRingHom (a + 2 + b) (PA a b)

variable {a b}

theorem inclY_eq_place' (f : SkewPolynomial (b + 2)) :
    inclY (a + 2) (b + 2) f = ProjectorRank.place (a + 2) le_y f := inclY_eq_place f

theorem PA_eq_place : PA a b = ProjectorRank.place (a + 2) (le_y (a := a) (b := b))
    (elementary (b + 2) (b + 2) ^ (a + 2)) := by
  rw [PA, topY, inclY_eq_place, map_pow]

theorem iotaL_x (j : Fin (a + 2)) :
    ONH.iotaL a b (ONH.x j) = ONH.polyRingHom (a + 2 + b) (inclX (a + 2) (b + 2) (generator j)) := by
  rw [ONH.iotaL, EQOnhDG.ONH.windowDG_apply, EQOnhDG.ONH.windowRing_x, ← EQOnhDG.ONH.polyRingHom_generator,
    EQZab.inclX_generator]
  congr 2

theorem iotaR_x (j : Fin (b + 2)) :
    ONH.iotaR a b (ONH.x j) = ONH.polyRingHom (a + 2 + b) (inclY (a + 2) (b + 2) (generator j)) := by
  rw [ONH.iotaR, EQOnhDG.ONH.windowDG_apply, EQOnhDG.ONH.windowRing_x, ← EQOnhDG.ONH.polyRingHom_generator,
    EQZab.inclY_generator]
  congr 2
  exact Fin.ext (by simp; omega)

theorem iotaL_del (i : Fin (a + 1)) :
    ONH.iotaL a b (ONH.del i) = ONH.del (OnhWindow.shiftIndex (le_x (a := a) (b := b)) i) := by
  rw [ONH.iotaL, EQOnhDG.ONH.windowDG_apply, EQOnhDG.ONH.windowRing_del]
  rfl

theorem iotaR_del (k : Fin (b + 1)) :
    ONH.iotaR a b (ONH.del k) = ONH.del (OnhWindow.shiftIndex (le_y (a := a) (b := b)) k) := by
  rw [ONH.iotaR, EQOnhDG.ONH.windowDG_apply, EQOnhDG.ONH.windowRing_del]
  rfl

/-! #### Polynomial identities -/

theorem inclX_generator_mul_PA (j : Fin (a + 2)) :
    inclX (a + 2) (b + 2) (generator j) * PA a b =
      ((-1 : ℤ) ^ (b + 2)) ^ (a + 2) • (PA a b * inclX (a + 2) (b + 2) (generator j)) :=
  mul_topY_pow (inclX_generator_mul_topY j) _

theorem inclY_generator_mul_PA (j : Fin (b + 2)) :
    inclY (a + 2) (b + 2) (generator j) * PA a b =
      ((-1 : ℤ) ^ (b + 2 - 1)) ^ (a + 2) • (PA a b * inclY (a + 2) (b + 2) (generator j)) :=
  mul_topY_pow (inclY_generator_mul_topY j) _

theorem divided_PA_x (i : Fin (a + 1)) :
    AllRankDivided.divided (OnhWindow.shiftIndex (le_x (a := a) (b := b)) i) (PA a b) = 0 := by
  rw [PA_eq_place]
  exact EQThick.divided_place_eq_zero le_y _ (Or.inl (by simp; omega)) _

theorem s_PA_x (i : Fin (a + 1)) :
    AllRankDivided.s (OnhWindow.shiftIndex (le_x (a := a) (b := b)) i) (PA a b) =
      ((-1 : ℤ) ^ (b + 2)) ^ (a + 2) • PA a b := by
  have h : ∀ g : SkewPolynomial (b + 2), AllRankDivided.s (OnhWindow.shiftIndex (le_x (a := a) (b := b)) i)
      (inclY (a + 2) (b + 2) g) = inclY (a + 2) (b + 2) (parityInv (b + 2) g) := by
    intro g
    have e : (AllRankDivided.s (OnhWindow.shiftIndex (le_x (a := a) (b := b)) i)).toRingHom.comp
        (inclY (a + 2) (b + 2)) = (inclY (a + 2) (b + 2)).comp (parityInv (b + 2)) :=
      ringHom_ext fun j => by
        show AllRankDivided.s _ (inclY (a + 2) (b + 2) (generator j)) =
          inclY (a + 2) (b + 2) (parityInv (b + 2) (generator j))
        rw [EQZab.inclY_generator, parityInv_generator, map_neg, EQZab.inclY_generator]
        change AllRankDivided.s _ (generator (Fin.natAdd (a + 2) j) : SkewPolynomial (a + 2 + b + 2)) = _
        rw [AllRankDivided.s_generator, Equiv.swap_apply_of_ne_of_ne]
        · intro h; have := congrArg Fin.val h; simp at this; omega
        · intro h; have := congrArg Fin.val h; simp at this; omega
    exact RingHom.congr_fun e g
  rw [PA, topY, map_pow, h, parityInv_elementary, map_zsmul, smul_pow]

theorem divided_PA_y (k : Fin (b + 1)) :
    AllRankDivided.divided (OnhWindow.shiftIndex (le_y (a := a) (b := b)) k) (PA a b) = 0 := by
  rw [PA_eq_place, (ProjectorRank.place_divided_and_s le_y k _).1]
  have hk : elementary (b + 2) (b + 2) ^ (a + 2) ∈ OddSymmetricKernel.kernelSubring b :=
    pow_mem (show elementary (b + 2) (b + 2) ∈ OddSymmetricKernel.kernelSubring b from
      fun i => divided_elementary_top b i) _
  rw [hk k, map_zero]

theorem s_PA_y (k : Fin (b + 1)) :
    AllRankDivided.s (OnhWindow.shiftIndex (le_y (a := a) (b := b)) k) (PA a b) =
      ((-1 : ℤ) ^ (b + 1)) ^ (a + 2) • PA a b := by
  rw [PA_eq_place, (ProjectorRank.place_divided_and_s le_y k _).2, map_pow, s_elementary_top, smul_pow,
    map_zsmul, map_pow]

/-! #### Commutation with `P^a` in `ONH_{a+b}` -/

theorem neg_one_pow_pow_eq_koszulSign (m k : ℕ) :
    ((-1 : ℤ) ^ m) ^ k = (koszulSign ((k * m : ℕ) : ℤ) : ℤ) := by
  rw [koszulSign_eq_neg_one_pow_natAbs, Int.natAbs_natCast, ← pow_mul, mul_comm]

variable (a b) in
/-- The twist `(-1)^{ab |·|}` of `ONH_a`. -/
abbrev twL : ONH a →+* ONH a := DG.Shift.twist (ONH a) (((a + 2) * (b + 2) : ℕ) : ℤ)

variable (a b) in
/-- The twist `(-1)^{(b-1)a |·|}` of `ONH_b`. -/
abbrev twR : ONH b →+* ONH b := DG.Shift.twist (ONH b) (((a + 2) * (b + 1) : ℕ) : ℤ)

theorem koszulSign_mul_neg_one (n : ℤ) : koszulSign (n * -1) = koszulSign n := by
  rw [mul_neg_one, koszulSign, Int.negOnePow_neg]

theorem smul_comm_helper {R : Type*} [Ring R] (u : ℤˣ) (P X : R) :
    (u : ℤ) • (P * X) = P * ((u : ℤ) • X) := by
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, Int.cast_comm]

theorem x_mul_Pw_left (j : Fin (a + 2)) :
    ONH.iotaL a b (ONH.x j) * Pw a b = Pw a b * ONH.iotaL a b (twL a b (ONH.x j)) := by
  rw [DG.Shift.twist_of_mem (EQOnhDG.ONH.x_mem_grading j), Units.smul_def, map_zsmul, iotaL_x, ← map_mul,
    inclX_generator_mul_PA, map_zsmul, map_mul, mul_one, neg_one_pow_pow_eq_koszulSign]
  exact smul_comm_helper _ _ _

theorem del_mul_Pw_left (i : Fin (a + 1)) :
    ONH.iotaL a b (ONH.del i) * Pw a b = Pw a b * ONH.iotaL a b (twL a b (ONH.del i)) := by
  rw [DG.Shift.twist_of_mem (EQOnhDG.ONH.del_mem_grading i), koszulSign_mul_neg_one, Units.smul_def,
    map_zsmul, iotaL_del, del_mul_polyRingHom, s_PA_x, divided_PA_x, map_zero, add_zero, map_zsmul,
    neg_one_pow_pow_eq_koszulSign, smul_mul_assoc]
  exact smul_comm_helper _ _ _

theorem x_mul_Pw_right (j : Fin (b + 2)) :
    ONH.iotaR a b (ONH.x j) * Pw a b = Pw a b * ONH.iotaR a b (twR a b (ONH.x j)) := by
  rw [DG.Shift.twist_of_mem (EQOnhDG.ONH.x_mem_grading j), Units.smul_def, map_zsmul, iotaR_x, ← map_mul,
    inclY_generator_mul_PA, map_zsmul, map_mul, mul_one, show b + 2 - 1 = b + 1 by omega,
    neg_one_pow_pow_eq_koszulSign]
  exact smul_comm_helper _ _ _

theorem del_mul_Pw_right (k : Fin (b + 1)) :
    ONH.iotaR a b (ONH.del k) * Pw a b = Pw a b * ONH.iotaR a b (twR a b (ONH.del k)) := by
  rw [DG.Shift.twist_of_mem (EQOnhDG.ONH.del_mem_grading k), koszulSign_mul_neg_one, Units.smul_def,
    map_zsmul, iotaR_del, del_mul_polyRingHom, s_PA_y, divided_PA_y, map_zero, add_zero, map_zsmul,
    neg_one_pow_pow_eq_koszulSign, smul_mul_assoc]
  exact smul_comm_helper _ _ _

theorem iotaL_mul_Pw (v : ONH a) : ONH.iotaL a b v * Pw a b = Pw a b * ONH.iotaL a b (twL a b v) := by
  refine EQOnhDG.ONH.freeAlgebra_ind (P := fun v => ONH.iotaL a b v * Pw a b =
    Pw a b * ONH.iotaL a b (twL a b v)) ?_ ?_ ?_ ?_ ?_ v
  · rw [map_one, map_one, map_one, one_mul, mul_one]
  · intro v w hv hw; rw [map_add, add_mul, hv, hw, map_add, map_add, mul_add]
  · intro v hv; rw [map_neg, neg_mul, hv, map_neg, map_neg, mul_neg]
  · intro j v hv
    rw [map_mul, mul_assoc, hv, ← mul_assoc, x_mul_Pw_left, mul_assoc, ← map_mul, ← map_mul]
  · intro i v hv
    rw [map_mul, mul_assoc, hv, ← mul_assoc, del_mul_Pw_left, mul_assoc, ← map_mul, ← map_mul]

theorem iotaR_mul_Pw (v : ONH b) : ONH.iotaR a b v * Pw a b = Pw a b * ONH.iotaR a b (twR a b v) := by
  refine EQOnhDG.ONH.freeAlgebra_ind (P := fun v => ONH.iotaR a b v * Pw a b =
    Pw a b * ONH.iotaR a b (twR a b v)) ?_ ?_ ?_ ?_ ?_ v
  · rw [map_one, map_one, map_one, one_mul, mul_one]
  · intro v w hv hw; rw [map_add, add_mul, hv, hw, map_add, map_add, mul_add]
  · intro v hv; rw [map_neg, neg_mul, hv, map_neg, map_neg, mul_neg]
  · intro j v hv
    rw [map_mul, mul_assoc, hv, ← mul_assoc, x_mul_Pw_right, mul_assoc, ← map_mul, ← map_mul]
  · intro i v hv
    rw [map_mul, mul_assoc, hv, ← mul_assoc, del_mul_Pw_right, mul_assoc, ← map_mul, ← map_mul]

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)

/-- **`ι(s) P^a ∈ P^a ONH_{a+b}`**: the right ideal is stable under `ι(ONH_a ⊗ ONH_b)`. -/
theorem iota_mul_Pw (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) : ∃ t : ONH (a + 2 + b), ONH.iota a b s * Pw a b = Pw a b * t := by
  induction s using GradedTensorProduct.induction_on_tmul with
  | zero => exact ⟨0, by rw [map_zero, zero_mul, mul_zero]⟩
  | @tmul i j f hf g hg =>
    refine ⟨ONH.iotaL a b (twL a b f) * ONH.iotaR a b (twR a b g), ?_⟩
    rw [ONH.iota_tmul, mul_assoc, iotaR_mul_Pw, ← mul_assoc, iotaL_mul_Pw, mul_assoc]
  | add s s' hs hs' =>
    obtain ⟨t, ht⟩ := hs
    obtain ⟨t', ht'⟩ := hs'
    exact ⟨t + t', by rw [map_add, add_mul, ht, ht', mul_add]⟩

/-- **`d(P^a) = {a} e_1(y) P^a`** in `ONH_{a+b}`, and `d(P^a) ∈ P^a ONH_{a+b}`. -/
theorem d_Pw : DG.d (Pw a b) =
    par (a + 2) • (ONH.polyRingHom (a + 2 + b) (e1Y (a + 2) (b + 2)) * Pw a b) := by
  have h := (EQOnhDG.ONH.polyHom (a + 2 + b)).map_d (OPol.equiv _ (PA a b))
  change DG.d (EQOnhDG.ONH.polyHom (a + 2 + b) (OPol.equiv _ (PA a b))) = _
  rw [← h]
  change EQOnhDG.ONH.polyRingHom (a + 2 + b) (d _ (PA a b)) = _
  rw [show d (a + 2 + b + 2) (PA a b) = _ from d_topY_pow (A := a + 2) (B := b + 2) (a + 2), map_zsmul,
    map_mul]

theorem d_Pw_mem : ∃ t : ONH (a + 2 + b), DG.d (Pw a b) = Pw a b * t := by
  refine ⟨par (a + 2) • (((-1 : ℤ) ^ (b + 2 - 1)) ^ (a + 2) •
    ONH.polyRingHom (a + 2 + b) (e1Y (a + 2) (b + 2))), ?_⟩
  rw [d_Pw, ← map_mul, mul_topY_pow (e1Y_mul_topY (A := a + 2) (B := b + 2)), map_zsmul, map_mul,
    mul_smul_comm, mul_smul_comm]

/-! ### The right ideal as a dg bimodule -/

variable (a b) in
/-- The degree `ab` of `P^a`. -/
abbrev degP : ℤ := ((b + 2 : ℕ) : ℤ) * ((a + 2 : ℕ) : ℤ)

theorem Pw_mem : Pw a b ∈ DG.grading (degP a b) := by
  have h := topY_pow_mem_grading (A := a + 2) (B := b + 2) (a + 2)
  exact (EQOnhDG.ONH.polyHom (a + 2 + b)).map_mem (OPol.equiv_mem_grading_iff.mpr h)

variable (a b) in
/-- `ι^* ONH_{a+b}`. -/
abbrev IONH : Type := RestrictScalars (ONH.iota a b) (ONH (a + 2 + b))

theorem iota_smul_IONH (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (x : IONH a b) :
    s • x = (show IONH a b from ONH.iota a b s * (show ONH (a + 2 + b) from x)) := rfl

variable (a b) in
/-- **The right ideal `P^a ONH_{a+b}`** as a dg left `ONH_a ⊗ ONH_b`-submodule of `ι^* ONH_{a+b}`. -/
def natSub : DGSubmodule (𝒪a ᵍ⊗[ℤ] 𝒪b) (IONH a b) where
  carrier := {x | ∃ h : ONH (a + 2 + b), (show ONH (a + 2 + b) from x) = Pw a b * h}
  add_mem' := by
    rintro x y ⟨h, hx⟩ ⟨h', hy⟩
    exact ⟨h + h', by rw [mul_add, ← hx, ← hy]⟩
  zero_mem' := ⟨0, by rw [mul_zero]⟩
  smul_mem' s x := by
    rintro ⟨h, hx⟩
    obtain ⟨t, ht⟩ := iota_mul_Pw s
    exact ⟨t * h, by rw [iota_smul_IONH]; change ONH.iota a b s * _ = _; rw [hx, ← mul_assoc, ht,
      mul_assoc]⟩
  d_mem' {x} := by
    rintro ⟨h, hx⟩
    obtain ⟨t, ht⟩ := d_Pw_mem (a := a) (b := b)
    refine ⟨t * h + (koszulSign (degP a b) : ℤ) • DG.d h, ?_⟩
    change DG.d (show ONH (a + 2 + b) from x) = _
    rw [hx, DG.d_mul Pw_mem, ht, mul_add, mul_assoc, Units.smul_def, mul_smul_comm]
  decompose_mem' k {x} hx := by
    obtain ⟨h, hx⟩ := hx
    change ∃ h', (DirectSum.decompose (DG.grading (M := ONH (a + 2 + b))) (show ONH (a + 2 + b) from x) k :
      ONH (a + 2 + b)) = Pw a b * h'
    rw [hx]
    clear hx
    induction h using DG.induction_on generalizing k with
    | h_zero => exact ⟨0, by simp⟩
    | @h_homogeneous j h =>
      have hm : Pw a b * (h : ONH (a + 2 + b)) ∈ DG.grading (degP a b + j) := DG.mul_mem_grading Pw_mem h.2
      by_cases hk : degP a b + j = k
      · subst hk
        exact ⟨h, by rw [DirectSum.decompose_of_mem_same _ hm]⟩
      · exact ⟨0, by rw [DirectSum.decompose_of_mem_ne _ hm hk, mul_zero]⟩
    | h_add h h' ih ih' =>
      obtain ⟨u, hu⟩ := ih k
      obtain ⟨u', hu'⟩ := ih' k
      exact ⟨u + u', by rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, AddSubgroup.coe_add,
        hu, hu', mul_add]⟩

theorem mem_natSub_mul {x : IONH a b} (hx : x ∈ natSub a b) (g : ONH (a + 2 + b)) :
    (show IONH a b from (show ONH (a + 2 + b) from x) * g) ∈ natSub a b := by
  obtain ⟨h, hx⟩ := hx
  exact ⟨h * g, by change (show ONH (a + 2 + b) from x) * g = _; rw [hx, mul_assoc]⟩

instance natSubSMulOp : SMul (ONH (a + 2 + b))ᵐᵒᵖ (natSub a b) :=
  ⟨fun g x => ⟨_, mem_natSub_mul x.2 g.unop⟩⟩

theorem coe_natSub_op_smul (g : ONH (a + 2 + b)) (x : natSub a b) :
    ((op g • x : natSub a b) : IONH a b) = op g • (x : IONH a b) := rfl

instance natSubModuleOp : Module (ONH (a + 2 + b))ᵐᵒᵖ (natSub a b) :=
  Function.Injective.module (ONH (a + 2 + b))ᵐᵒᵖ (AddSubmonoidClass.subtype (natSub a b))
    Subtype.val_injective fun _ _ => rfl

instance natSubDGRightModule : DGRightModule (ONH (a + 2 + b)) (natSub a b) where
  op_smul_mem' {i j g x} hg hx :=
    (DGSubmodule.mem_grading_iff _).mpr (op_smul_mem_grading (M := IONH a b) hg
      ((DGSubmodule.mem_grading_iff _).mp hx))
  d_op_smul' {j x} hx g := Subtype.ext (by
    change DG.d ((op g • (x : IONH a b))) = op g • DG.d (x : IONH a b) + koszulSign j • (op (DG.d g) • (x : IONH a b))
    exact d_op_smul (M := IONH a b) ((DGSubmodule.mem_grading_iff _).mp hx) g)

instance natSubSMulCommClass : SMulCommClass (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONH (a + 2 + b))ᵐᵒᵖ (natSub a b) where
  smul_comm s g x := Subtype.ext (smul_comm s g (x : IONH a b))

instance natSubDGBimodule : DGBimodule (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONH (a + 2 + b)) (natSub a b) :=
  DGBimodule.mk'

variable (a b) in
/-- **`ONH^♮_{a+b}`** (Ellis–Qi (4.32), corrected): the right ideal `P^a ONH_{a+b}`,
`P = x_{a+1} ⋯ x_{a+b}`, as a dg `(ONH_a ⊗ ONH_b, ONH_{a+b})`-bimodule (left action through `ι`),
regraded so that the generator `1^♮ = P^a` has degree `0` (the right action carries the sign
`(-1)^{ab |·|}`). -/
abbrev ONHNat : Type := Regrade (degP a b) (natSub a b)

example : DGBimodule (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONH (a + 2 + b)) (ONHNat a b) := inferInstance

end OddMath.Frontier.EQFunctor
