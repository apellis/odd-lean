import OddMath.Frontier.EQRestrictionFunctor
import OddMath.Frontier.EQActionCompare

/-!
# The right action of `OΛ_{a+b}` on `Z^♮_{a,b}` is forced

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.15 (`Z^♮_{a,b} = (OΛ̃_a ⊗ OΛ̃_b) · z^♮`, `d z^♮ = 0`, `z^♮` of degree `0`; the right action
of `OΛ_{a+b}` is not specified) and the proof of the restriction half of Corollary 4.21, which needs an
isomorphism of dg `(ONH_a ⊗ ONH_b, ONH_{a+b})`-bimodules
`((Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b}) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ ≅ ONH^♮_{a+b}`; ranks `a + 2`, `b + 2`.

A right action of `OΛ_{a+b}` on the free left module `(OΛ_a ⊗ OΛ_b) z^♮` with `d z^♮ = 0` and `z^♮` of degree
`0` is the same as a morphism of dg rings `φ : OΛ_{a+b} → OΛ_a ⊗ OΛ_b` (`z^♮ h = φ(h) z^♮`, `φ.Bimodule`).

**`natAction_unique`**: if the bimodule isomorphism exists for `φ`, then `φ` is the block swap
`h ↦ h(y, x)` (`EQFunctor.swapDG`), for which it exists (`EQFunctor.gEquiv`). In particular the inclusion
`OΛ_{a+b} ⊆ OΛ_a ⊗ OΛ_b`, `h ↦ h(x, y)`, and its composites with `w₀` on either block do not work.

The proof extracts from such an isomorphism `e` the map `Θ(t) = e(t ⊗ δ) · 1_z` into `Z_{a+b}` (`δ` the dual
basis vector of `1_z`), which is left linear along `ι`, right `OΛ_{a+b}`-linear up to the sign of the
regrading, and sends `(1_z ⊠ 1_z) ⊗ z^♮` to a nonzero multiple of `P^a 1_z` (a degree argument inside the
right ideal `P^a ONH_{a+b}`). Comparing with the same map for the block swap and cancelling `P^a` gives
`(1_z ⊠ 1_z) φ(h) = (1_z ⊠ 1_z) h(y, x)`, hence `φ(h) = h(y, x)`.
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

variable {a b : ℕ}

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

/-! ### A homogeneous injective map reflects degrees -/

theorem mem_grading_of_map_mem {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N]
    [DGAddCommGroup N] {k : ℤ} (f : M →+ N) (hf : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading (n + k))
    (hinj : ∀ m, f m = 0 → m = 0) {i : ℤ} {m : M} (hm : f m ∈ grading (i + k)) : m ∈ grading i := by
  classical
  have hcomp : ∀ j, j ≠ i → (DirectSum.decompose (DG.grading (M := M)) m j : M) = 0 := by
    intro j hj
    apply hinj
    rw [← DG.decompose_map f hf m j, DirectSum.decompose_of_mem_ne _ hm (by omega)]
  rw [← DirectSum.sum_support_decompose (DG.grading (M := M)) m]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  by_cases hj : j = i
  · subst hj; exact (DirectSum.decompose (DG.grading (M := M)) m j).2
  · rw [hcomp j hj]; exact zero_mem _

theorem zn_eq_of_zsmul_eq {N : ℕ} {c : ℤ} (hc : c ≠ 0) {z z' : Zn N} (h : c • z = c • z') : z = z' := by
  apply (zE N).symm.injective
  have h' := congrArg (zE N).symm h
  rw [map_zsmul, map_zsmul] at h'
  ext α
  have := congrArg (fun F : SkewPolynomial N => F α) h'
  simp only [Finsupp.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

/-! ### The underlying element of `ONH^♮` -/

/-- The element of `ONH_{a+b}` underlying an element of `ONH^♮_{a+b}`. -/
def natVal (m : ONHNat a b) : ONH (a + 2 + b) :=
  (show IONH a b from (((Regrade.mk (degP a b)).symm m : natSub a b) : IONH a b))

theorem natVal_add (m m' : ONHNat a b) : natVal (m + m') = natVal m + natVal m' := rfl

theorem natVal_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (m : ONHNat a b) : natVal (s • m) = ONH.iota a b s * natVal m :=
  rfl

theorem natVal_op_smul {k : ℤ} {g : ONH (a + 2 + b)} (hg : g ∈ DG.grading k) (m : ONHNat a b) :
    natVal (op g • m) = (koszulSign (degP a b * k) : ℤ) • (natVal m * g) := by
  have h := Regrade.op_smul_mk_of_mem (M := natSub a b) (n := degP a b) hg ((Regrade.mk (degP a b)).symm m)
  rw [AddEquiv.apply_symm_apply] at h
  rw [natVal, h, AddEquiv.symm_apply_apply, Units.smul_def]
  rfl

theorem natVal_mem {k : ℤ} {m : ONHNat a b} (hm : m ∈ DG.grading k) :
    natVal m ∈ DG.grading (k + degP a b) := hm

theorem natVal_eq_Pw_mul (m : ONHNat a b) : ∃ p : ONH (a + 2 + b), natVal m = Pw a b * p :=
  ((Regrade.mk (degP a b)).symm m).2

/-- `P^a` as an element of `ONH^♮`. -/
def natPw : ONHNat a b := Regrade.mk (degP a b) ⟨show IONH a b from Pw a b, ⟨1, (mul_one _).symm⟩⟩

theorem natVal_natPw : natVal (natPw (a := a) (b := b)) = Pw a b := rfl

/-! ### The map `Θ` attached to an isomorphism -/

/-- `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b}` for the right action through `φ`. -/
abbrev TTφ (φ : osymDG ((a + 2) + (b + 2)) →ᵈᵍ+* (Λa ᵍ⊗[ℤ] Λb)) : Type :=
  TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) φ.Bimodule

variable (a b) in
/-- `OΛ_a ⊗ OΛ_b`. -/
abbrev LAB : Type := Λa ᵍ⊗[ℤ] Λb

variable (a b) in
/-- `ONH_a ⊗ ONH_b`. -/
abbrev OAB : Type := 𝒪a ᵍ⊗[ℤ] 𝒪b

section Theta

variable (φ : osymDG ((a + 2) + (b + 2)) →ᵈᵍ+* LAB a b)

/-- `(1_z ⊠ 1_z) ⊗ z^♮`. -/
def t0φ : TTφ φ := TensorProductOver.tmul _ (yOne a b) (φ.bimoduleEquiv 1)

/-- The generator `1_z` of `Z_{a+b}`. -/
abbrev bzAB : Zn ((a + 2) + (b + 2)) := bz

theorem bzAB_mem : (bzAB (a := a) (b := b)) ∈ DG.grading (0 : ℤ) := bz_mem

/-- The dual basis vector of `1_z`. -/
abbrev δz : ZD a b := (znRightBasis ((a + 2) + (b + 2))).δ stair0

theorem toHom_δz_bz : RightDual.toHom (δz (a := a) (b := b)) (bzAB (a := a) (b := b)) = 1 := by
  rw [RightBasis.toHom_δ]; exact coeff_bz

theorem δz_mem : (δz (a := a) (b := b)) ∈ DG.grading (0 : ℤ) := by
  have h := (znRightBasis ((a + 2) + (b + 2))).δ_mem stair0
  have e : (znRightBasis ((a + 2) + (b + 2))).deg stair0 = 0 := by
    simp [znRightBasis, stair0, EQSkewDifferential.totalDeg]
  rwa [e, neg_zero] at h

variable (e : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TTφ φ) (ZD a b) ≃ᵈᵍ[OAB a b]
  ONHNat a b)
  (he : ∀ (g : ONH (a + 2 + b)) (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TTφ φ) (ZD a b)),
    e (op g • x) = op g • e x)

/-- `Θ(t) = e(t ⊗ δ) · 1_z ∈ Z_{a+b}`. -/
def thetaE (t : TTφ φ) : Zn ((a + 2) + (b + 2)) :=
  natVal (a := a) (b := b) (e (TensorProductOver.tmul _ t (δz (a := a) (b := b)))) • (bzAB (a := a) (b := b))

/-- Every element of `Z_{a+b}^∨` is `δ · ρ(1_z, f)`. -/
theorem eq_op_rho_smul_δz (f : ZD a b) : f = op ((hFull a b).rho (bzAB (a := a) (b := b)) f) • (δz (a := a) (b := b)) := by
  ext w
  rw [RightDual.toHom_op_smul, FullAction.rho_smul, RightDual.map_op_smul, toHom_δz_bz, one_mul]

include he in
theorem natVal_e_tmul_smul_bz (t : TTφ φ) {k : ℤ} {f : ZD a b} (hf : f ∈ DG.grading k) :
    natVal (a := a) (b := b) (e (TensorProductOver.tmul _ t f)) • (bzAB (a := a) (b := b)) =
      (koszulSign (degP a b * k) : ℤ) • (op (RightDual.toHom f (bzAB (a := a) (b := b))) • thetaE φ e t) := by
  have hρ : (hFull a b).rho (bzAB (a := a) (b := b)) f ∈ DG.grading k := by
    have := (hFull a b).rho_mem (bzAB_mem (a := a) (b := b)) hf; rwa [zero_add] at this
  conv_lhs => rw [eq_op_rho_smul_δz f, ← TensorProductOver.op_smul_tmul_right, he, natVal_op_smul hρ]
  rw [smul_assoc, mul_smul, FullAction.rho_smul, thetaE]
  congr 1
  exact smul_comm _ _ _

include he in
theorem thetaE_op_smul {k : ℤ} {h : osymDG ((a + 2) + (b + 2))} (hh : h ∈ DG.grading k) (t : TTφ φ) :
    thetaE φ e (op h • t) = (koszulSign (degP a b * k) : ℤ) • (op h • thetaE φ e t) := by
  have hf : h • (δz (a := a) (b := b)) ∈ DG.grading k := by
    have := DG.smul_mem_grading hh (δz_mem (a := a) (b := b)); rwa [add_zero] at this
  rw [thetaE, TensorProductOver.op_smul_tmul, natVal_e_tmul_smul_bz φ e he t hf, RightDual.toHom_smul,
    toHom_δz_bz, mul_one]

theorem thetaE_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (t : TTφ φ) : thetaE φ e (s • t) = ONH.iota a b s • thetaE φ e t := by
  rw [thetaE, thetaE, show TensorProductOver.tmul (osymDG ((a + 2) + (b + 2))) (s • t) (δz (a := a) (b := b)) =
    s • TensorProductOver.tmul (osymDG ((a + 2) + (b + 2))) t (δz (a := a) (b := b)) from rfl, map_smul,
    natVal_smul, mul_smul]

theorem thetaE_add (t t' : TTφ φ) : thetaE φ e (t + t') = thetaE φ e t + thetaE φ e t' := by
  rw [thetaE, thetaE, thetaE, TensorProductOver.add_tmul, map_add, natVal_add, add_smul]

theorem exists_smul_t0φ_tmul (y : ZZ a b) (r : φ.Bimodule) :
    ∃ s : 𝒪a ᵍ⊗[ℤ] 𝒪b, TensorProductOver.tmul _ y r = s • t0φ φ := by
  obtain ⟨r', rfl⟩ := φ.bimoduleEquiv.surjective r
  obtain ⟨s, hs⟩ := exists_smul_yOne (op r' • y)
  refine ⟨s, ?_⟩
  rw [t0φ, TensorProductOver.smul_tmul, ← hs, TensorProductOver.op_smul_tmul,
    DGRingHom.Bimodule.smul_bimoduleEquiv, mul_one]

theorem op_smul_t0φ (h : osymDG ((a + 2) + (b + 2))) {s : 𝒪a ᵍ⊗[ℤ] 𝒪b}
    (hs : s • yOne a b = op (φ h) • yOne a b) : op h • t0φ φ = s • t0φ φ := by
  rw [t0φ, TensorProductOver.op_smul_tmul_right, DGRingHom.Bimodule.op_smul_bimoduleEquiv, one_mul,
    show φ.bimoduleEquiv (φ h) = φ h • φ.bimoduleEquiv 1 by
      rw [DGRingHom.Bimodule.smul_bimoduleEquiv, mul_one],
    ← TensorProductOver.op_smul_tmul, ← hs, TensorProductOver.smul_tmul]

theorem t0φ_mem : t0φ φ ∈ DG.grading (0 : ℤ) := by
  have hy : yOne a b ∈ DG.grading (0 : ℤ) := by
    have := DG.tmul_mem_grading (M := Zn (a + 2)) (N := Zn (b + 2))
      (OPolAlpha.mem_grading_iff.mpr (by rw [AddEquiv.symm_apply_apply]; exact one_mem_grading'))
      (OPolAlpha.mem_grading_iff.mpr (by rw [AddEquiv.symm_apply_apply]; exact one_mem_grading'))
    rwa [add_zero] at this
  have := TensorProductOver.tmul_mem_grading (A := Λa ᵍ⊗[ℤ] Λb) hy
    ((DGRingHom.Bimodule.bimoduleEquiv_mem_grading_iff (φ := φ)).mpr (DG.one_mem_grading (A := Λa ᵍ⊗[ℤ] Λb)))
  rwa [add_zero] at this

theorem Pw_smul_mem {n : ℤ} {z : Zn ((a + 2) + (b + 2))} (hz : z ∈ DG.grading n) :
    Pw a b • z ∈ DG.grading (n + degP a b) := by
  have := DG.smul_mem_grading (Pw_mem (a := a) (b := b)) hz; rwa [add_comm (degP a b) n] at this

set_option maxHeartbeats 1000000 in
include he in
/-- **`Θ((1_z ⊠ 1_z) ⊗ z^♮) = m P^a 1_z` with `m ≠ 0`.** -/
theorem thetaE_t0φ : ∃ m : ℤ, m ≠ 0 ∧ thetaE φ e (t0φ φ) = m • zE _ (PA a b) := by
  have hx : TensorProductOver.tmul (osymDG ((a + 2) + (b + 2))) (t0φ φ) (δz (a := a) (b := b)) ∈ DG.grading (0 : ℤ) := by
    have := TensorProductOver.tmul_mem_grading (A := osymDG ((a + 2) + (b + 2))) (t0φ_mem φ) (δz_mem (a := a) (b := b))
    rwa [add_zero] at this
  obtain ⟨p, hp⟩ := natVal_eq_Pw_mul (e (TensorProductOver.tmul _ (t0φ φ) (δz (a := a) (b := b))))
  have hT : thetaE φ e (t0φ φ) = Pw a b • (p • (bzAB (a := a) (b := b))) := by rw [thetaE, hp, mul_smul]
  have hmem : Pw a b • (p • (bzAB (a := a) (b := b))) ∈ DG.grading (0 + degP a b) := by
    rw [← hT, thetaE]
    have := DG.smul_mem_grading (natVal_mem (e.map_mem hx)) (bzAB_mem (a := a) (b := b))
    rwa [add_zero] at this
  have h0 : p • (bzAB (a := a) (b := b)) ∈ DG.grading (0 : ℤ) :=
    mem_grading_of_map_mem (DistribSMul.toAddMonoidHom (Zn ((a + 2) + (b + 2))) (Pw a b)) (fun hm => Pw_smul_mem hm)
      (fun _ h => Pw_smul_eq_zero h) hmem
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (zE ((a + 2) + (b + 2))).symm (p • (bzAB (a := a) (b := b))) = m • 1 :=
    ⟨_, eq_smul_one_of_mem_grading_zero (OPolAlpha.mem_grading_iff.mp h0)⟩
  have hT' : thetaE φ e (t0φ φ) = m • zE _ (PA a b) := by
    rw [hT]
    apply (zE ((a + 2) + (b + 2))).symm.injective
    rw [zE_symm_Pw_smul, hm, map_zsmul, AddEquiv.symm_apply_apply, mul_smul_comm, sp_mul_one']
  refine ⟨m, fun hm0 => ?_, hT'⟩
  -- If `m = 0`, `Θ = 0`, so every `e(x)` kills `1_z`; but `e` is onto `P^a`.
  have hΘ : ∀ t, thetaE φ e t = 0 := fun t => by
    induction t using TensorProductOver.induction_on with
    | zero => rw [thetaE, TensorProductOver.zero_tmul, map_zero]; exact zero_smul _ _
    | tmul y r =>
      obtain ⟨s, hs⟩ := exists_smul_t0φ_tmul φ y r
      rw [hs, thetaE_smul, hT', hm0, zero_smul, smul_zero]
    | add t t' ht ht' => rw [thetaE_add, ht, ht', add_zero]
  have hall : ∀ x, natVal (a := a) (b := b) (e x) • (bzAB (a := a) (b := b)) = 0 := fun x => by
    induction x using TensorProductOver.induction_on with
    | zero => rw [map_zero]; exact zero_smul _ _
    | tmul t f =>
      induction f using DG.induction_on with
      | h_zero => rw [TensorProductOver.tmul_zero, map_zero]; exact zero_smul _ _
      | @h_homogeneous k f =>
        rw [natVal_e_tmul_smul_bz φ e he t f.2, hΘ, smul_zero, smul_zero]
      | h_add f f' hf hf' =>
        rw [TensorProductOver.tmul_add, map_add, natVal_add, add_smul, hf, hf', add_zero]
    | add x x' hx hx' => rw [map_add, natVal_add, add_smul, hx, hx', add_zero]
  obtain ⟨x, hx⟩ := e.surjective natPw
  have h1 := hall x
  rw [hx, natVal_natPw] at h1
  have h2 := congrArg (fun z => (znRightBasis ((a + 2) + (b + 2))).coeff z stair0) (Pw_smul_eq_zero h1)
  simp only [coeff_bz, RightBasis.coeff_zero, Pi.zero_apply] at h2
  have h3 := congrArg (fun x : osymDG ((a + 2) + (b + 2)) => (OPol.equiv ((a + 2) + (b + 2))).symm (x : OPol ((a + 2) + (b + 2)))) h2
  simp only [OneMemClass.coe_one, ZeroMemClass.coe_zero, map_one, map_zero] at h3
  exact one_ne_zero (α := SkewPolynomial ((a + 2) + (b + 2))) h3

end Theta

/-! ### Uniqueness -/

theorem iota_smul_PA_eq (φ : osymDG ((a + 2) + (b + 2)) →ᵈᵍ+* LAB a b)
    (e : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TTφ φ) (ZD a b) ≃ᵈᵍ[𝒪a ᵍ⊗[ℤ] 𝒪b] ONHNat a b)
    (he : ∀ (g : ONH (a + 2 + b)) (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TTφ φ) (ZD a b)),
      e (op g • x) = op g • e x)
    {k : ℤ} {h : osymDG ((a + 2) + (b + 2))} (hh : h ∈ DG.grading k) {s : 𝒪a ᵍ⊗[ℤ] 𝒪b}
    (hs : s • yOne a b = op (φ h) • yOne a b) :
    ONH.iota a b s • zE ((a + 2) + (b + 2)) (PA a b) =
      (koszulSign (degP a b * k) : ℤ) • (op h • zE ((a + 2) + (b + 2)) (PA a b)) := by
  obtain ⟨m, hm0, hm⟩ := thetaE_t0φ φ e he
  have h1 := thetaE_op_smul φ e he hh (t0φ φ)
  rw [op_smul_t0φ φ h hs, thetaE_smul, hm] at h1
  apply zn_eq_of_zsmul_eq hm0
  rw [← smul_comm, h1, smul_comm (op h) m, smul_comm _ m]

theorem rHat_injective : Function.Injective (rHat (a := a) (b := b)) := fun r r' h => by
  apply tensorToOsymAB_injective (a := a + 2) (b := b + 2)
  apply Subtype.ext
  have h' := congrArg (OPol.equiv ((a + 2) + (b + 2))) h
  rw [rHat, rHat, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at h'
  rw [coe_tensorToOsymAB, coe_tensorToOsymAB]
  exact h'

theorem PA_mul_cancel {X X' : SkewPolynomial ((a + 2) + (b + 2))} (h : X * PA a b = X' * PA a b) : X = X' := by
  rw [mul_PA_eq, mul_PA_eq] at h
  have h0 : topY (a + 2) (b + 2) ^ (a + 2) * (chi a b X - chi a b X') = 0 := by
    change PA a b * (chi a b X - chi a b X') = 0
    rw [show ∀ X Y Z : SkewPolynomial ((a + 2) + (b + 2)), X * (Y - Z) = X * Y - X * Z from
      fun X Y Z => by rw [sub_eq_add_neg, mul_add, mul_neg, ← sub_eq_add_neg], h, sub_self]
  have h1 := sub_eq_zero.mp (topY_pow_mul_eq_zero (a + 2) h0)
  have h2 := congrArg (chi a b) h1
  rwa [chi_chi, chi_chi] at h2

/-- **The right action on `Z^♮_{a,b}` is forced** (Definition 4.15, Corollary 4.21, ranks `a + 2`, `b + 2`):
if, for `OΛ_{a+b}` acting on `Z^♮_{a,b} = OΛ_a ⊗ OΛ_b` through a morphism of dg rings `φ`, there is an
isomorphism of dg `(ONH_a ⊗ ONH_b, ONH_{a+b})`-bimodules
`((Z_a ⊠ Z_b) ⊗ Z^♮_{a,b}) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ ≅ ONH^♮_{a+b}`, then `φ` is the block swap `h ↦ h(y, x)`. -/
theorem natAction_unique (φ : osymDG ((a + 2) + (b + 2)) →ᵈᵍ+* LAB a b)
    (e : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TTφ φ) (ZD a b) ≃ᵈᵍ[𝒪a ᵍ⊗[ℤ] 𝒪b] ONHNat a b)
    (he : ∀ (g : ONH (a + 2 + b)) (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TTφ φ) (ZD a b)),
      e (op g • x) = op g • e x)
    (h : osymDG ((a + 2) + (b + 2))) : φ h = swapDG a b h := by
  induction h using DG.induction_on with
  | h_zero => rw [map_zero, map_zero]
  | @h_homogeneous k h =>
    obtain ⟨s, hs⟩ := exists_smul_yOne (op (φ h) • yOne a b)
    obtain ⟨s', hs'⟩ := exists_smul_yOne (op (swapDG a b h) • yOne a b)
    have h1 := iota_smul_PA_eq φ e he h.2 hs.symm
    have h2 := iota_smul_PA_eq (swapDG a b) (gEquiv a b) (fun g x => gEquiv_op_smul g x) h.2 hs'.symm
    have h3 := h1.trans h2.symm
    have h4 : (zE _).symm (ONH.iota a b s • zE ((a + 2) + (b + 2)) 1) * PA a b =
        (zE _).symm (ONH.iota a b s' • zE ((a + 2) + (b + 2)) 1) * PA a b := by
      rw [← zE_symm_iota_smul_mul s 1 (PA a b) blockSym_PA, ← zE_symm_iota_smul_mul s' 1 (PA a b) blockSym_PA,
        sp_one_mul', h3]
    have h5 := (zE ((a + 2) + (b + 2))).symm.injective (PA_mul_cancel h4)
    rw [← polyHom_yOne (a := a) (b := b), ← zE_polyHom_smul, ← zE_polyHom_smul, ← hs, ← hs'] at h5
    have h6 := (zE ((a + 2) + (b + 2))).injective h5
    rw [polyHom_op_smul, polyHom_op_smul, polyHom_yOne, sp_one_mul', sp_one_mul'] at h6
    have h7 := congrArg (fun F => blockRev (a + 2) (b + 2) (EQZab.tauAB (a + 2) (b + 2) F)) h6
    simp only [EQZab.tauAB_tauAB, blockRev_blockRev] at h7
    exact rHat_injective h7
  | h_add h h' ih ih' => rw [map_add, map_add, ih, ih']

/-! ### The inclusion `OΛ_{a+b} ⊆ OΛ_a ⊗ OΛ_b` does not work (`a = b = 2`) -/

variable (a b) in
/-- `OΛ_{a+b} → OΛ_a ⊗ OΛ_b`, `h ↦ h(x, y)` (the inclusion). -/
def inclTensor : osymDG ((a + 2) + (b + 2)) →ᵈᵍ+* LAB a b :=
  (tensorEquivOsymAB (a + 2) (b + 2)).symm.toDGAlgHom.toDGRingHom.comp (inclDG (a + 2) (b + 2))

theorem swapPoly_two : swapPoly 2 2 = permPoly (swapPerm 2) :=
  ringHom_ext fun j => by
    rw [swapPoly_generator, permPoly_generator]
    congr 1
    fin_cases j <;> rfl

/-- **For `a = b = 2` the inclusion `h ↦ h(x, y)` does not give the restriction half**: the witness is
`h = e_2`, with `e_2(x, y) - e_2(y, x) = 2 e_1(x) e_1(y)`. -/
theorem no_resIso_incl :
    ¬ ∃ e : TensorProductOver (osymDG ((0 + 2) + (0 + 2))) (TTφ (inclTensor 0 0)) (ZD 0 0) ≃ᵈᵍ[
        DGAlgebra.gradingSubmodule ℤ (ONH 0) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (ONH 0)] ONHNat 0 0,
      ∀ (g : ONH (0 + 2 + 0)) (x : TensorProductOver (osymDG ((0 + 2) + (0 + 2))) (TTφ (inclTensor 0 0)) (ZD 0 0)),
        e (op g • x) = op g • e x := by
  rintro ⟨e, he⟩
  have h := natAction_unique (inclTensor 0 0) e he ⟨OPol.equiv _ (elementary _ 2), elementary_mem_osymDG 2⟩
  have h1 := congrArg (fun r => rHat r) h
  rw [rHat_swapDG] at h1
  have h2 : rHat (inclTensor 0 0 ⟨OPol.equiv _ (elementary _ 2), elementary_mem_osymDG 2⟩) =
      elementary ((0 + 2) + (0 + 2)) 2 := by
    rw [rHat, ← coe_tensorToOsymAB]
    change (OPol.equiv ((0 + 2) + (0 + 2))).symm (((tensorToOsymAB (0 + 2) (0 + 2)
      ((tensorEquivOsymAB (0 + 2) (0 + 2)).symm (inclDG (0 + 2) (0 + 2) _)) : osymABDG (0 + 2) (0 + 2)) :
        OPol ((0 + 2) + (0 + 2)))) = _
    rw [← tensorEquivOsymAB_apply, DGAlgEquiv.apply_symm_apply, coe_inclDG, RingEquiv.symm_apply_apply]
  rw [h2, toSkew_e2] at h1
  have hk := congrArg (kap π02) h1
  obtain ⟨_, _, _, _, _, _, _, _, h9, h10, h11, h12⟩ := kap_values
  rw [show swapPoly (0 + 2) (0 + 2) = permPoly (swapPerm 2) from swapPoly_two, e2_decomp] at hk
  simp only [map_add, map_mul, sX2, sY2, sX1, sY1] at hk
  simp only [h9, h10, h11, h12] at hk
  norm_num at hk

end OddMath.Frontier.EQFunctor
