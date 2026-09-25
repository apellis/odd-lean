import OddMath.Frontier.EKAntipode
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! EK1107.5610v2 pp20–21 infinite orders and the faithful infinite dihedral
subgroup of the actual integral quotient. Composition is pointwise; reflections
are psi2 after integer powers of psi1. S remains the inherited LINEAR antipode.
No claim is made in positive characteristic or about the larger SAut group. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace OddMath.Frontier.EKInfiniteSymmetry
open EKRadicalQuotient (Q)
open EKElementaryQuotient (h)
open EKPresentation (psi1)
open EKAutomorphisms (psi2)
open EKAntipode (S)
theorem psi1_h_one : psi1 (h 1) = h 1 := by
  rw [EKPresentation.psi1_h, EKPresentationControls.degree_one]
theorem psi1_h_two : psi1 (h 2) = h 2-h 1*h 1 := by
  rw [EKPresentation.psi1_h, EKPresentationControls.degree_two]
theorem psi2_h_one : psi2 (h 1) = -h 1 :=
  EKAutomorphismsControls.psi2_generator_controls.2.1
theorem psi2_h_two : psi2 (h 2) = -h 2 :=
  EKAutomorphismsControls.psi2_generator_controls.2.2.1

theorem composition_apply (a b : Q ≃+* Q) (x : Q) : (a*b) x = a (b x) := rfl

theorem conjugation : psi2*psi1*psi2 = psi1⁻¹ := by
  ext x
  exact EKAutomorphisms.psi2_psi1_psi2 x


/-- Actual integral h-basis coordinate detects every multiple of h1². -/
theorem square_smul_injective : Function.Injective (fun z : ℤ => z • (h 1*h 1)) := by
  intro a b hab
  have he := congrArg (fun x : Q => EKIntegralBases.hBasis.repr x EKIntegralBasesControls.col2) hab
  dsimp only at he
  rw [← EKIntegralBasesControls.col2_value, map_smul, map_smul,
    EKIntegralBases.h_coordinates_partition] at he
  simpa using he

theorem square_ne_zero : h 1*h 1 ≠ 0 := by
  intro he
  have hh : (1 : ℤ) = 0 := square_smul_injective (by simp [he])
  norm_num at hh

theorem h_one_ne_zero : h 1 ≠ 0 := by
  intro he
  exact square_ne_zero (by rw [he, zero_mul])

theorem h_one_ne_neg : h 1 ≠ -h 1 := by
  intro he
  have hh := congrArg (fun x : Q => x*h 1) he
  dsimp only at hh
  rw [neg_mul] at hh
  exact EKAutomorphismsControls.super_square_not_ordinary hh.symm

theorem translation_injective : Function.Injective (fun z : ℤ => h 2-z • (h 1*h 1)) := by
  intro a b hab
  exact square_smul_injective (sub_right_injective hab)

@[simp] theorem psi1_square : psi1 (h 1*h 1) = h 1*h 1 := by
  rw [map_mul, psi1_h_one]

theorem psi1_iterate_h_two (k : ℕ) :
    (psi1^[k]) (h 2) = h 2-(k : ℤ) • (h 1*h 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_sub, map_zsmul, psi1_h_two, psi1_square,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

theorem psi1_pow_apply (k : ℕ) (x : Q) : (psi1^k) x = (psi1^[k]) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', composition_apply, ih, Function.iterate_succ_apply']

theorem psi1_infinite_order : orderOf psi1 = 0 := by
  rw [orderOf_eq_zero_iff']
  intro k hk he
  have hh := congrArg (fun f : Q ≃+* Q => f (h 2)) he
  dsimp only at hh
  rw [psi1_pow_apply, psi1_iterate_h_two] at hh
  change h 2-(k : ℤ) • (h 1*h 1) = h 2 at hh
  have hz : (k : ℤ) = 0 := translation_injective (by simpa only [zero_smul, sub_zero] using hh)
  exact (Nat.ne_of_gt hk) (Int.ofNat_eq_zero.mp hz)

theorem S_even_iterate_h_two (k : ℕ) :
    (S^[2*k]) (h 2) = h 2-(2*(k : ℤ)) • (h 1*h 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)=2+(2*k) by omega, Function.iterate_add_apply, ih]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      map_sub, map_smul, EKAntipode.S_square_word, map_neg, neg_neg,
      EKAntipode.S_square_h_two, Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_smul]
    abel

theorem S_even_orbit_injective : Function.Injective (fun k : ℕ => (S^[2*k]) (h 2)) := by
  intro i j he
  simp only [S_even_iterate_h_two] at he
  have hh := translation_injective he
  omega

theorem S_no_positive_iterate (k : ℕ) (hk : 0 < k) : (S^[k]) ≠ id := by
  intro he
  have hh : (S^[2*k]) (h 2) = h 2 := by
    rw [two_mul, Function.iterate_add_apply, he]
    rfl
  have hz : k = 0 := S_even_orbit_injective (by simpa using hh)
  omega

/-- Integer powers are needed for the ACTUAL dihedral action, not just naturals. -/
theorem psi1_inverse_h_one : psi1⁻¹ (h 1) = h 1 := by
  apply psi1.injective
  change psi1 (psi1.symm (h 1)) = psi1 (h 1)
  rw [RingEquiv.apply_symm_apply, psi1_h_one]

theorem psi1_inverse_h_two : psi1⁻¹ (h 2) = h 2+h 1*h 1 := by
  apply psi1.injective
  change psi1 (psi1.symm (h 2)) = psi1 (h 2+h 1*h 1)
  rw [RingEquiv.apply_symm_apply, map_add, psi1_h_two, psi1_square, sub_add_cancel]

theorem rotation_values (i : ℤ) :
    (psi1^i) (h 1) = h 1 ∧ (psi1^i) (h 2) = h 2-i • (h 1*h 1) := by
  refine Int.induction_on i (by simp only [zpow_zero, zero_smul, sub_zero]; exact ⟨rfl, rfl⟩) ?_ ?_
  · intro n ih
    rw [zpow_add_one]
    constructor
    · change (psi1^(n : ℤ)) (psi1 (h 1)) = _
      rw [psi1_h_one, ih.1]
    · change (psi1^(n : ℤ)) (psi1 (h 2)) = _
      rw [psi1_h_two, map_sub, map_mul, ih.1, ih.2, add_smul, one_smul]
      abel
  · intro n ih
    rw [zpow_sub_one]
    constructor
    · change (psi1^(-(n : ℤ))) (psi1⁻¹ (h 1)) = _
      rw [psi1_inverse_h_one, ih.1]
    · change (psi1^(-(n : ℤ))) (psi1⁻¹ (h 2)) = _
      rw [psi1_inverse_h_two, map_add, map_mul, ih.1, ih.2, sub_smul, one_smul]
      abel

@[simp] theorem rotation_h_one (i : ℤ) : (psi1^i) (h 1) = h 1 := (rotation_values i).1
@[simp] theorem rotation_h_two (i : ℤ) :
    (psi1^i) (h 2) = h 2-i • (h 1*h 1) := (rotation_values i).2

theorem rotation_injective : Function.Injective (fun i : ℤ => psi1^i) := by
  intro i j he
  have hh := congrArg (fun f : Q ≃+* Q => f (h 2)) he
  exact translation_injective (by simpa only [rotation_h_two] using hh)

@[simp] theorem psi2_mul_self : psi2*psi2 = 1 := by
  ext x
  exact EKAutomorphisms.psi2_involutive x

theorem rotation_cross (i : ℤ) : psi1^i*psi2 = psi2*psi1^(-i) := by
  have hs : SemiconjBy psi2 psi1 (psi1⁻¹) := by
    change psi2*psi1 = psi1⁻¹*psi2
    calc
      _ = (psi2*psi1*psi2)*psi2 := by rw [mul_assoc, mul_assoc, psi2_mul_self, mul_one]
      _ = _ := by rw [conjugation]
  simpa only [inv_zpow, zpow_neg, inv_inv] using (hs.zpow_right (-i)).symm

-- Explicit integer domain prevents power elaboration choosing exponent type ZMod 0.
def rotation (i : ℤ) : Q ≃+* Q := psi1^i

/-- Rotations r_i map to psi1^i; sr_i maps to psi2 AFTER psi1^i. -/
def rho : DihedralGroup 0 →* (Q ≃+* Q) where
  toFun
    | .r i => rotation i
    | .sr i => psi2*rotation i
  map_one' := by change psi1^(0 : ℤ) = 1; exact zpow_zero _
  map_mul' := by
    rintro (i | i) (j | j)
    all_goals change ℤ at i j
    · change psi1^((i : ℤ)+j) = psi1^i*psi1^j
      exact zpow_add _ _ _
    · change psi2*psi1^((j : ℤ)-i) = psi1^i*(psi2*psi1^j)
      rw [← mul_assoc, rotation_cross, mul_assoc, ← zpow_add]
      congr 1
      congr 1
      omega
    · change psi2*psi1^((i : ℤ)+j) = (psi2*psi1^i)*psi1^j
      rw [zpow_add, mul_assoc]
    · change psi1^((j : ℤ)-i) = (psi2*psi1^i)*(psi2*psi1^j)
      rw [mul_assoc, ← mul_assoc (psi1^i), rotation_cross,
        mul_assoc psi2 (psi1^(-i)), ← mul_assoc psi2 psi2,
        psi2_mul_self, one_mul, ← zpow_add]
      congr 1
      omega

@[simp] theorem rho_r (i : ℤ) : rho (.r i) = psi1^i := rfl
@[simp] theorem rho_sr (i : ℤ) : rho (.sr i) = psi2*psi1^i := rfl
@[simp] theorem rho_r_one : rho (.r 1) = psi1 := by simp
@[simp] theorem rho_sr_zero : rho (.sr 0) = psi2 := by simp

theorem reflection_h_one (i : ℤ) : (psi2*psi1^i) (h 1) = -h 1 := by
  rw [composition_apply, rotation_h_one, psi2_h_one]

theorem reflection_h_two (i : ℤ) :
    (psi2*psi1^i) (h 2) = -h 2-i • (h 1*h 1) := by
  rw [composition_apply, rotation_h_two, map_sub, map_zsmul,
    map_mul, psi2_h_two, psi2_h_one, neg_mul_neg]

theorem rotation_ne_reflection (i j : ℤ) : psi1^i ≠ psi2*psi1^j := by
  intro he
  apply h_one_ne_neg
  have hh := congrArg (fun f : Q ≃+* Q => f (h 1)) he
  simpa only [rotation_h_one, reflection_h_one] using hh

theorem rho_injective : Function.Injective rho := by
  rintro (i | i) (j | j) he
  · exact congrArg DihedralGroup.r (rotation_injective he)
  · exact (rotation_ne_reflection i j he).elim
  · exact (rotation_ne_reflection j i he.symm).elim
  · exact congrArg DihedralGroup.sr (rotation_injective (mul_left_cancel he))

/-- The subgroup is the closure of the TWO ACTUAL inherited generators. -/
def generated : Subgroup (Q ≃+* Q) := Subgroup.closure {psi1, psi2}

theorem psi1_mem : psi1 ∈ generated := Subgroup.subset_closure (by simp)
theorem psi2_mem : psi2 ∈ generated := Subgroup.subset_closure (by simp)

theorem rho_mem (g : DihedralGroup 0) : rho g ∈ generated := by
  cases g with
  | r i => exact generated.zpow_mem psi1_mem i
  | sr i => exact generated.mul_mem psi2_mem (generated.zpow_mem psi1_mem i)

theorem range_eq_generated : rho.range = generated := by
  apply le_antisymm
  · rintro f ⟨g, rfl⟩
    exact rho_mem g
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases (show f = psi1 ∨ f = psi2 from by simpa using hf) with rfl | rfl
    · exact ⟨.r 1, rho_r_one⟩
    · exact ⟨.sr 0, rho_sr_zero⟩

def rhoGenerated : DihedralGroup 0 →* generated where
  toFun g := ⟨rho g, rho_mem g⟩
  map_one' := Subtype.ext rho.map_one
  map_mul' a b := Subtype.ext (rho.map_mul a b)

/-- Faithful normal-form realization of the source's Z/2 * Z/2 claim. -/
def dihedralEquiv : DihedralGroup 0 ≃* generated :=
  MulEquiv.ofBijective rhoGenerated ⟨
    fun _ _ he => rho_injective (congrArg Subtype.val he),
    fun f => by
      have hf : f.val ∈ rho.range := range_eq_generated.symm ▸ f.property
      obtain ⟨g, hg⟩ := hf
      exact ⟨g, Subtype.ext hg⟩⟩

@[simp] theorem dihedralEquiv_apply (g : DihedralGroup 0) :
    (dihedralEquiv g).val = rho g := rfl

/-- Every element has one and only one tagged integer rotation/reflection form.
The Boolean tag is false for rotations and true for psi2-after-rotation. -/
theorem unique_normal_form (f : generated) :
    ∃! p : Bool × ℤ, f.val = if p.1 then psi2*psi1^p.2 else psi1^p.2 := by
  obtain ⟨g, hg⟩ := dihedralEquiv.surjective f
  have he : rho g = f.val := congrArg Subtype.val hg
  cases g with
  | r i =>
    refine ⟨(false, i), he.symm, ?_⟩
    rintro ⟨b,j⟩ hp
    cases b with
    | false =>
      have hj : j = i := rotation_injective (hp.symm.trans he.symm)
      simp [hj]
    | true => exact (rotation_ne_reflection i j (he.trans hp)).elim
  | sr i =>
    refine ⟨(true, i), he.symm, ?_⟩
    rintro ⟨b,j⟩ hp
    cases b with
    | false => exact (rotation_ne_reflection j i (hp.symm.trans he.symm)).elim
    | true =>
      have hj : j = i := rotation_injective (mul_left_cancel (hp.symm.trans he.symm))
      simp [hj]

/-- Normal-form consumer exposes the actual actions and a UNIQUE exponent;
no cardinality-only or abstract-presentation surrogate. -/
theorem normal_form_action (f : generated) :
    (∃! i : ℤ, f.val = psi1^i) ∧ f.val (h 1) = h 1 ∨
    (∃! i : ℤ, f.val = psi2*psi1^i) ∧ f.val (h 1) = -h 1 := by
  obtain ⟨⟨b,i⟩, hi, _⟩ := unique_normal_form f
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hi
    left
    refine ⟨⟨i, hi, fun j hj => rotation_injective (hj.symm.trans hi)⟩, ?_⟩
    rw [hi, rotation_h_one]
  | true =>
    simp only [↓reduceIte] at hi
    right
    refine ⟨⟨i, hi, fun j hj => rotation_injective (mul_left_cancel (hj.symm.trans hi))⟩, ?_⟩
    rw [hi, reflection_h_one]

end OddMath.Frontier.EKInfiniteSymmetry
