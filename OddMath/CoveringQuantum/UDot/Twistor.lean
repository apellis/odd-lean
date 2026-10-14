/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.Gauge
import OddMath.CoveringQuantum.UDot.RootCoordinates
import OddMath.CoveringQuantum.Twistor.Serre

/-!
# The twistor isomorphism of `U̇` between `π = -1` and `π = 1`

Supporting material for Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1. For a bar-consistent
datum, an ordering of `I` and a unit `t` with `t² = -1`, rescaling the Chevalley generators by
signs and powers of `t` is an algebra isomorphism `U̇_{q,-1}(𝔤) ≅ U̇_{tq,1}(𝔤)` fixing every
`1_λ`. The signs need integer coordinates `β(λ) ∈ ℤ[I]` of the weights in the direction of the
simple roots (`β(λ + αⱼ) = β(λ) + j`), e.g. the root coordinates of a datum with linearly
independent simple roots. With `εᵢⱼ = (αᵢ, αⱼ)/2 + |i||j|` and `gᵢ(λ) = Σ_{j<i} εᵢⱼ β(λ)ⱼ`,
```
eᵢ1_λ ↦ (-1)^{gᵢ(λ)} eᵢ1_λ,   fᵢ1_λ ↦ t^{2|i| + dᵢ(3-⟨hᵢ,λ⟩)} (-1)^{gᵢ(λ-αᵢ)} fᵢ1_λ.
```
The isomorphism commutes with the antiautomorphisms `ρ` of (9.8) at the two signs, and the
rescaling of positive words is compatible with the twisting comparison `form_freeTwist` of the
free half-algebra forms.

## Main definitions

* `SuperCartanDatum.twistEpsilon`: `εᵢⱼ`; `UDot.twistExp`: `gᵢ(λ)`.
* `UDot.twistE`, `UDot.twistF`: the rescaling units.
* `UDot.twistor`: the isomorphism; `UDot.twistorAdjoint`: `ρ ∘ twistor ∘ ρ`.

## Main results

* `UDot.qpInt_twist`: `[n]_{q,u²} = u^{1-n} [n]_{uq,1}` for `u⁴ = 1`.
* `UDot.twistor_E`, `UDot.twistor_F`, `UDot.twistor_halfWord_true`.
* `UDot.twistorAdjoint_E`, `UDot.twistorAdjoint_F`, `UDot.twistorAdjoint_eq`,
  `UDot.rho_twistor`.
* `UDot.form_twist_monomial`: the free forms at the two signs agree after rescaling the words
  by the phases of the twistor.
-/

noncomputable section

namespace OddMath.CoveringQuantum

namespace SuperCartanDatum

variable {I : Type*} (C : SuperCartanDatum I)

/-- `εᵢⱼ = (αᵢ, αⱼ)/2 + |i||j|`. -/
def twistEpsilon (i j : I) : ℤ := C.dot i j / 2 + (C.parity i).val * (C.parity j).val

theorem twistEpsilon_comm (i j : I) : C.twistEpsilon i j = C.twistEpsilon j i := by
  rw [twistEpsilon, twistEpsilon, C.dot_comm, mul_comm]

theorem two_mul_twistEpsilon (hC : C.BarConsistent) (i j : I) :
    2 * C.twistEpsilon i j = C.dot i j + 2 * (C.parity i).val * (C.parity j).val := by
  have h := Int.mul_ediv_cancel' (even_iff_two_dvd.mp (C.even_dot_of_barConsistent hC i j))
  rw [twistEpsilon]
  linear_combination h

theorem parity_val_cases (i : I) : (C.parity i).val = 0 ∨ (C.parity i).val = 1 := by
  have := ZMod.val_lt (C.parity i)
  omega

theorem d_mod_two (hC : C.BarConsistent) (i : I) : C.d i % 2 = (C.parity i).val := by
  have hm := congrArg ZMod.val (hC i)
  simpa only [ZMod.val_natCast] using hm

theorem d_eq_parity_add (hC : C.BarConsistent) (i : I) :
    ∃ c : ℤ, (C.d i : ℤ) = 2 * c + (C.parity i).val := by
  have := C.d_mod_two hC i
  exact ⟨(C.d i / 2 : ℕ), by omega⟩

theorem parity_mul_val (i j : I) :
    ((C.parity i * C.parity j).val : ℤ) = (C.parity i).val * (C.parity j).val := by
  rw [ZMod.val_mul]
  rcases C.parity_val_cases i with h | h <;> rcases C.parity_val_cases j with h' | h' <;>
    simp [h, h']

end SuperCartanDatum

/-- `[n]_{q,u²} = u^{1-n} [n]_{uq,1}` for `u⁴ = 1` and every `n ∈ ℤ`. -/
theorem qpInt_twist {k : Type*} [CommRing k] (q u : kˣ) (hu : u ^ 4 = 1) (n : ℤ) :
    qpInt q ((u : k) ^ 2) n = ((u ^ (1 - n) : kˣ) : k) * qpInt (u * q) 1 n := by
  have hn (m : ℕ) : qpNat (u * q) 1 m =
      ((u ^ ((m : ℤ) - 1) : kˣ) : k) * qpNat q ((u : k) ^ 2) m := by
    have := qpBinom_twist q u hu m 1
    simpa only [qpBinom_one_right, Nat.cast_one, one_mul] using this
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [qpInt_ofNat, qpInt_ofNat, hn, ← mul_assoc, ← Units.val_mul, ← zpow_add,
      show (1 - (m : ℤ)) + ((m : ℤ) - 1) = 0 by ring, zpow_zero, Units.val_one, one_mul]
  · rw [qpInt_neg_natCast, qpInt_neg_natCast, hn, one_pow, one_mul]
    have h : ((u : k) ^ 2) ^ m = ((u ^ (1 - -(m : ℤ)) * u ^ ((m : ℤ) - 1) : kˣ) : k) := by
      rw [← zpow_add, show (1 - -(m : ℤ)) + ((m : ℤ) - 1) = ((2 * m : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    rw [h, Units.val_mul]
    ring

namespace UDot

variable {L I X : Type*} [CommRing L] [AddCommGroup X] [LinearOrder I]
variable (D : RootDatum I X) (β : X → I →₀ ℤ)

/-- `gᵢ(λ) = Σ_{j<i} εᵢⱼ β(λ)ⱼ`. -/
def twistExp (i : I) (μ : X) : ℤ :=
  (β μ).sum fun j n ↦ if j < i then D.twistEpsilon i j * n else 0

/-- The increment of `gᵢ` along `αⱼ`: `εᵢⱼ` if `j < i`, else `0`. -/
def twistShift (i j : I) : ℤ := if j < i then D.twistEpsilon i j else 0

variable {β}
variable (hβ : ∀ μ j, β (μ + D.α j) = β μ + Finsupp.single j 1)
include hβ

theorem twistExp_add_α (i j : I) (μ : X) :
    twistExp D β i (μ + D.α j) = twistExp D β i μ + twistShift D i j := by
  rw [twistExp, hβ, Finsupp.sum_add_index' (by intro a; simp) (by intro a b c; split_ifs <;> ring),
    Finsupp.sum_single_index (by simp)]
  simp [twistExp, twistShift]

theorem twistExp_sub_α (i j : I) (μ : X) :
    twistExp D β i (μ - D.α j) = twistExp D β i μ - twistShift D i j := by
  have := twistExp_add_α D hβ i j (μ - D.α j)
  rw [sub_add_cancel] at this
  linarith

theorem twistExp_add_nsmul (i j : I) (μ : X) (n : ℕ) :
    twistExp D β i (μ + n • D.α j) = twistExp D β i μ + n * twistShift D i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ← add_assoc, twistExp_add_α D hβ, ih]
    push_cast; ring

theorem twistExp_sub_nsmul (i j : I) (μ : X) (n : ℕ) :
    twistExp D β i (μ - n • D.α j) = twistExp D β i μ - n * twistShift D i j := by
  have := twistExp_add_nsmul D hβ i j (μ - n • D.α j) n
  rw [sub_add_cancel] at this
  linarith

omit hβ

@[simp] theorem twistShift_self (i : I) : twistShift D i i = 0 := by simp [twistShift]

theorem twistShift_add {i j : I} (hij : i ≠ j) :
    twistShift D i j + twistShift D j i = D.twistEpsilon i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [twistShift, h, not_lt_of_gt h, D.twistEpsilon_comm j i]
  · simp [twistShift, h, not_lt_of_gt h]

variable (β)

/-- The rescaling unit of `eᵢ1_λ`: `(-1)^{gᵢ(λ)}`. -/
def twistE (i : I) (μ : X) : Lˣ := (-1 : Lˣ) ^ twistExp D β i μ

/-- The rescaling unit of `fᵢ1_λ`: `t^{2|i| + dᵢ(3-⟨hᵢ,λ⟩)} (-1)^{gᵢ(λ-αᵢ)}`. -/
def twistF (t : Lˣ) (i : I) (μ : X) : Lˣ :=
  t ^ (2 * ((D.parity i).val : ℤ) + D.d i * (3 - D.h i μ)) *
    (-1 : Lˣ) ^ twistExp D β i (μ - D.α i)

variable {β}
variable {t : Lˣ} (ht : t ^ 2 = -1)
include ht

theorem neg_one_units_eq : (-1 : Lˣ) = t ^ (2 : ℤ) := by rw [← ht, zpow_ofNat]

theorem twistE_eq (i : I) (μ : X) : twistE (L := L) D β i μ = t ^ (2 * twistExp D β i μ) := by
  rw [twistE, neg_one_units_eq ht, ← zpow_mul]

theorem twistF_eq (i : I) (μ : X) : twistF D β t i μ =
    t ^ (2 * ((D.parity i).val : ℤ) + D.d i * (3 - D.h i μ) + 2 * twistExp D β i (μ - D.α i)) := by
  rw [twistF, neg_one_units_eq ht, ← zpow_mul, ← zpow_add]

theorem neg_one_pow_eq (n : ℕ) : (-1 : L) ^ n = ((t ^ (2 * (n : ℤ)) : Lˣ) : L) := by
  rw [zpow_mul, ← neg_one_units_eq ht, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]

theorem twist_phase_eq {a b : ℤ} (c : ℤ) (h : a = b + 4 * c) : t ^ a = t ^ b := by
  have ht4 : t ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((2 * 2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_mul, ht]; simp
  rw [h, zpow_add, zpow_mul, ht4, one_zpow, mul_one]

omit ht in
theorem twist_fourth (ht : t ^ 2 = -1) (n : ℕ) : (t ^ n) ^ 4 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, show 4 = 2 * 2 by rfl, pow_mul, ht]; simp

include hβ

theorem ePowPhase_twistE (i : I) (n : ℕ) (ν : X) :
    ePowPhase D (twistE D β) i n ν = t ^ (2 * (n * twistExp D β i ν)) := by
  induction n with
  | zero => simp [ePowPhase]
  | succ n ih =>
    rw [ePowPhase, ih, twistE_eq D ht, twistExp_add_nsmul D hβ, twistShift_self, ← zpow_add]
    congr 1
    push_cast; ring

theorem fPowPhase_twistF (i : I) (n : ℕ) (ν : X) :
    fPowPhase D (twistF D β t) i n ν =
      t ^ (n * (2 * ((D.parity i).val : ℤ) + D.d i * (3 - D.h i ν) + 2 * twistExp D β i ν) +
        D.d i * (n * (n - 1))) := by
  induction n with
  | zero => simp [fPowPhase]
  | succ n ih =>
    rw [fPowPhase, ih, twistF_eq D ht, twistExp_sub_α D hβ, twistExp_sub_nsmul D hβ,
      twistShift_self, h_sub_nsmul, D.isGCM.diag, ← zpow_add]
    congr 1
    push_cast; ring

variable {D}
variable (q) (hC : D.BarConsistent)
include hC

omit hβ in
theorem serreCoeff_twist {i j : I} (hij : i ≠ j) (V Y c : ℤ) (r : ℕ)
    (hY : Y = V + 2 * r * D.twistEpsilon i j + 4 * c) :
    D.serreCoeff q (-1) i j r * ((t ^ Y : Lˣ) : L) =
      ((t ^ V : Lˣ) : L) * D.serreCoeff (t * q) 1 i j r := by
  obtain ⟨c₁, hc₁⟩ := (D.serre_phase_mod_four hC hij r).dvd
  obtain ⟨c₂, hc₂⟩ := (D.twistPhi_skew_mod_four hC i j).dvd
  have hε := D.two_mul_twistEpsilon hC i j
  have key : t ^ (2 * (((D.parity i).val * ((r * (D.parity j).val + r.choose 2 : ℕ)) : ℕ) : ℤ))
      * t ^ Y = t ^ V * t ^ ((D.d i : ℤ) * r * ((D.serreDeg i j : ℤ) - r)) := by
    rw [← zpow_add, ← zpow_add]
    apply twist_phase_eq ht (r * c₂ + c + c₁)
    push_cast
    linear_combination hY + hc₁ + (r : ℤ) * hc₂ + (r : ℤ) * hε
  have key' := congrArg (fun u : Lˣ ↦ (u : L)) key
  simp only [Units.val_mul] at key'
  rw [SuperCartanDatum.serreCoeff, SuperCartanDatum.serreCoeff,
    show D.pii (1 : L) i = 1 from one_pow _, one_pow, mul_one, D.qpBinom_qi_twist t hC ht q i]
  rw [show D.pii (-1 : L) i ^ (r * (D.parity j).val + r.choose 2) =
      ((t ^ (2 * (((D.parity i).val * ((r * (D.parity j).val + r.choose 2 : ℕ)) : ℕ) : ℤ)) : Lˣ) : L)
      by rw [SuperCartanDatum.pii, ← pow_mul, neg_one_pow_eq ht]]
  linear_combination (-1 : L) ^ r *
    qpBinom (D.qi q i) (D.pii (-1) i) (D.serreDeg i j) r * key'

variable (D)


/-- The rescaling by `twistE`, `twistF` respects the relations (9.2)–(9.4). -/
theorem twist_gaugeCompatible :
    GaugeCompatible D q (-1) (t * q) 1 (twistE D β) (twistF D β t) where
  comm i j μ := by
    rw [one_pow, mul_one, neg_one_pow_eq ht, ← Units.val_mul]
    congr 1
    rw [twistE_eq D ht, twistF_eq D ht, twistF_eq D ht, twistE_eq D ht, ← zpow_add, ← zpow_add,
      ← zpow_add, twistExp_sub_α D hβ, h_add_α, add_sub_right_comm, twistExp_add_α D hβ,
      D.parity_mul_val]
    have hdot : (D.d j : ℤ) * D.a j i = D.dot i j := by rw [D.dot_comm]; rfl
    by_cases hij : i = j
    · subst hij
      obtain ⟨c, hc⟩ := D.d_eq_parity_add hC i
      rw [twistShift_self, D.isGCM.diag]
      apply twist_phase_eq ht c
      rcases D.parity_val_cases i with h | h <;> rw [h] at hc ⊢ <;> push_cast <;>
        linear_combination (2 : ℤ) * hc
    · apply twist_phase_eq ht (-((D.parity i).val * (D.parity j).val))
      linear_combination hdot - 2 * twistShift_add D hij - D.two_mul_twistEpsilon hC i j
  comm_self i μ := by
    rw [← D.twist_qi_sq t hC ht i, show D.pii (1 : L) i = 1 from one_pow _,
      show D.qi (t * q) i = t ^ D.d i * D.qi q i by simp [SuperCartanDatum.qi, mul_pow],
      qpInt_twist _ _ (twist_fourth ht _)]
    congr 2
    obtain ⟨c, hc⟩ := D.d_eq_parity_add hC i
    rw [twistE_eq D ht, twistF_eq D ht, ← zpow_add, ← zpow_natCast, ← zpow_mul]
    apply twist_phase_eq ht (twistExp D β i (μ - D.α i) + c + (D.parity i).val)
    linear_combination 2 * hc
  serreE i j hij μ := by
    refine ⟨t ^ (2 * (D.serreDeg i j * twistExp D β i μ) + 2 * twistExp D β j μ +
      2 * (D.serreDeg i j * twistShift D i j)), fun r hr ↦ ?_⟩
    rw [serreEPhase, ePowPhase_twistE D hβ ht, ePowPhase_twistE D hβ ht, twistE_eq D ht,
      ← zpow_add, ← zpow_add, twistExp_add_α D hβ, twistExp_add_nsmul D hβ,
      twistExp_add_nsmul D hβ, twistShift_self]
    apply serreCoeff_twist ht q hC hij _ _ (-(r * twistShift D i j)) r
    rw [Nat.cast_sub hr]
    linear_combination (2 * (r : ℤ)) * twistShift_add D hij
  serreF i j hij μ := by
    refine ⟨t ^ (D.serreDeg i j * (2 * ((D.parity i).val : ℤ) + D.d i * (3 - D.h i μ) +
      2 * twistExp D β i μ) + D.d i * (D.serreDeg i j * (D.serreDeg i j - 1)) +
      D.serreDeg i j * (D.d i * D.a i j) + (2 * ((D.parity j).val : ℤ) + D.d j * (3 - D.h j μ) +
      2 * twistExp D β j μ) - 2 * (D.serreDeg i j * twistShift D i j)), fun r hr ↦ ?_⟩
    rw [serreFPhase, fPowPhase_twistF D hβ ht, fPowPhase_twistF D hβ ht, twistF_eq D ht,
      ← zpow_add, ← zpow_add, twistExp_sub_α D hβ, twistExp_sub_α D hβ, twistExp_sub_nsmul D hβ,
      twistExp_sub_nsmul D hβ, h_sub_α, h_sub_nsmul, h_sub_nsmul, D.isGCM.diag, twistShift_self,
      twistShift_self]
    apply serreCoeff_twist ht q hC hij _ _ (-(r * twistShift D j i)) r
    rw [Nat.cast_sub hr]
    linear_combination (2 * (r : ℤ)) * twistShift_add D hij - (r : ℤ) * D.d_mul_symm i j

/-! ### Phases of positive words and the free twisting comparison -/

omit ht hC in
theorem twistE_add_halfWeight (x : I) (l : List I) (μ : X) :
    twistE (L := L) D β x (μ + halfWeight D true (PreF.wordWeight l)) =
      twistE D β x μ * (l.map fun z ↦ (-1 : Lˣ) ^ twistShift D x z).prod := by
  induction l with
  | nil => simp
  | cons z l ih =>
    rw [PreF.wordWeight_cons, halfWeight_add, halfWeight_single,
      show μ + (halfRoot D true z + halfWeight D true (PreF.wordWeight l)) =
        μ + halfWeight D true (PreF.wordWeight l) + D.α z by simp [halfRoot]; abel,
      twistE, twistExp_add_α D hβ, zpow_add, ← twistE, ih, List.map_cons, List.prod_cons]
    ac_rfl

omit hβ in
private theorem pairPhase_comm_of_lt {x z : I} (h : x < z) :
    (-1 : Lˣ) ^ twistShift D x z * t ^ D.twistPhi x z =
      (-1 : Lˣ) ^ twistShift D z x * t ^ D.twistPhi z x := by
  rw [neg_one_units_eq ht, ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add]
  apply twist_phase_eq ht (-D.twistEpsilon z x)
  have hε := D.two_mul_twistEpsilon hC z x
  simp only [twistShift, not_lt_of_gt h, h, ite_false, ite_true, D.twistPhi_of_lt h,
    D.twistPhi_of_gt h]
  linear_combination hε

omit hβ in
/-- The ordered phase of a pair of letters, corrected by the sign of `twistE`, is symmetric. -/
theorem pairPhase_comm (x z : I) :
    (-1 : Lˣ) ^ twistShift D x z * t ^ D.twistPhi x z =
      (-1 : Lˣ) ^ twistShift D z x * t ^ D.twistPhi z x := by
  rcases lt_trichotomy x z with h | rfl | h
  · exact pairPhase_comm_of_lt D ht hC h
  · rfl
  · exact (pairPhase_comm_of_lt D ht hC h).symm

omit ht q hC in
theorem halfPhase_mul_wordPhase_cons (x : I) (l : List I) (μ : X) :
    halfPhase D (twistE (L := L) D β) true (x :: l) μ *
        PreF.wordPhase (fun i j ↦ t ^ D.twistPhi i j) (x :: l) =
      twistE D β x μ * (l.map fun z ↦ (-1 : Lˣ) ^ twistShift D x z * t ^ D.twistPhi x z).prod *
        (halfPhase D (twistE D β) true l μ *
          PreF.wordPhase (fun i j ↦ t ^ D.twistPhi i j) l) := by
  rw [halfPhase, PreF.wordPhase_cons, twistE_add_halfWeight D hβ, List.prod_map_mul]
  ac_rfl

/-- The `twistE`-phase of a positive word times its ordered phase depends only on the
multiset of letters. -/
theorem halfPhase_mul_wordPhase_perm {a b : List I} (hab : a.Perm b) (μ : X) :
    halfPhase D (twistE (L := L) D β) true a μ *
        PreF.wordPhase (fun i j ↦ t ^ D.twistPhi i j) a =
      halfPhase D (twistE D β) true b μ * PreF.wordPhase (fun i j ↦ t ^ D.twistPhi i j) b := by
  induction hab with
  | nil => rfl
  | cons x h ih =>
    rw [halfPhase_mul_wordPhase_cons D hβ, halfPhase_mul_wordPhase_cons D hβ, ih,
      (h.map _).prod_eq]
  | swap x y l =>
    simp only [halfPhase_mul_wordPhase_cons D hβ, List.map_cons, List.prod_cons]
    rw [pairPhase_comm D ht hC y x]
    ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem form_twist_monomial_aux (a b : List I) (μ : X) :
    ((halfPhase D (twistE D β) true a μ : Lˣ) : L) *
        (((halfPhase D (twistE D β) true b μ)⁻¹ : Lˣ) : L) *
        D.form (t * q) 1 (PreF.monomial L a) (PreF.monomial L b) =
      D.form q (-1) (PreF.monomial L a) (PreF.monomial L b) := by
  by_cases hw : PreF.wordWeight a = PreF.wordWeight b
  · have hperm : a.Perm b := List.perm_iff_count.mpr fun x ↦ by
      have := congrArg (· x) hw
      simpa only [PreF.wordWeight_apply] using this
    have hQ := congrArg (fun u : Lˣ ↦ (u : L))
      (halfPhase_mul_wordPhase_perm D hβ ht hC hperm μ)
    simp only [Units.val_mul] at hQ
    have hF := D.form_freeTwist q t hC ht (PreF.monomial L a) (PreF.monomial L b)
    simp only [SuperCartanDatum.freeTwist, PreF.wordGauge_monomial, LinearMap.smul_apply,
      map_smul, smul_eq_mul] at hF
    set P := PreF.wordPhase (fun i j ↦ t ^ D.twistPhi i j)
    set H := halfPhase D (twistE (L := L) D β) true
    have hPa : ((P a : Lˣ) : L) * ((P a)⁻¹ : Lˣ) = 1 := by simp
    have hHb : ((H b μ : Lˣ) : L) * ((H b μ)⁻¹ : Lˣ) = 1 := by simp
    linear_combination (-(((P a)⁻¹ : Lˣ) : L)) * hF +
      D.form (t * q) 1 (PreF.monomial L a) (PreF.monomial L b) *
        ((((H b μ)⁻¹ : Lˣ) : L) * (((P a)⁻¹ : Lˣ) : L) * hQ -
          (H a μ : L) * (((H b μ)⁻¹ : Lˣ) : L) * hPa + (P b : L) * (((P a)⁻¹ : Lˣ) : L) * hHb) +
      D.form q (-1) (PreF.monomial L a) (PreF.monomial L b) * hPa
  · rw [PreF.form_eq_zero_of_ne _ _ hw (PreF.monomial_mem_weightSpace a)
      (PreF.monomial_mem_weightSpace b),
      PreF.form_eq_zero_of_ne _ _ hw (PreF.monomial_mem_weightSpace a)
      (PreF.monomial_mem_weightSpace b), mul_zero]

omit hβ ht hC in
theorem twistE_inv (i : I) (μ : X) : (twistE (L := L) D β i μ)⁻¹ = twistE D β i μ := by
  rw [twistE, ← inv_zpow, inv_neg_one]

omit hβ ht hC in
theorem halfPhase_twistE_inv (positive : Bool) (w : List I) (μ : X) :
    (halfPhase D (twistE (L := L) D β) positive w μ)⁻¹ = halfPhase D (twistE D β) positive w μ := by
  rw [← halfPhase_inv]
  simp only [twistE_inv]

variable [DecidableEq I]

/-- The normalization identity: on positive words, the free forms at `(q, -1)` and `(tq, 1)`
agree after rescaling the words by their `twistE`-phases. -/
theorem form_twist_monomial (a b : List I) (μ : X) :
    ((halfPhase D (twistE D β) true a μ : Lˣ) : L) *
        (((halfPhase D (twistE D β) true b μ)⁻¹ : Lˣ) : L) *
        D.form (t * q) 1 (PreF.monomial L a) (PreF.monomial L b) =
      D.form q (-1) (PreF.monomial L a) (PreF.monomial L b) := by
  convert form_twist_monomial_aux D hβ ht q hC a b μ using 5

variable [DecidableEq X]

/-- The twistor `U̇_{q,-1}(𝔤) ≅ U̇_{tq,1}(𝔤)`: `1_λ ↦ 1_λ`, `eᵢ1_λ ↦ twistE i λ • eᵢ1_λ`,
`fᵢ1_λ ↦ twistF i λ • fᵢ1_λ`. -/
def twistor : CoveringUDot L D q (-1) ≃ₐ[L] CoveringUDot L D (t * q) 1 :=
  gaugeEquiv D (t * q) 1 (twistE D β) (twistF D β t) (twist_gaugeCompatible D hβ ht q hC)

@[simp] theorem twistor_one (μ : X) :
    twistor D hβ ht q hC (one D q (-1) μ) = one D (t * q) 1 μ :=
  gauge_one _ μ

@[simp] theorem twistor_E (i : I) (μ : X) :
    twistor D hβ ht q hC (E D q (-1) i μ) = ((twistE (L := L) D β i μ : Lˣ) : L) • E D (t * q) 1 i μ :=
  gauge_E _ i μ

@[simp] theorem twistor_F (i : I) (μ : X) :
    twistor D hβ ht q hC (F D q (-1) i μ) = (twistF D β t i μ : L) • F D (t * q) 1 i μ :=
  gauge_F _ i μ

@[simp] theorem twistor_symm_one (μ : X) :
    (twistor D hβ ht q hC).symm (one D (t * q) 1 μ) = one D q (-1) μ :=
  gauge_one _ μ

@[simp] theorem twistor_symm_E (i : I) (μ : X) :
    (twistor D hβ ht q hC).symm (E D (t * q) 1 i μ) =
      (((twistE (L := L) D β i μ)⁻¹ : Lˣ) : L) • E D q (-1) i μ :=
  gauge_E _ i μ

@[simp] theorem twistor_symm_F (i : I) (μ : X) :
    (twistor D hβ ht q hC).symm (F D (t * q) 1 i μ) =
      (((twistF D β t i μ)⁻¹ : Lˣ) : L) • F D q (-1) i μ :=
  gauge_F _ i μ

theorem twistor_halfWord_true (w : List I) (μ : X) :
    twistor D hβ ht q hC (halfWord D q (-1) true w μ) =
      ((halfPhase D (twistE (L := L) D β) true w μ : Lˣ) : L) • halfWord D (t * q) 1 true w μ :=
  gauge_halfWord_true _ w μ

theorem twistor_halfWord_false (w : List I) (μ : X) :
    twistor D hβ ht q hC (halfWord D q (-1) false w μ) =
      (halfPhase D (twistF D β t) false w μ : L) • halfWord D (t * q) 1 false w μ :=
  gauge_halfWord_false _ w μ

theorem twistor_mem_modified {x : CoveringUDot L D q (-1)} (hx : x ∈ modified D q (-1)) :
    twistor D hβ ht q hC x ∈ modified D (t * q) 1 :=
  gauge_mem_modified _ hx

/-- `ρ ∘ twistor ∘ ρ`, with `ρ` the antiautomorphisms (9.8) at `(tq, 1)` and `(q, -1)`. -/
def twistorAdjoint : CoveringUDot L D q (-1) →ₐ[L] CoveringUDot L D (t * q) 1 where
  toFun x := (rho D (t * q) 1 (one_pow 2)
    (twistor D hβ ht q hC (rho D q (-1) neg_one_sq x).unop)).unop
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, MulOpposite.unop_mul]
  map_zero' := by simp
  map_add' x y := by simp
  commutes' c := by simp

theorem twistorAdjoint_apply (x : CoveringUDot L D q (-1)) :
    twistorAdjoint D hβ ht q hC x = (rho D (t * q) 1 (one_pow 2)
      (twistor D hβ ht q hC (rho D q (-1) neg_one_sq x).unop)).unop := rfl

@[simp] theorem twistorAdjoint_one (μ : X) :
    twistorAdjoint D hβ ht q hC (one D q (-1) μ) = one D (t * q) 1 μ := by
  simp [twistorAdjoint_apply]

@[simp] theorem twistorAdjoint_E (i : I) (μ : X) :
    twistorAdjoint D hβ ht q hC (E D q (-1) i μ) =
      (((twistE (L := L) D β i μ)⁻¹ : Lˣ) : L) • E D (t * q) 1 i μ := by
  rw [twistorAdjoint_apply, rho_E, map_smul, twistor_F, rho_smul, rho_smul, rho_F, smul_smul,
    smul_smul, add_sub_cancel_right, h_add_α, D.isGCM.diag]
  congr 1
  simp only [qp, ← Units.val_mul]
  congr 1
  obtain ⟨c, hc⟩ := D.d_eq_parity_add hC i
  rw [twistF_eq D ht, add_sub_cancel_right, h_add_α, D.isGCM.diag, twistE_inv, twistE_eq D ht, mul_zpow,
    show q ^ (-((D.d i : ℤ) * (D.h i μ + 1))) * t ^ (2 * ((D.parity i).val : ℤ) +
        D.d i * (3 - (D.h i μ + 2)) + 2 * twistExp D β i μ) *
        (t ^ ((D.d i : ℤ) * (D.h i μ + 2 - 1)) * q ^ ((D.d i : ℤ) * (D.h i μ + 2 - 1))) =
      t ^ (2 * ((D.parity i).val : ℤ) + D.d i * (3 - (D.h i μ + 2)) + 2 * twistExp D β i μ) *
        t ^ ((D.d i : ℤ) * (D.h i μ + 2 - 1)) *
        (q ^ (-((D.d i : ℤ) * (D.h i μ + 1))) * q ^ ((D.d i : ℤ) * (D.h i μ + 2 - 1))) by ac_rfl,
    ← zpow_add, ← zpow_add, show -((D.d i : ℤ) * (D.h i μ + 1)) + D.d i * (D.h i μ + 2 - 1) = 0
      by ring, zpow_zero, mul_one]
  apply twist_phase_eq ht (c + (D.parity i).val)
  linear_combination 2 * hc

@[simp] theorem twistorAdjoint_F (i : I) (μ : X) :
    twistorAdjoint D hβ ht q hC (F D q (-1) i μ) = (twistF D β t i μ : L) • F D (t * q) 1 i μ := by
  rw [twistorAdjoint_apply, rho_F, map_smul, twistor_E, rho_smul, rho_smul, rho_E, smul_smul,
    smul_smul, sub_add_cancel, h_sub_α, D.isGCM.diag]
  congr 1
  simp only [qp, ← Units.val_mul]
  congr 1
  obtain ⟨c, hc⟩ := D.d_eq_parity_add hC i
  rw [twistF_eq D ht, twistE_eq D ht, mul_zpow,
    show q ^ ((D.d i : ℤ) * (D.h i μ - 1)) * t ^ (2 * twistExp D β i (μ - D.α i)) *
        (t ^ (-((D.d i : ℤ) * (D.h i μ - 2 + 1))) * q ^ (-((D.d i : ℤ) * (D.h i μ - 2 + 1)))) =
      t ^ (2 * twistExp D β i (μ - D.α i)) * t ^ (-((D.d i : ℤ) * (D.h i μ - 2 + 1))) *
        (q ^ ((D.d i : ℤ) * (D.h i μ - 1)) * q ^ (-((D.d i : ℤ) * (D.h i μ - 2 + 1)))) by ac_rfl,
    ← zpow_add, ← zpow_add, show (D.d i : ℤ) * (D.h i μ - 1) + -((D.d i : ℤ) * (D.h i μ - 2 + 1)) = 0
      by ring, zpow_zero, mul_one]
  apply twist_phase_eq ht (-(c + (D.parity i).val))
  linear_combination -2 * hc

/-- The adjoint twistor is the twistor itself: the twistor commutes with `ρ`. -/
theorem twistorAdjoint_eq :
    twistorAdjoint D hβ ht q hC = (twistor D hβ ht q hC : CoveringUDot L D q (-1) →ₐ[L] _) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | one μ =>
    change twistorAdjoint D hβ ht q hC (one D q (-1) μ) = twistor D hβ ht q hC (one D q (-1) μ)
    simp
  | e i μ =>
    change twistorAdjoint D hβ ht q hC (E D q (-1) i μ) = twistor D hβ ht q hC (E D q (-1) i μ)
    rw [twistorAdjoint_E, twistor_E, twistE_inv]
  | f i μ =>
    change twistorAdjoint D hβ ht q hC (F D q (-1) i μ) = twistor D hβ ht q hC (F D q (-1) i μ)
    rw [twistorAdjoint_F, twistor_F]

/-- `ρ ∘ twistor = twistorAdjoint ∘ ρ`. -/
theorem rho_twistor (x : CoveringUDot L D q (-1)) :
    (rho D (t * q) 1 (one_pow 2) (twistor D hβ ht q hC x)).unop =
      twistorAdjoint D hβ ht q hC (rho D q (-1) neg_one_sq x).unop := by
  rw [twistorAdjoint_apply, rho_rho]

theorem twistorAdjoint_mem_modified {x : CoveringUDot L D q (-1)}
    (hx : x ∈ modified D q (-1)) : twistorAdjoint D hβ ht q hC x ∈ modified D (t * q) 1 := by
  rw [twistorAdjoint_eq]
  exact twistor_mem_modified D hβ ht q hC hx

theorem twistorAdjoint_halfWord_true (w : List I) (μ : X) :
    twistorAdjoint D hβ ht q hC (halfWord D q (-1) true w μ) =
      (((halfPhase D (twistE (L := L) D β) true w μ)⁻¹ : Lˣ) : L) • halfWord D (t * q) 1 true w μ := by
  rw [twistorAdjoint_eq, halfPhase_twistE_inv]
  exact twistor_halfWord_true D hβ ht q hC w μ

/-- The twistor with the root coordinates of a datum with linearly independent simple roots. -/
abbrev twistorRootCoord (hα : LinearIndependent ℤ D.α) :
    CoveringUDot L D q (-1) ≃ₐ[L] CoveringUDot L D (t * q) 1 :=
  twistor D (β := D.rootCoord hα) (D.rootCoord_add_α hα) ht q hC

end UDot

end OddMath.CoveringQuantum
