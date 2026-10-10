/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.Serre
import OddMath.CoveringQuantum.UDot.Basic

/-!
# The symmetries `ω`, `ψ` of `U̇_{q,π}(𝔤)`

Brundan–Ellis, arXiv:1701.04133v2 ([BE2]), §9, (9.6), (9.7): the antilinear (for the bar
involution `q ↦ q⁻¹`, `π ↦ π` of the ground ring) algebra automorphisms `ω`, `ψ` of
`U̇_{q,π}(𝔤)` with
```
ω(1_λ) = 1_{-λ},  ω(eᵢ1_λ) = fᵢ1_{-λ},  ω(fᵢ1_λ) = eᵢ1_{-λ},
ψ(1_λ) = 1_λ,     ψ(eᵢ1_λ) = eᵢ1_λ,     ψ(fᵢ1_λ) = π^{|i,λ|} fᵢ1_λ.
```

The ground ring is any commutative ring `k` with a unit `q`, an element `π` with `π² = 1`, and a
ring endomorphism `σ` (the bar involution) with `σ(q) = q⁻¹` and `σ(π) = π`. An antilinear map
is a ring homomorphism `φ` with `φ(c x) = σ(c) φ(x)`; it is constructed as a `k`-algebra
homomorphism into `UDot.Twist σ U̇`, the ring `U̇` with `k` acting through `σ`.

The relations are checked using (9.1), `bar [n r] = π^{r(n-r)} [n r]` (for the Serre
coefficients, whose binomials are bar invariant: `dᵢⱼ + 1` is odd whenever `i` is odd), and the
invariance of `|i, λ|` under adding roots.

## Main definitions

* `UDot.Twist σ A`: `A` with scalars acting through `σ`.
* `UDot.omega`, `UDot.psi`: `ω` and `ψ`, as ring endomorphisms of `CoveringUDot k D q π`.

## Main results

* `UDot.omega_one`, `UDot.omega_E`, `UDot.omega_F`, `UDot.omega_smul`, `UDot.omega_omega`.
* `UDot.psi_one`, `UDot.psi_E`, `UDot.psi_F`, `UDot.psi_smul`, `UDot.psi_psi`.
-/

noncomputable section

namespace OddMath.CoveringQuantum

open Finset

/-- Ring homomorphisms commute with `(q, π)`-binomial coefficients. -/
theorem map_qpBinom {k k' : Type*} [CommRing k] [CommRing k'] (f : k →+* k') (q : kˣ) (π : k)
    (n r : ℕ) : f (qpBinom q π n r) = qpBinom (Units.map f.toMonoidHom q) (f π) n r := by
  induction n generalizing r with
  | zero => rcases r with _ | r <;> simp
  | succ n ih =>
    rcases r with _ | r
    · simp
    · simp only [qpBinom_succ_succ, map_add, map_mul, map_pow, ih, Units.coe_map,
        Units.coe_map_inv, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]

namespace UDot

/-- A type synonym for `A` on which `k` acts through the ring endomorphism `σ`. -/
def Twist {k : Type*} [CommRing k] (_σ : k →+* k) (A : Type*) := A

namespace Twist

variable {k : Type*} [CommRing k] (σ : k →+* k) {A : Type*} [Ring A] [Algebra k A]

instance : Ring (Twist σ A) := ‹Ring A›

instance : Algebra k (Twist σ A) :=
  ((algebraMap k A).comp σ).toAlgebra' fun c x ↦ Algebra.commutes (σ c) (x : A)

/-- The identity `A → Twist σ A`. -/
def of : A ≃+* Twist σ A := RingEquiv.refl A

omit [Algebra k A] in
@[simp] theorem of_apply (x : A) : of σ x = x := rfl

omit [Algebra k A] in
@[simp] theorem of_symm_apply (x : Twist σ A) : (of σ).symm x = x := rfl

theorem smul_def (c : k) (x : Twist σ A) : c • x = of σ (σ c • ((of σ).symm x : A)) :=
  show algebraMap k A (σ c) * (of σ).symm x = σ c • (of σ).symm x from (Algebra.smul_def _ _).symm

end Twist

variable {k : Type*} [CommRing k] {I X : Type*} [AddCommGroup X]
  (D : RootDatum I X) (q : kˣ) (π : k) (σ : k →+* k)

/-- The hypotheses on the bar involution `σ`: `σ(q) = q⁻¹`, `σ(π) = π`, and `π² = 1`. -/
structure BarData : Prop where
  map_q : σ q = ((q⁻¹ : kˣ) : k)
  map_π : σ π = π
  π_sq : π ^ 2 = 1

variable {D q π σ}

theorem BarData.units_map_qi (hσ : BarData q π σ) (i : I) :
    Units.map σ.toMonoidHom (D.qi q i) = (D.qi q i)⁻¹ := by
  ext
  show σ ((q ^ D.d i : kˣ) : k) = (((q ^ D.d i)⁻¹ : kˣ) : k)
  rw [← inv_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, hσ.map_q]

theorem BarData.map_pii (hσ : BarData q π σ) (i : I) : σ (D.pii π i) = D.pii π i := by
  rw [SuperCartanDatum.pii, map_pow, hσ.map_π]

/-- The Serre coefficients are bar invariant. -/
theorem BarData.map_serreCoeff (hσ : BarData q π σ) {i j : I} (hij : i ≠ j) (r : ℕ) :
    σ (D.serreCoeff q π i j r) = D.serreCoeff q π i j r := by
  rw [SuperCartanDatum.serreCoeff, map_mul, map_mul, map_pow, map_pow, map_neg, map_one,
    hσ.map_pii, map_qpBinom, hσ.units_map_qi, hσ.map_pii]
  congr 1
  rcases D.odd_serreDeg_or π hij with h | h
  · rw [qpBinom_inv_of_odd (D.pii_sq π hσ.π_sq i) h]
  · rw [qpBinom_inv (D.pii_sq π hσ.π_sq i), h, one_pow, one_mul]

/-- `bar [n]_{qᵢ,πᵢ} = -πᵢ [-n]_{qᵢ,πᵢ}` ((9.1)). -/
theorem BarData.map_qpInt (hσ : BarData q π σ) (i : I) (n : ℤ) :
    σ (qpInt (D.qi q i) (D.pii π i) n) = -(D.pii π i * qpInt (D.qi q i) (D.pii π i) (-n)) := by
  rw [OddMath.CoveringQuantum.map_qpInt, hσ.units_map_qi, hσ.map_pii,
    qpInt_inv_eq_neg (D.pii_sq π hσ.π_sq i)]

/-! ### `ω` -/

section Omega

variable [DecidableEq I] [DecidableEq X] (D q π σ)

/-- `ω` on generators. -/
def omegaGen : Gen I X → CoveringUDot k D q π
  | .one μ => one D q π (-μ)
  | .e i μ => F D q π i (-μ)
  | .f i μ => E D q π i (-μ)

/-- `ω` on the free algebra, as a `k`-algebra map into the twist. -/
def omegaFree : Free k I X →ₐ[k] Twist σ (CoveringUDot k D q π) :=
  FreeAlgebra.lift k fun g ↦ Twist.of σ (omegaGen D q π g)

/-- `ω` on the free algebra, as a ring homomorphism. -/
def omegaFreeR : Free k I X →+* CoveringUDot k D q π :=
  (Twist.of σ).symm.toRingHom.comp (omegaFree D q π σ).toRingHom

variable {D q π σ}

theorem omegaFree_eq (x : Free k I X) :
    omegaFree D q π σ x = Twist.of σ (omegaFreeR D q π σ x) := rfl

@[simp] theorem omegaFreeR_one (μ : X) : omegaFreeR D q π σ (Free.one k μ) = one D q π (-μ) := by
  simp [omegaFreeR, omegaFree, Free.one, omegaGen]

@[simp] theorem omegaFreeR_E (i : I) (μ : X) :
    omegaFreeR D q π σ (Free.E k i μ) = F D q π i (-μ) := by
  simp [omegaFreeR, omegaFree, Free.E, omegaGen]

@[simp] theorem omegaFreeR_F (i : I) (μ : X) :
    omegaFreeR D q π σ (Free.F k i μ) = E D q π i (-μ) := by
  simp [omegaFreeR, omegaFree, Free.F, omegaGen]

theorem omegaFreeR_smul (c : k) (x : Free k I X) :
    omegaFreeR D q π σ (c • x) = σ c • omegaFreeR D q π σ x := by
  simp only [omegaFreeR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_smul, Twist.smul_def, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply]

theorem omegaFreeR_epow (i : I) (n : ℕ) (μ : X) :
    omegaFreeR D q π σ (epow D i n μ) = mk D q π (fpow D i n (-μ)) := by
  induction n with
  | zero => simp [epow, fpow, one]
  | succ n ih =>
    rw [epow, map_mul, ih, omegaFreeR_E, fpow, map_mul, neg_add']
    rfl

theorem omegaFreeR_fpow (i : I) (n : ℕ) (μ : X) :
    omegaFreeR D q π σ (fpow D i n μ) = mk D q π (epow D i n (-μ)) := by
  induction n with
  | zero => simp [epow, fpow, one]
  | succ n ih =>
    rw [fpow, map_mul, ih, omegaFreeR_F, epow, map_mul, neg_sub', sub_neg_eq_add]
    rfl

theorem omegaFreeR_rel (hσ : BarData q π σ) {x y : Free k I X} (h : Rel D q π x y) :
    omegaFreeR D q π σ x = omegaFreeR D q π σ y := by
  cases h with
  | one_one μ ν =>
    rw [map_mul, omegaFreeR_one, omegaFreeR_one, one_mul_one]
    split_ifs with h₁ h₂ h₂
    · simp
    · exact absurd (neg_inj.1 h₁) h₂
    · exact absurd (congrArg Neg.neg h₂) h₁
    · simp
  | one_E i μ =>
    rw [map_mul, omegaFreeR_one, omegaFreeR_E, neg_add', one_mul_F_self]
  | E_one i μ =>
    rw [map_mul, omegaFreeR_one, omegaFreeR_E, F_mul_one_self]
  | one_F i μ =>
    rw [map_mul, omegaFreeR_one, omegaFreeR_F, neg_sub', sub_neg_eq_add, one_mul_E_self]
  | F_one i μ =>
    rw [map_mul, omegaFreeR_one, omegaFreeR_F, E_mul_one_self]
  | comm i j μ =>
    have hc := comm_rel D q π j i (-μ)
    rw [mul_comm (D.parity j)] at hc
    set v := (D.parity i * D.parity j).val
    have hv : π ^ v * π ^ v = 1 := by rw [← pow_add, ← two_mul, pow_mul, hσ.π_sq, one_pow]
    rw [map_sub, map_mul, omegaFreeR_smul, map_mul, omegaFreeR_E, omegaFreeR_F,
      omegaFreeR_F, omegaFreeR_E, map_pow, hσ.map_π, neg_sub', sub_neg_eq_add, neg_add']
    have key : F D q π i (-μ + D.α j) * E D q π j (-μ) -
        π ^ v • (E D q π j (-μ - D.α i) * F D q π i (-μ)) =
        -(π ^ v • (if j = i then qpInt (D.qi q j) (D.pii π j) (D.h j (-μ)) • one D q π (-μ)
          else 0)) := by
      rw [← hc, smul_sub, smul_smul, hv, one_smul]; abel
    rw [key]
    split_ifs with h₁ h₂ h₂
    · subst h₁
      have hpp : π ^ (D.parity j * D.parity j).val = D.pii π j := by
        rw [SuperCartanDatum.pii]; congr 1; generalize D.parity j = p; fin_cases p <;> rfl
      rw [omegaFreeR_smul, omegaFreeR_one, hσ.map_qpInt, smul_smul, ← neg_smul, hpp, RootDatum.h,
        RootDatum.h, map_neg]
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · simp
  | serreE i j μ h =>
    rw [map_zero, serreE, map_sum, ← serreF_rel D q π h (-μ), serreF, map_sum]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [omegaFreeR_smul, map_mul, map_mul, omegaFreeR_epow, omegaFreeR_E, omegaFreeR_epow,
      hσ.map_serreCoeff h, map_smul, map_mul, map_mul, neg_add', neg_add']
    rfl
  | serreF i j μ h =>
    rw [map_zero, serreF, map_sum, ← serreE_rel D q π h (-μ), serreE, map_sum]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [omegaFreeR_smul, map_mul, map_mul, omegaFreeR_fpow, omegaFreeR_F, omegaFreeR_fpow,
      hσ.map_serreCoeff h, map_smul, map_mul, map_mul, neg_sub', neg_sub', sub_neg_eq_add,
      sub_neg_eq_add]
    rfl

variable (D q π σ) in
/-- The antilinear algebra automorphism `ω` of (9.6):
`ω(1_λ) = 1_{-λ}`, `ω(eᵢ1_λ) = fᵢ1_{-λ}`, `ω(fᵢ1_λ) = eᵢ1_{-λ}`. -/
def omega (hσ : BarData q π σ) : CoveringUDot k D q π →+* CoveringUDot k D q π :=
  (Twist.of σ).symm.toRingHom.comp
    (RingQuot.liftAlgHom k ⟨omegaFree D q π σ, fun _ _ h ↦ by
      rw [omegaFree_eq, omegaFree_eq, omegaFreeR_rel hσ h]⟩).toRingHom

theorem omega_mk (hσ : BarData q π σ) (x : Free k I X) :
    omega D q π σ hσ (mk D q π x) = omegaFreeR D q π σ x := by
  simp only [omega, mk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingQuot.liftAlgHom_mkAlgHom_apply, RingEquiv.toRingHom_eq_coe]
  rfl

@[simp] theorem omega_one (hσ : BarData q π σ) (μ : X) :
    omega D q π σ hσ (one D q π μ) = one D q π (-μ) := by
  rw [one, omega_mk, omegaFreeR_one]

@[simp] theorem omega_E (hσ : BarData q π σ) (i : I) (μ : X) :
    omega D q π σ hσ (E D q π i μ) = F D q π i (-μ) := by
  rw [E, omega_mk, omegaFreeR_E]

@[simp] theorem omega_F (hσ : BarData q π σ) (i : I) (μ : X) :
    omega D q π σ hσ (F D q π i μ) = E D q π i (-μ) := by
  rw [F, omega_mk, omegaFreeR_F]

/-- `ω` is antilinear. -/
theorem omega_smul (hσ : BarData q π σ) (c : k) (x : CoveringUDot k D q π) :
    omega D q π σ hσ (c • x) = σ c • omega D q π σ hσ x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  rw [← map_smul, omega_mk, omega_mk, omegaFreeR_smul]

theorem omega_algebraMap (hσ : BarData q π σ) (c : k) :
    omega D q π σ hσ (algebraMap k _ c) = algebraMap k _ (σ c) := by
  rw [Algebra.algebraMap_eq_smul_one, omega_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

/-- `ω` is an involution (given `σ² = 1`). -/
theorem omega_omega (hσ : BarData q π σ) (hσσ : ∀ c, σ (σ c) = c) (x : CoveringUDot k D q π) :
    omega D q π σ hσ (omega D q π σ hσ x) = x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, omega_algebraMap, omega_algebraMap, hσσ]
  | grade1 g =>
    cases g with
    | one μ => rw [← Free.one, ← one, omega_one, omega_one, neg_neg]
    | e i μ => rw [← Free.E, ← E, omega_E, omega_F, neg_neg]
    | f i μ => rw [← Free.F, ← F, omega_F, omega_E, neg_neg]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]

end Omega

/-! ### `ψ` -/

section Psi

theorem _root_.OddMath.CoveringQuantum.RootDatum.parl_sub_α (i j : I) (μ : X) :
    D.parl i (μ - D.α j) = D.parl i μ := by
  rw [← D.parl_add_α i j (μ - D.α j), sub_add_cancel]

theorem _root_.OddMath.CoveringQuantum.RootDatum.parl_sub_nsmul (i j : I) (μ : X) (n : ℕ) :
    D.parl i (μ - n • D.α j) = D.parl i μ := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ← sub_sub, D.parl_sub_α, ih]

/-- `π^{|i,λ|} = πᵢ^{⟨hᵢ,λ⟩ - 1}` (the exponent read mod 2), given `π² = 1`. -/
theorem pow_parl (hπ : π ^ 2 = 1) (i : I) (μ : X) :
    π ^ (D.parl i μ).val = D.pii π i ^ (D.h i μ - 1).natAbs := by
  rw [RootDatum.parl, SuperCartanDatum.pii]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (D.parity i) with hp | hp
  · simp [hp]
  · rw [hp, one_mul, ZMod.val_one, pow_one]
    have h1 : ((D.h i μ : ZMod 2) + 1) = ((D.h i μ - 1 : ℤ) : ZMod 2) := by
      push_cast
      rw [sub_eq_add_neg, show (-1 : ZMod 2) = 1 from rfl]
    rw [h1]
    have h2 := ZMod.val_intCast (n := 2) (D.h i μ - 1)
    have h3 := Int.natAbs_eq (D.h i μ - 1)
    rw [← Nat.div_add_mod (ZMod.val _) 2, ← Nat.div_add_mod (D.h i μ - 1).natAbs 2, pow_add,
      pow_add, pow_mul, pow_mul, hπ, one_pow, one_pow, one_mul, one_mul]
    congr 1
    rcases h3 with h3 | h3 <;> omega

variable [DecidableEq I] [DecidableEq X] (D q π σ)

/-- `ψ` on generators. -/
def psiGen : Gen I X → CoveringUDot k D q π
  | .one μ => one D q π μ
  | .e i μ => E D q π i μ
  | .f i μ => π ^ (D.parl i μ).val • F D q π i μ

/-- `ψ` on the free algebra, as a `k`-algebra map into the twist. -/
def psiFree : Free k I X →ₐ[k] Twist σ (CoveringUDot k D q π) :=
  FreeAlgebra.lift k fun g ↦ Twist.of σ (psiGen D q π g)

/-- `ψ` on the free algebra, as a ring homomorphism. -/
def psiFreeR : Free k I X →+* CoveringUDot k D q π :=
  (Twist.of σ).symm.toRingHom.comp (psiFree D q π σ).toRingHom

variable {D q π σ}

theorem psiFree_eq (x : Free k I X) : psiFree D q π σ x = Twist.of σ (psiFreeR D q π σ x) := rfl

@[simp] theorem psiFreeR_one (μ : X) : psiFreeR D q π σ (Free.one k μ) = one D q π μ := by
  simp [psiFreeR, psiFree, Free.one, psiGen]

@[simp] theorem psiFreeR_E (i : I) (μ : X) : psiFreeR D q π σ (Free.E k i μ) = E D q π i μ := by
  simp [psiFreeR, psiFree, Free.E, psiGen]

@[simp] theorem psiFreeR_F (i : I) (μ : X) :
    psiFreeR D q π σ (Free.F k i μ) = π ^ (D.parl i μ).val • F D q π i μ := by
  simp [psiFreeR, psiFree, Free.F, psiGen]

theorem psiFreeR_smul (c : k) (x : Free k I X) :
    psiFreeR D q π σ (c • x) = σ c • psiFreeR D q π σ x := by
  simp only [psiFreeR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_smul, Twist.smul_def, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply]

theorem psiFreeR_epow (i : I) (n : ℕ) (μ : X) :
    psiFreeR D q π σ (epow D i n μ) = mk D q π (epow D i n μ) := by
  induction n with
  | zero => simp [epow, one]
  | succ n ih => rw [epow, map_mul, ih, psiFreeR_E, map_mul]; rfl

theorem psiFreeR_fpow (i : I) (n : ℕ) (μ : X) :
    psiFreeR D q π σ (fpow D i n μ) = π ^ (n * (D.parl i μ).val) • mk D q π (fpow D i n μ) := by
  induction n with
  | zero => simp [fpow, one]
  | succ n ih =>
    rw [fpow, map_mul, ih, psiFreeR_F, D.parl_sub_nsmul, map_mul, smul_mul_smul_comm, ← pow_add,
      add_mul, one_mul, add_comm]
    rfl

theorem psiFreeR_rel (hσ : BarData q π σ) {x y : Free k I X} (h : Rel D q π x y) :
    psiFreeR D q π σ x = psiFreeR D q π σ y := by
  cases h with
  | one_one μ ν =>
    rw [map_mul, psiFreeR_one, psiFreeR_one, one_mul_one]
    split_ifs <;> simp
  | one_E i μ => rw [map_mul, psiFreeR_one, psiFreeR_E, one_mul_E_self]
  | E_one i μ => rw [map_mul, psiFreeR_one, psiFreeR_E, E_mul_one_self]
  | one_F i μ => rw [map_mul, psiFreeR_one, psiFreeR_F, mul_smul_comm, one_mul_F_self]
  | F_one i μ => rw [map_mul, psiFreeR_one, psiFreeR_F, smul_mul_assoc, F_mul_one_self]
  | comm i j μ =>
    rw [map_sub, map_mul, psiFreeR_smul, map_mul, psiFreeR_E, psiFreeR_F, psiFreeR_F,
      psiFreeR_E, map_pow, hσ.map_π, D.parl_add_α]
    have e : E D q π i (μ - D.α j) * (π ^ (D.parl j μ).val • F D q π j μ) -
        π ^ (D.parity i * D.parity j).val • ((π ^ (D.parl j μ).val • F D q π j (μ + D.α i)) *
          E D q π i μ) =
        π ^ (D.parl j μ).val • (E D q π i (μ - D.α j) * F D q π j μ -
          π ^ (D.parity i * D.parity j).val • (F D q π j (μ + D.α i) * E D q π i μ)) := by
      simp only [mul_smul_comm, smul_mul_assoc]; module
    rw [e, comm_rel]
    split_ifs with h
    · subst h
      rw [psiFreeR_smul, psiFreeR_one, smul_smul, OddMath.CoveringQuantum.map_qpInt,
        hσ.units_map_qi, hσ.map_pii, qpInt_inv (D.pii_sq π hσ.π_sq i), pow_parl hσ.π_sq]
    · simp
  | serreE i j μ h =>
    rw [map_zero, serreE, map_sum, ← serreE_rel D q π h μ, serreE, map_sum]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [psiFreeR_smul, map_mul, map_mul, psiFreeR_epow, psiFreeR_E, psiFreeR_epow,
      hσ.map_serreCoeff h, map_smul, map_mul, map_mul]
    rfl
  | serreF i j μ h =>
    rw [map_zero, serreF, map_sum]
    have key : ∀ r ∈ range (D.serreDeg i j + 1),
        psiFreeR D q π σ (D.serreCoeff q π i j r • (fpow D i (D.serreDeg i j - r)
          (μ - r • D.α i - D.α j) * Free.F k j (μ - r • D.α i) * fpow D i r μ)) =
        π ^ (D.serreDeg i j * (D.parl i μ).val + (D.parl j μ).val) •
          mk D q π (D.serreCoeff q π i j r • (fpow D i (D.serreDeg i j - r)
          (μ - r • D.α i - D.α j) * Free.F k j (μ - r • D.α i) * fpow D i r μ)) := by
      intro r hr
      have hr := mem_range.1 hr
      rw [psiFreeR_smul, map_mul, map_mul, psiFreeR_fpow, psiFreeR_F, psiFreeR_fpow,
        hσ.map_serreCoeff h, D.parl_sub_α, D.parl_sub_nsmul, D.parl_sub_nsmul, map_smul, map_mul,
        map_mul]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      obtain ⟨m, hm⟩ : ∃ m, D.serreDeg i j = m + r := ⟨_, (Nat.sub_add_cancel (by omega)).symm⟩
      rw [hm, Nat.add_sub_cancel]
      congr 1
      ring
    rw [sum_congr rfl key, ← smul_sum, ← map_sum, ← serreF, serreF_rel D q π h μ, smul_zero]

variable (D q π σ) in
/-- The antilinear algebra automorphism `ψ` of (9.7):
`ψ(1_λ) = 1_λ`, `ψ(eᵢ1_λ) = eᵢ1_λ`, `ψ(fᵢ1_λ) = π^{|i,λ|} fᵢ1_λ`. -/
def psi (hσ : BarData q π σ) : CoveringUDot k D q π →+* CoveringUDot k D q π :=
  (Twist.of σ).symm.toRingHom.comp
    (RingQuot.liftAlgHom k ⟨psiFree D q π σ, fun _ _ h ↦ by
      rw [psiFree_eq, psiFree_eq, psiFreeR_rel hσ h]⟩).toRingHom

theorem psi_mk (hσ : BarData q π σ) (x : Free k I X) :
    psi D q π σ hσ (mk D q π x) = psiFreeR D q π σ x := by
  simp only [psi, mk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingQuot.liftAlgHom_mkAlgHom_apply, RingEquiv.toRingHom_eq_coe]
  rfl

@[simp] theorem psi_one (hσ : BarData q π σ) (μ : X) :
    psi D q π σ hσ (one D q π μ) = one D q π μ := by
  rw [one, psi_mk, psiFreeR_one]; rfl

@[simp] theorem psi_E (hσ : BarData q π σ) (i : I) (μ : X) :
    psi D q π σ hσ (E D q π i μ) = E D q π i μ := by
  rw [E, psi_mk, psiFreeR_E]; rfl

@[simp] theorem psi_F (hσ : BarData q π σ) (i : I) (μ : X) :
    psi D q π σ hσ (F D q π i μ) = π ^ (D.parl i μ).val • F D q π i μ := by
  rw [F, psi_mk, psiFreeR_F]; rfl

/-- `ψ` is antilinear. -/
theorem psi_smul (hσ : BarData q π σ) (c : k) (x : CoveringUDot k D q π) :
    psi D q π σ hσ (c • x) = σ c • psi D q π σ hσ x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  rw [← map_smul, psi_mk, psi_mk, psiFreeR_smul]

theorem psi_algebraMap (hσ : BarData q π σ) (c : k) :
    psi D q π σ hσ (algebraMap k _ c) = algebraMap k _ (σ c) := by
  rw [Algebra.algebraMap_eq_smul_one, psi_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

/-- `ψ` is an involution (given `σ² = 1`). -/
theorem psi_psi (hσ : BarData q π σ) (hσσ : ∀ c, σ (σ c) = c) (x : CoveringUDot k D q π) :
    psi D q π σ hσ (psi D q π σ hσ x) = x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, psi_algebraMap, psi_algebraMap, hσσ]
  | grade1 g =>
    cases g with
    | one μ => rw [← Free.one, ← one, psi_one, psi_one]
    | e i μ => rw [← Free.E, ← E, psi_E, psi_E]
    | f i μ =>
      rw [← Free.F, ← F, psi_F, psi_smul, psi_F, smul_smul, map_pow, hσ.map_π, ← pow_add,
        ← two_mul, pow_mul, hσ.π_sq, one_pow, one_smul]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]

end Psi

end UDot

end OddMath.CoveringQuantum
