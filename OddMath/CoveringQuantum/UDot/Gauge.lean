/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.HalfWeights

/-!
# Diagonal rescaling of the Chevalley generators of `U̇`

Supporting material for Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1: an algebra map between
two presentations `U̇_{q₁,π₁}(𝔤)` and `U̇_{q₂,π₂}(𝔤)` (§9, relations (9.2)–(9.4)) fixing every
`1_λ` and rescaling `eᵢ1_λ`, `fᵢ1_λ` by units `cE i λ`, `cF i λ`.

The map exists as soon as the rescaled generators satisfy the relations (9.2)–(9.4) of the
source. For (9.2) this is the pair of scalar identities `GaugeCompatible.comm`,
`GaugeCompatible.comm_self`; for (9.3)–(9.4) it is that the rescaled Serre coefficients of the
source are, up to one unit, the Serre coefficients of the target. Here the phase of a word is
the product of the rescaling units of its letters, each taken at the weight where it acts
(`ePowPhase`, `fPowPhase`, `serreEPhase`, `serreFPhase`, `halfPhase`).

## Main definitions

* `UDot.GaugeCompatible`: the scalar conditions.
* `UDot.gauge`: the algebra map; `UDot.gaugeEquiv`: the algebra isomorphism whose inverse
  rescales by the inverse units.

## Main results

* `UDot.gauge_one`, `UDot.gauge_E`, `UDot.gauge_F`, `UDot.gauge_halfWord_true`,
  `UDot.gauge_halfWord_false`, `UDot.gauge_mem_modified`.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open Finset

variable {k I X : Type*} [CommRing k] [AddCommGroup X]
variable (D : RootDatum I X)

section Phases

variable (c : I → X → kˣ)

/-- The phase of `eᵢⁿ 1_λ`, mirroring `UDot.epow`. -/
def ePowPhase (i : I) : ℕ → X → kˣ
  | 0, _ => 1
  | n + 1, μ => c i (μ + n • D.α i) * ePowPhase i n μ

/-- The phase of `fᵢⁿ 1_λ`, mirroring `UDot.fpow`. -/
def fPowPhase (i : I) : ℕ → X → kˣ
  | 0, _ => 1
  | n + 1, μ => c i (μ - n • D.α i) * fPowPhase i n μ

/-- The phase of `eᵢ^{N-r} eⱼ eᵢʳ 1_λ`, the `r`-th word of `UDot.Free.serreE`. -/
def serreEPhase (i j : I) (r : ℕ) (μ : X) : kˣ :=
  ePowPhase D c i (D.serreDeg i j - r) (μ + r • D.α i + D.α j) * c j (μ + r • D.α i) *
    ePowPhase D c i r μ

/-- The phase of `fᵢ^{N-r} fⱼ fᵢʳ 1_λ`, the `r`-th word of `UDot.Free.serreF`. -/
def serreFPhase (i j : I) (r : ℕ) (μ : X) : kˣ :=
  fPowPhase D c i (D.serreDeg i j - r) (μ - r • D.α i - D.α j) * c j (μ - r • D.α i) *
    fPowPhase D c i r μ

/-- The phase of a signed word with right weight `λ`, mirroring `UDot.halfWord`. -/
def halfPhase (positive : Bool) : List I → X → kˣ
  | [], _ => 1
  | i :: w, μ => c i (μ + halfWeight D positive (PreF.wordWeight w)) * halfPhase positive w μ

theorem ePowPhase_inv (i : I) (n : ℕ) (μ : X) :
    ePowPhase D (fun i μ ↦ (c i μ)⁻¹) i n μ = (ePowPhase D c i n μ)⁻¹ := by
  induction n with
  | zero => simp [ePowPhase]
  | succ n ih => simp only [ePowPhase, ih, mul_inv]

theorem fPowPhase_inv (i : I) (n : ℕ) (μ : X) :
    fPowPhase D (fun i μ ↦ (c i μ)⁻¹) i n μ = (fPowPhase D c i n μ)⁻¹ := by
  induction n with
  | zero => simp [fPowPhase]
  | succ n ih => simp only [fPowPhase, ih, mul_inv]

theorem serreEPhase_inv (i j : I) (r : ℕ) (μ : X) :
    serreEPhase D (fun i μ ↦ (c i μ)⁻¹) i j r μ = (serreEPhase D c i j r μ)⁻¹ := by
  simp only [serreEPhase, ePowPhase_inv, mul_inv]

theorem serreFPhase_inv (i j : I) (r : ℕ) (μ : X) :
    serreFPhase D (fun i μ ↦ (c i μ)⁻¹) i j r μ = (serreFPhase D c i j r μ)⁻¹ := by
  simp only [serreFPhase, fPowPhase_inv, mul_inv]

theorem halfPhase_inv (positive : Bool) (w : List I) (μ : X) :
    halfPhase D (fun i μ ↦ (c i μ)⁻¹) positive w μ = (halfPhase D c positive w μ)⁻¹ := by
  induction w with
  | nil => simp [halfPhase]
  | cons i w ih => simp only [halfPhase, ih, mul_inv]

end Phases

variable [DecidableEq I] [DecidableEq X]

/-- The scalar conditions under which rescaling `eᵢ1_λ ↦ cE i λ • eᵢ1_λ`,
`fᵢ1_λ ↦ cF i λ • fᵢ1_λ` respects the relations (9.2)–(9.4). -/
structure GaugeCompatible (q₁ : kˣ) (π₁ : k) (q₂ : kˣ) (π₂ : k) (cE cF : I → X → kˣ) :
    Prop where
  /-- (9.2), the `fⱼ eᵢ` coefficient. -/
  comm : ∀ i j μ, ((cE i (μ - D.α j) * cF j μ : kˣ) : k) * π₂ ^ (D.parity i * D.parity j).val =
    π₁ ^ (D.parity i * D.parity j).val * ((cF j (μ + D.α i) * cE i μ : kˣ) : k)
  /-- (9.2), the `1_λ` coefficient. -/
  comm_self : ∀ i μ, ((cE i (μ - D.α i) * cF i μ : kˣ) : k) *
    qpInt (D.qi q₂ i) (D.pii π₂ i) (D.h i μ) = qpInt (D.qi q₁ i) (D.pii π₁ i) (D.h i μ)
  /-- (9.3). -/
  serreE : ∀ i j, i ≠ j → ∀ μ, ∃ u : kˣ, ∀ r ≤ D.serreDeg i j,
    D.serreCoeff q₁ π₁ i j r * (serreEPhase D cE i j r μ : k) = u * D.serreCoeff q₂ π₂ i j r
  /-- (9.4). -/
  serreF : ∀ i j, i ≠ j → ∀ μ, ∃ u : kˣ, ∀ r ≤ D.serreDeg i j,
    D.serreCoeff q₁ π₁ i j r * (serreFPhase D cF i j r μ : k) = u * D.serreCoeff q₂ π₂ i j r

variable {D} {q₁ : kˣ} {π₁ : k} {q₂ : kˣ} {π₂ : k} {cE cF : I → X → kˣ}

private theorem unit_comm_inv {A B : kˣ} {P₁ P₂ : k} (h : (A : k) * P₂ = P₁ * B) :
    ((A⁻¹ : kˣ) : k) * P₁ = P₂ * ((B⁻¹ : kˣ) : k) := by
  have hA : (A : k) * ((A⁻¹ : kˣ) : k) = 1 := by simp
  have hB : (B : k) * ((B⁻¹ : kˣ) : k) = 1 := by simp
  linear_combination (-(((A⁻¹ : kˣ) : k) * ((B⁻¹ : kˣ) : k))) * h +
    (P₂ * ((B⁻¹ : kˣ) : k)) * hA - (((A⁻¹ : kˣ) : k) * P₁) * hB

private theorem unit_scale_inv {A u : kˣ} {P₁ P₂ : k} (h : P₁ * (A : k) = u * P₂) :
    P₂ * ((A⁻¹ : kˣ) : k) = ((u⁻¹ : kˣ) : k) * P₁ := by
  have hA : (A : k) * ((A⁻¹ : kˣ) : k) = 1 := by simp
  have hu : (u : k) * ((u⁻¹ : kˣ) : k) = 1 := by simp
  linear_combination (-(((A⁻¹ : kˣ) : k) * ((u⁻¹ : kˣ) : k))) * h +
    (((u⁻¹ : kˣ) : k) * P₁) * hA - (P₂ * ((A⁻¹ : kˣ) : k)) * hu

omit [DecidableEq I] [DecidableEq X] in
/-- The inverse rescaling satisfies the conditions in the opposite direction. -/
theorem GaugeCompatible.inv (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) :
    GaugeCompatible D q₂ π₂ q₁ π₁ (fun i μ ↦ (cE i μ)⁻¹) (fun i μ ↦ (cF i μ)⁻¹) where
  comm i j μ := by
    simp only [← mul_inv]
    exact unit_comm_inv (hc.comm i j μ)
  comm_self i μ := by
    simp only [← mul_inv]
    rw [← hc.comm_self i μ, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul]
  serreE i j hij μ := by
    obtain ⟨u, hu⟩ := hc.serreE i j hij μ
    exact ⟨u⁻¹, fun r hr ↦ by rw [serreEPhase_inv]; exact unit_scale_inv (hu r hr)⟩
  serreF i j hij μ := by
    obtain ⟨u, hu⟩ := hc.serreF i j hij μ
    exact ⟨u⁻¹, fun r hr ↦ by rw [serreFPhase_inv]; exact unit_scale_inv (hu r hr)⟩

variable (D q₂ π₂ cE cF)

/-- The rescaling on generators. -/
def gaugeGen : Gen I X → CoveringUDot k D q₂ π₂
  | .one μ => one D q₂ π₂ μ
  | .e i μ => (cE i μ : k) • E D q₂ π₂ i μ
  | .f i μ => (cF i μ : k) • F D q₂ π₂ i μ

/-- The rescaling on the free algebra. -/
def gaugeFree : Free k I X →ₐ[k] CoveringUDot k D q₂ π₂ :=
  FreeAlgebra.lift k (gaugeGen D q₂ π₂ cE cF)

variable {D q₂ π₂ cE cF}

@[simp] theorem gaugeFree_one (μ : X) :
    gaugeFree D q₂ π₂ cE cF (Free.one k μ) = one D q₂ π₂ μ := by
  simp [gaugeFree, Free.one, gaugeGen]

@[simp] theorem gaugeFree_E (i : I) (μ : X) :
    gaugeFree D q₂ π₂ cE cF (Free.E k i μ) = (cE i μ : k) • E D q₂ π₂ i μ := by
  simp [gaugeFree, Free.E, gaugeGen]

@[simp] theorem gaugeFree_F (i : I) (μ : X) :
    gaugeFree D q₂ π₂ cE cF (Free.F k i μ) = (cF i μ : k) • F D q₂ π₂ i μ := by
  simp [gaugeFree, Free.F, gaugeGen]

theorem gaugeFree_epow (i : I) (n : ℕ) (μ : X) :
    gaugeFree D q₂ π₂ cE cF (epow D i n μ) =
      (ePowPhase D cE i n μ : k) • mk D q₂ π₂ (epow D i n μ) := by
  induction n with
  | zero => simp [epow, ePowPhase, one]
  | succ n ih =>
    rw [epow, map_mul, ih, gaugeFree_E, smul_mul_smul_comm, map_mul, ePowPhase, Units.val_mul]
    rfl

theorem gaugeFree_fpow (i : I) (n : ℕ) (μ : X) :
    gaugeFree D q₂ π₂ cE cF (fpow D i n μ) =
      (fPowPhase D cF i n μ : k) • mk D q₂ π₂ (fpow D i n μ) := by
  induction n with
  | zero => simp [fpow, fPowPhase, one]
  | succ n ih =>
    rw [fpow, map_mul, ih, gaugeFree_F, smul_mul_smul_comm, map_mul, fPowPhase, Units.val_mul]
    rfl

theorem gaugeFree_rel (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) {x y : Free k I X}
    (h : Rel D q₁ π₁ x y) : gaugeFree D q₂ π₂ cE cF x = gaugeFree D q₂ π₂ cE cF y := by
  cases h with
  | one_one μ ν =>
    rw [map_mul, gaugeFree_one, gaugeFree_one, one_mul_one]
    split_ifs <;> simp
  | one_E i μ =>
    rw [map_mul, gaugeFree_one, gaugeFree_E, mul_smul_comm, one_mul_E_self]
  | E_one i μ =>
    rw [map_mul, gaugeFree_one, gaugeFree_E, smul_mul_assoc, E_mul_one_self]
  | one_F i μ =>
    rw [map_mul, gaugeFree_one, gaugeFree_F, mul_smul_comm, one_mul_F_self]
  | F_one i μ =>
    rw [map_mul, gaugeFree_one, gaugeFree_F, smul_mul_assoc, F_mul_one_self]
  | comm i j μ =>
    have hEF := eq_add_of_sub_eq (comm_rel D q₂ π₂ i j μ)
    rw [map_sub, map_mul, map_smul, map_mul, gaugeFree_E, gaugeFree_F, gaugeFree_E, gaugeFree_F,
      smul_mul_smul_comm, smul_mul_smul_comm, hEF, smul_add, smul_smul, smul_smul, add_sub_assoc,
      ← sub_smul, ← Units.val_mul, ← Units.val_mul, hc.comm i j μ, sub_self, zero_smul, add_zero]
    split_ifs with hij
    · subst hij
      rw [smul_smul, hc.comm_self, map_smul, gaugeFree_one]
    · simp
  | serreE i j μ hij =>
    obtain ⟨u, hu⟩ := hc.serreE i j hij μ
    rw [map_zero, serreE, map_sum]
    have key : ∀ r ∈ range (D.serreDeg i j + 1),
        gaugeFree D q₂ π₂ cE cF (D.serreCoeff q₁ π₁ i j r •
          (epow D i (D.serreDeg i j - r) (μ + r • D.α i + D.α j) * Free.E k j (μ + r • D.α i) *
            epow D i r μ)) =
        (u : k) • mk D q₂ π₂ (D.serreCoeff q₂ π₂ i j r •
          (epow D i (D.serreDeg i j - r) (μ + r • D.α i + D.α j) * Free.E k j (μ + r • D.α i) *
            epow D i r μ)) := by
      intro r hr
      rw [map_smul, map_mul, map_mul, gaugeFree_epow, gaugeFree_E, gaugeFree_epow,
        smul_mul_smul_comm, smul_mul_smul_comm, smul_smul, map_smul, smul_smul, map_mul, map_mul,
        ← hu r (Nat.lt_succ_iff.mp (mem_range.mp hr)), serreEPhase]
      simp only [Units.val_mul]
      rfl
    rw [sum_congr rfl key, ← smul_sum, ← map_sum]
    exact (congrArg _ (serreE_rel D q₂ π₂ hij μ)).trans (smul_zero _)
  | serreF i j μ hij =>
    obtain ⟨u, hu⟩ := hc.serreF i j hij μ
    rw [map_zero, serreF, map_sum]
    have key : ∀ r ∈ range (D.serreDeg i j + 1),
        gaugeFree D q₂ π₂ cE cF (D.serreCoeff q₁ π₁ i j r •
          (fpow D i (D.serreDeg i j - r) (μ - r • D.α i - D.α j) * Free.F k j (μ - r • D.α i) *
            fpow D i r μ)) =
        (u : k) • mk D q₂ π₂ (D.serreCoeff q₂ π₂ i j r •
          (fpow D i (D.serreDeg i j - r) (μ - r • D.α i - D.α j) * Free.F k j (μ - r • D.α i) *
            fpow D i r μ)) := by
      intro r hr
      rw [map_smul, map_mul, map_mul, gaugeFree_fpow, gaugeFree_F, gaugeFree_fpow,
        smul_mul_smul_comm, smul_mul_smul_comm, smul_smul, map_smul, smul_smul, map_mul, map_mul,
        ← hu r (Nat.lt_succ_iff.mp (mem_range.mp hr)), serreFPhase]
      simp only [Units.val_mul]
      rfl
    rw [sum_congr rfl key, ← smul_sum, ← map_sum]
    exact (congrArg _ (serreF_rel D q₂ π₂ hij μ)).trans (smul_zero _)

variable (D q₂ π₂ cE cF)

/-- The algebra map `U̇_{q₁,π₁} → U̇_{q₂,π₂}` rescaling the Chevalley generators. -/
def gauge (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) :
    CoveringUDot k D q₁ π₁ →ₐ[k] CoveringUDot k D q₂ π₂ :=
  RingQuot.liftAlgHom k ⟨gaugeFree D q₂ π₂ cE cF, fun _ _ h ↦ gaugeFree_rel hc h⟩

variable {D q₂ π₂ cE cF}

theorem gauge_mk (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) (x : Free k I X) :
    gauge D q₂ π₂ cE cF hc (mk D q₁ π₁ x) = gaugeFree D q₂ π₂ cE cF x := by
  simp only [gauge, mk, RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem gauge_one (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) (μ : X) :
    gauge D q₂ π₂ cE cF hc (one D q₁ π₁ μ) = one D q₂ π₂ μ := by
  rw [one, gauge_mk, gaugeFree_one]

@[simp] theorem gauge_E (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) (i : I) (μ : X) :
    gauge D q₂ π₂ cE cF hc (E D q₁ π₁ i μ) = (cE i μ : k) • E D q₂ π₂ i μ := by
  rw [E, gauge_mk, gaugeFree_E]

@[simp] theorem gauge_F (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) (i : I) (μ : X) :
    gauge D q₂ π₂ cE cF hc (F D q₁ π₁ i μ) = (cF i μ : k) • F D q₂ π₂ i μ := by
  rw [F, gauge_mk, gaugeFree_F]

/-- A positive word is multiplied by its `cE`-phase. -/
theorem gauge_halfWord_true (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) (w : List I) (μ : X) :
    gauge D q₂ π₂ cE cF hc (halfWord D q₁ π₁ true w μ) =
      (halfPhase D cE true w μ : k) • halfWord D q₂ π₂ true w μ := by
  induction w with
  | nil => simp [halfWord, halfPhase]
  | cons i w ih =>
    simp only [halfWord, halfPhase, map_mul, ih, halfGen, ite_true, gauge_E, smul_mul_smul_comm,
      Units.val_mul]

/-- A negative word is multiplied by its `cF`-phase. -/
theorem gauge_halfWord_false (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) (w : List I) (μ : X) :
    gauge D q₂ π₂ cE cF hc (halfWord D q₁ π₁ false w μ) =
      (halfPhase D cF false w μ : k) • halfWord D q₂ π₂ false w μ := by
  induction w with
  | nil => simp [halfWord, halfPhase]
  | cons i w ih =>
    simp only [halfWord, halfPhase, map_mul, ih, halfGen, Bool.false_eq_true, ite_false, gauge_F,
      smul_mul_smul_comm, Units.val_mul]

theorem gauge_mem_block (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) {μ η : X}
    {x : CoveringUDot k D q₁ π₁} (hx : x ∈ block D q₁ π₁ μ η) :
    gauge D q₂ π₂ cE cF hc x ∈ block D q₂ π₂ μ η := by
  constructor
  · have := congrArg (gauge D q₂ π₂ cE cF hc) hx.1
    rwa [map_mul, gauge_one] at this
  · have := congrArg (gauge D q₂ π₂ cE cF hc) hx.2
    rwa [map_mul, gauge_one] at this

/-- The rescaling restricts to the nonunital modified algebras. -/
theorem gauge_mem_modified (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF)
    {x : CoveringUDot k D q₁ π₁} (hx : x ∈ modified D q₁ π₁) :
    gauge D q₂ π₂ cE cF hc x ∈ modified D q₂ π₂ := by
  refine Submodule.iSup_induction (fun b : X × X ↦ block D q₁ π₁ b.1 b.2)
    (motive := fun x ↦ gauge D q₂ π₂ cE cF hc x ∈ modified D q₂ π₂) hx ?_ ?_ ?_
  · intro b x hx
    exact block_le_modified D q₂ π₂ b.1 b.2 (gauge_mem_block hc hx)
  · simp only [map_zero]; exact zero_mem _
  · intro x y hx hy
    simpa only [map_add] using add_mem hx hy

theorem gauge_inv_gauge (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) :
    (gauge D q₁ π₁ _ _ hc.inv).comp (gauge D q₂ π₂ cE cF hc) = AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | one μ =>
    change gauge D q₁ π₁ _ _ hc.inv (gauge D q₂ π₂ cE cF hc (one D q₁ π₁ μ)) = one D q₁ π₁ μ
    simp
  | e i μ =>
    change gauge D q₁ π₁ _ _ hc.inv (gauge D q₂ π₂ cE cF hc (E D q₁ π₁ i μ)) = E D q₁ π₁ i μ
    rw [gauge_E, map_smul, gauge_E, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]
  | f i μ =>
    change gauge D q₁ π₁ _ _ hc.inv (gauge D q₂ π₂ cE cF hc (F D q₁ π₁ i μ)) = F D q₁ π₁ i μ
    rw [gauge_F, map_smul, gauge_F, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]

theorem gauge_gauge_inv (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) :
    (gauge D q₂ π₂ cE cF hc).comp (gauge D q₁ π₁ _ _ hc.inv) = AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | one μ =>
    change gauge D q₂ π₂ cE cF hc (gauge D q₁ π₁ _ _ hc.inv (one D q₂ π₂ μ)) = one D q₂ π₂ μ
    simp
  | e i μ =>
    change gauge D q₂ π₂ cE cF hc (gauge D q₁ π₁ _ _ hc.inv (E D q₂ π₂ i μ)) = E D q₂ π₂ i μ
    rw [gauge_E, map_smul, gauge_E, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]
  | f i μ =>
    change gauge D q₂ π₂ cE cF hc (gauge D q₁ π₁ _ _ hc.inv (F D q₂ π₂ i μ)) = F D q₂ π₂ i μ
    rw [gauge_F, map_smul, gauge_F, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]

variable (D q₂ π₂ cE cF)

/-- The rescaling as an algebra isomorphism; its inverse rescales by the inverse units. -/
def gaugeEquiv (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF) :
    CoveringUDot k D q₁ π₁ ≃ₐ[k] CoveringUDot k D q₂ π₂ :=
  AlgEquiv.ofAlgHom (gauge D q₂ π₂ cE cF hc) (gauge D q₁ π₁ _ _ hc.inv)
    (gauge_gauge_inv hc) (gauge_inv_gauge hc)

variable {D q₂ π₂ cE cF}

@[simp] theorem gaugeEquiv_apply (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF)
    (x : CoveringUDot k D q₁ π₁) : gaugeEquiv D q₂ π₂ cE cF hc x = gauge D q₂ π₂ cE cF hc x :=
  rfl

@[simp] theorem gaugeEquiv_symm_apply (hc : GaugeCompatible D q₁ π₁ q₂ π₂ cE cF)
    (x : CoveringUDot k D q₂ π₂) :
    (gaugeEquiv D q₂ π₂ cE cF hc).symm x = gauge D q₁ π₁ _ _ hc.inv x :=
  rfl

end OddMath.CoveringQuantum.UDot
