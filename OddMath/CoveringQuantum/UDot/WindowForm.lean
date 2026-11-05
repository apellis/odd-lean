/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.FiniteWeightForm
import OddMath.CoveringQuantum.SerreRestrict

/-!
# Finite weight windows of the modified covering algebra

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1 allows an arbitrary
colour set `I` and the weight lattice `P = {λ ∈ 𝔥* | ⟨hᵢ, λ⟩ ∈ ℤ}` of a complex realization.
This file compares the modified covering algebra `U̇` of §9 with the algebras of its finite
weight windows (`RootDatum.weightWindow`): a finite set of colours together with a finitely
generated sublattice containing their roots and finitely many chosen weights.

* `windowHom` is the algebra homomorphism induced by the inclusions of colours and weights; it
  sends blocks to blocks and commutes with `ρ` and `ψ` of §9.
* `positiveModifiedForm_modifiedHom`, `sesquilinearForm_modifiedHom`: the forms of Theorem 10.1
  are compatible with it (by the uniqueness characterization of the form).
* `exists_modifiedHom_eq`: every element of `U̇` comes from some window.
* `sesquilinearForm_nondegenerate_of_windows`: if the form is nondegenerate on every window,
  it is nondegenerate on `U̇`.
* `sesquilinearForm_nondegenerate_of_separating`: the form of Theorem 10.1 is nondegenerate for
  a torsion-free weight group with independent roots and integral weights separating the
  coroots, for an arbitrary (possibly infinite) colour set.
* `sourceWeightLattice_nondegenerate`: hence it is nondegenerate on BE2's own
  weight lattice `P` of a complex realization with independent roots and coroots.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot.WindowForm

open Coefficients PreF GenericTensor

variable {k I X : Type*} [CommRing k] [AddCommGroup X]
variable (D : RootDatum I X) (ω : I → X)

/-- The weight lattice of the window on the colours `J` and seed weights `W`. -/
abbrev Lat (J : Finset I) (W : Finset X) : Submodule ℤ X :=
  FiniteWeightWindow.lattice W (fun j : J ↦ D.α j) (fun j : J ↦ ω j)

/-- The root datum of the window on the colours `J` and seed weights `W`. -/
abbrev Dw (J : Finset I) (W : Finset X) : RootDatum J (Lat D ω J W) :=
  D.weightWindow J W (fun j : J ↦ ω j)

variable (J : Finset I) (W : Finset X)

@[simp] theorem Dw_d (i : J) : (Dw D ω J W).d i = D.d i := rfl

@[simp] theorem Dw_parity (i : J) : (Dw D ω J W).parity i = D.parity i := rfl

@[simp] theorem Dw_qi (q : kˣ) (i : J) : (Dw D ω J W).qi q i = D.qi q (i : I) := rfl

@[simp] theorem Dw_pii (π : k) (i : J) : (Dw D ω J W).pii π i = D.pii π (i : I) := rfl

@[simp] theorem Dw_parl (i : J) (μ : Lat D ω J W) :
    (Dw D ω J W).parl i μ = D.parl (i : I) (μ : X) := rfl

@[simp] theorem coe_Dw_α (i : J) : (((Dw D ω J W).α i : Lat D ω J W) : X) = D.α (i : I) := rfl

variable (k) in
/-- Relabel the free generators along the inclusions of colours and weights. -/
def freeInclude : Free k J (Lat D ω J W) →ₐ[k] Free k I X :=
  FreeAlgebra.lift k fun g ↦ match g with
    | .one μ => Free.one k (μ : X)
    | .e i μ => Free.E k (i : I) (μ : X)
    | .f i μ => Free.F k (i : I) (μ : X)

@[simp] theorem freeInclude_one (μ : Lat D ω J W) :
    freeInclude k D ω J W (Free.one k μ) = Free.one k (μ : X) := by
  simp [freeInclude, Free.one]

@[simp] theorem freeInclude_E (i : J) (μ : Lat D ω J W) :
    freeInclude k D ω J W (Free.E k i μ) = Free.E k (i : I) (μ : X) := by
  simp [freeInclude, Free.E]

@[simp] theorem freeInclude_F (i : J) (μ : Lat D ω J W) :
    freeInclude k D ω J W (Free.F k i μ) = Free.F k (i : I) (μ : X) := by
  simp [freeInclude, Free.F]

@[simp] theorem freeInclude_epow (i : J) (n : ℕ) (μ : Lat D ω J W) :
    freeInclude k D ω J W (epow (Dw D ω J W) i n μ) = epow D (i : I) n (μ : X) := by
  induction n with
  | zero => simp [epow]
  | succ n ih => simp [epow, ih]

@[simp] theorem freeInclude_fpow (i : J) (n : ℕ) (μ : Lat D ω J W) :
    freeInclude k D ω J W (fpow (Dw D ω J W) i n μ) = fpow D (i : I) n (μ : X) := by
  induction n with
  | zero => simp [fpow]
  | succ n ih => simp [fpow, ih]

variable (q : kˣ) (π : k)

theorem freeInclude_serreE (i j : J) (μ : Lat D ω J W) :
    freeInclude k D ω J W (serreE (Dw D ω J W) q π i j μ) =
      serreE D q π (i : I) (j : I) (μ : X) := by
  simp only [serreE, map_sum, map_smul, map_mul, freeInclude_epow, freeInclude_E,
    Submodule.coe_add, Submodule.coe_smul_of_tower, coe_Dw_α]
  rfl

theorem freeInclude_serreF (i j : J) (μ : Lat D ω J W) :
    freeInclude k D ω J W (serreF (Dw D ω J W) q π i j μ) =
      serreF D q π (i : I) (j : I) (μ : X) := by
  simp only [serreF, map_sum, map_smul, map_mul, freeInclude_fpow, freeInclude_F,
    Submodule.coe_sub, Submodule.coe_smul_of_tower, coe_Dw_α]
  rfl

variable [DecidableEq I] [DecidableEq X]

/-- Every defining relation of the window is a defining relation of `U̇`. -/
theorem rel_freeInclude {x y : Free k J (Lat D ω J W)} (h : Rel (Dw D ω J W) q π x y) :
    Rel D q π (freeInclude k D ω J W x) (freeInclude k D ω J W y) := by
  cases h with
  | one_one μ ν =>
    simpa only [map_mul, freeInclude_one, apply_ite, map_zero, Subtype.coe_inj] using
      (Rel.one_one (D := D) (q := q) (π := π) (μ : X) (ν : X))
  | one_E i μ =>
    simpa only [map_mul, freeInclude_one, freeInclude_E, Submodule.coe_add, coe_Dw_α] using
      (Rel.one_E (D := D) (q := q) (π := π) (i : I) (μ : X))
  | E_one i μ =>
    simpa only [map_mul, freeInclude_one, freeInclude_E] using
      (Rel.E_one (D := D) (q := q) (π := π) (i : I) (μ : X))
  | one_F i μ =>
    simpa only [map_mul, freeInclude_one, freeInclude_F, Submodule.coe_sub, coe_Dw_α] using
      (Rel.one_F (D := D) (q := q) (π := π) (i : I) (μ : X))
  | F_one i μ =>
    simpa only [map_mul, freeInclude_one, freeInclude_F] using
      (Rel.F_one (D := D) (q := q) (π := π) (i : I) (μ : X))
  | comm i j μ =>
    simpa only [map_sub, map_mul, map_smul, apply_ite, map_zero, freeInclude_one,
      freeInclude_E, freeInclude_F, Submodule.coe_add, Submodule.coe_sub, coe_Dw_α,
      Dw_parity, Dw_qi, Dw_pii, RootDatum.weightWindow_h, Subtype.coe_inj] using
      (Rel.comm (D := D) (q := q) (π := π) (i : I) (j : I) (μ : X))
  | serreE i j μ h =>
    rw [freeInclude_serreE, map_zero]
    exact Rel.serreE (i : I) (j : I) (μ : X) (fun he ↦ h (Subtype.ext he))
  | serreF i j μ h =>
    rw [freeInclude_serreF, map_zero]
    exact Rel.serreF (i : I) (j : I) (μ : X) (fun he ↦ h (Subtype.ext he))

/-- The homomorphism from the unital envelope of a window. -/
def windowHom : CoveringUDot k (Dw D ω J W) q π →ₐ[k] CoveringUDot k D q π :=
  RingQuot.liftAlgHom k ⟨(mk D q π).comp (freeInclude k D ω J W), fun _ _ h ↦
    mk_rel D q π (rel_freeInclude D ω J W q π h)⟩

@[simp] theorem windowHom_mk (x : Free k J (Lat D ω J W)) :
    windowHom D ω J W q π (mk (Dw D ω J W) q π x) = mk D q π (freeInclude k D ω J W x) := by
  simp only [windowHom, mk, RingQuot.liftAlgHom_mkAlgHom_apply, AlgHom.comp_apply]

@[simp] theorem windowHom_one (μ : Lat D ω J W) :
    windowHom D ω J W q π (one (Dw D ω J W) q π μ) = one D q π (μ : X) := by
  rw [one, windowHom_mk, freeInclude_one]
  rfl

@[simp] theorem windowHom_E (i : J) (μ : Lat D ω J W) :
    windowHom D ω J W q π (E (Dw D ω J W) q π i μ) = E D q π (i : I) (μ : X) := by
  rw [E, windowHom_mk, freeInclude_E]
  rfl

@[simp] theorem windowHom_F (i : J) (μ : Lat D ω J W) :
    windowHom D ω J W q π (F (Dw D ω J W) q π i μ) = F D q π (i : I) (μ : X) := by
  rw [F, windowHom_mk, freeInclude_F]
  rfl

theorem windowHom_mem_block {μ η : Lat D ω J W} {x : CoveringUDot k (Dw D ω J W) q π}
    (hx : x ∈ block (Dw D ω J W) q π μ η) :
    windowHom D ω J W q π x ∈ block D q π (μ : X) (η : X) := by
  constructor
  · rw [← windowHom_one, ← map_mul, hx.1]
  · rw [← windowHom_one, ← map_mul, hx.2]

theorem windowHom_mem_modified {x : CoveringUDot k (Dw D ω J W) q π}
    (hx : x ∈ modified (Dw D ω J W) q π) : windowHom D ω J W q π x ∈ modified D q π := by
  refine Submodule.iSup_induction (fun b : Lat D ω J W × Lat D ω J W ↦
      block (Dw D ω J W) q π b.1 b.2)
    (motive := fun x ↦ windowHom D ω J W q π x ∈ modified D q π) hx ?_ ?_ ?_
  · intro b x hx
    exact block_le_modified D q π _ _ (windowHom_mem_block D ω J W q π hx)
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

/-- The window homomorphism on BE2's nonunital modified algebras. -/
def modifiedHom : modified (Dw D ω J W) q π →ₗ[k] modified D q π where
  toFun x := ⟨windowHom D ω J W q π x, windowHom_mem_modified D ω J W q π x.property⟩
  map_add' x y := Subtype.ext (map_add (windowHom D ω J W q π) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (windowHom D ω J W q π) c x.1)

@[simp] theorem coe_modifiedHom (x : modified (Dw D ω J W) q π) :
    (modifiedHom D ω J W q π x : CoveringUDot k D q π) = windowHom D ω J W q π x := rfl

theorem modifiedHom_mul (x y : modified (Dw D ω J W) q π) :
    modifiedHom D ω J W q π (x * y) = modifiedHom D ω J W q π x * modifiedHom D ω J W q π y :=
  Subtype.ext (map_mul (windowHom D ω J W q π) x.1 y.1)

/-- The window homomorphism commutes with the antiautomorphism `ρ` of §9. -/
theorem windowHom_rho (hπ : π ^ 2 = 1) (x : CoveringUDot k (Dw D ω J W) q π) :
    windowHom D ω J W q π (rho (Dw D ω J W) q π hπ x).unop =
      (rho D q π hπ (windowHom D ω J W q π x)).unop := by
  obtain ⟨x, rfl⟩ := mk_surjective (Dw D ω J W) q π x
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  | grade1 g =>
    cases g with
    | one μ =>
      rw [← Free.one, ← one]
      simp only [rho_one, windowHom_one]
    | e i μ =>
      rw [← Free.E, ← E]
      simp only [rho_E, map_smul, windowHom_E, windowHom_F, Submodule.coe_add, coe_Dw_α,
        Dw_d, RootDatum.weightWindow_h]
    | f i μ =>
      rw [← Free.F, ← F]
      simp only [rho_F, map_smul, windowHom_E, windowHom_F, Submodule.coe_sub, coe_Dw_α,
        Dw_d, RootDatum.weightWindow_h]
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, MulOpposite.unop_mul, ha, hb]

/-- The window homomorphism commutes with the scalar-bar automorphism `ψ` of §9. -/
theorem windowHom_psi (σ : k →+* k) (hσ : BarData q π σ)
    (x : CoveringUDot k (Dw D ω J W) q π) :
    windowHom D ω J W q π (psi (Dw D ω J W) q π σ hσ x) =
      psi D q π σ hσ (windowHom D ω J W q π x) := by
  obtain ⟨x, rfl⟩ := mk_surjective (Dw D ω J W) q π x
  induction x using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes, psi_algebraMap]
  | grade1 g =>
    cases g with
    | one μ =>
      rw [← Free.one, ← one]
      simp only [psi_one, windowHom_one]
    | e i μ =>
      rw [← Free.E, ← E]
      simp only [psi_E, windowHom_E]
    | f i μ =>
      rw [← Free.F, ← F]
      simp only [psi_F, map_smul, windowHom_F, Dw_parl]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

theorem modifiedHom_rho (hπ : π ^ 2 = 1) (x : modified (Dw D ω J W) q π) :
    modifiedHom D ω J W q π (rhoModified (Dw D ω J W) q π hπ x) =
      rhoModified D q π hπ (modifiedHom D ω J W q π x) :=
  Subtype.ext (windowHom_rho D ω J W q π hπ x.val)

theorem modifiedHom_psi (x : modified (Dw D ω J W) Coefficients.q pi) :
    modifiedHom D ω J W Coefficients.q pi (psiModified (Dw D ω J W) x) =
      psiModified D (modifiedHom D ω J W Coefficients.q pi x) :=
  Subtype.ext (windowHom_psi D ω J W Coefficients.q pi bar barData x.val)

omit [DecidableEq I] [DecidableEq X] in
theorem coe_halfWeight (positive : Bool) (w : List J) :
    ((halfWeight (Dw D ω J W) positive (PreF.wordWeight w) : Lat D ω J W) : X) =
      halfWeight D positive (PreF.wordWeight (w.map Subtype.val)) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [PreF.wordWeight_cons, halfWeight_add, halfWeight_single, List.map_cons,
      Submodule.coe_add, ih, halfRoot]
    cases positive <;> simp

/-- The window homomorphism sends each signed word to the same word of colours. -/
theorem windowHom_halfWord (positive : Bool) (w : List J) (μ : Lat D ω J W) :
    windowHom D ω J W q π (halfWord (Dw D ω J W) q π positive w μ) =
      halfWord D q π positive (w.map Subtype.val) (μ : X) := by
  induction w with
  | nil => exact windowHom_one D ω J W q π μ
  | cons i w ih =>
    simp only [halfWord, List.map_cons, map_mul, ih]
    congr 1
    cases positive <;>
      simp only [halfGen, Bool.false_eq_true, ↓reduceIte, windowHom_E, windowHom_F,
        Submodule.coe_add, coe_halfWeight]

/-- The window's Serre half algebra is the restriction of the datum to the colours `J`. -/
abbrev serreWindow : (Dw D ω J W).serreF q π →ₐ[k] D.serreF q π :=
  D.toSuperCartanDatum.serreRestrict ((↑) : J → I) Subtype.val_injective q π

omit [DecidableEq I] [DecidableEq X] in
theorem serreWindow_toSerreF (x : PreF k J) :
    serreWindow D ω J W q π ((Dw D ω J W).toSerreF q π x) =
      D.toSerreF q π (PreF.incl k ((↑) : J → I) x) :=
  D.toSuperCartanDatum.serreRestrict_toSerreF _ Subtype.val_injective q π x

omit [DecidableEq I] [DecidableEq X] in
theorem incl_monomial (w : List J) :
    PreF.incl k ((↑) : J → I) (PreF.monomial k w) = PreF.monomial k (w.map Subtype.val) := by
  induction w with
  | nil => simp [PreF.monomial]
  | cons i w ih => simp only [PreF.monomial_cons, map_mul, PreF.incl_θ, ih, List.map_cons]

/-- The window homomorphism sends the positive half to the positive half. -/
theorem modifiedHom_positiveHalf (μ : Lat D ω J W) (x : (Dw D ω J W).serreF q π) :
    modifiedHom D ω J W q π (positiveHalf (Dw D ω J W) q π μ x) =
      positiveHalf D q π (μ : X) (serreWindow D ω J W q π x) := by
  obtain ⟨x, rfl⟩ := (Dw D ω J W).toSerreF_surjective q π x
  induction x using induction_monomial with
  | word w =>
    apply Subtype.ext
    change windowHom D ω J W q π (halfMap (Dw D ω J W) q π true μ _) =
      halfMap D q π true _ _
    rw [halfMap_monomial, serreWindow_toSerreF, incl_monomial, halfMap_monomial,
      windowHom_halfWord]
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

omit [DecidableEq X] in
/-- The Serre form of the window is the restriction of the Serre form of `D`. -/
theorem serreForm_serreWindow (hπ : π ^ 2 = 1) (x y : (Dw D ω J W).serreF q π) :
    D.serreForm q π hπ (serreWindow D ω J W q π x) (serreWindow D ω J W q π y) =
      (Dw D ω J W).serreForm q π hπ x y := by
  obtain ⟨x, rfl⟩ := (Dw D ω J W).toSerreF_surjective q π x
  obtain ⟨y, rfl⟩ := (Dw D ω J W).toSerreF_surjective q π y
  rw [serreWindow_toSerreF, serreWindow_toSerreF, SuperCartanDatum.serreForm_toSerreF,
    SuperCartanDatum.serreForm_toSerreF]
  exact PreF.form_incl (D.chi q π) ((Dw D ω J W).chi q π) ((↑) : J → I) (fun _ _ ↦ rfl)
    (D.norm q π) ((Dw D ω J W).norm q π) (fun _ ↦ rfl) Subtype.val_injective x y

/-- The window homomorphism preserves the positive-normalized form of Theorem 10.1. -/
theorem positiveModifiedForm_modifiedHom (x y : modified (Dw D ω J W) Coefficients.q pi) :
    positiveModifiedForm D (modifiedHom D ω J W Coefficients.q pi x)
      (modifiedHom D ω J W Coefficients.q pi y) = positiveModifiedForm (Dw D ω J W) x y := by
  let e := modifiedHom D ω J W Coefficients.q pi
  let B : LinearMap.BilinForm Coefficients.Ring (modified (Dw D ω J W) Coefficients.q pi) :=
    (positiveModifiedForm D).compl₁₂ e e
  have he : B = positiveModifiedForm (Dw D ω J W) := by
    apply positiveModifiedForm_unique (Dw D ω J W) B
    · intro μ ν μ' ν' a b ha hb hn
      apply positiveModifiedForm_orthogonal D (μ : X) (ν : X) (μ' : X) (ν' : X)
        (e a) (e b) (windowHom_mem_block D ω J W Coefficients.q pi ha)
        (windowHom_mem_block D ω J W Coefficients.q pi hb)
      exact hn.imp (fun h he ↦ h (Subtype.ext he)) (fun h he ↦ h (Subtype.ext he))
    · intro u a b
      change positiveModifiedForm D (e (u * a)) (e b) =
        positiveModifiedForm D (e a)
          (e (rhoModified (Dw D ω J W) Coefficients.q pi pi_sq u * b))
      simp only [e, modifiedHom_mul, positiveModifiedForm_adjoint, modifiedHom_rho]
    · intro μ a b
      change positiveModifiedForm D (e (positiveHalf (Dw D ω J W) Coefficients.q pi μ a))
        (e (positiveHalf (Dw D ω J W) Coefficients.q pi μ b)) = _
      rw [modifiedHom_positiveHalf, modifiedHom_positiveHalf,
        positiveModifiedForm_positiveHalf, serreForm_serreWindow]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- The window homomorphism preserves the sesquilinear form of Theorem 10.1. -/
theorem sesquilinearForm_modifiedHom (x y : modified (Dw D ω J W) Coefficients.q pi) :
    sesquilinearForm D (modifiedHom D ω J W Coefficients.q pi x)
      (modifiedHom D ω J W Coefficients.q pi y) = sesquilinearForm (Dw D ω J W) x y := by
  rw [sesquilinearForm_apply, ← modifiedHom_psi, positiveModifiedForm_modifiedHom,
    sesquilinearForm_apply]

/-! ### Every element comes from a window -/

omit [AddCommGroup X] [DecidableEq I] [DecidableEq X] in
/-- Every element of the free algebra involves finitely many generators. -/
theorem exists_finset_mem_adjoin (f : Free k I X) :
    ∃ s : Finset (Gen I X), f ∈ Algebra.adjoin k (FreeAlgebra.ι k '' (s : Set (Gen I X))) := by
  classical
  induction f using FreeAlgebra.induction with
  | grade0 c => exact ⟨∅, Subalgebra.algebraMap_mem _ c⟩
  | grade1 g => exact ⟨{g}, Algebra.subset_adjoin ⟨g, by simp, rfl⟩⟩
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    refine ⟨s ∪ t, add_mem ?_ ?_⟩
    · exact Algebra.adjoin_mono (Set.image_mono (by simp)) hs
    · exact Algebra.adjoin_mono (Set.image_mono (by simp)) ht
  | mul a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    refine ⟨s ∪ t, mul_mem ?_ ?_⟩
    · exact Algebra.adjoin_mono (Set.image_mono (by simp)) hs
    · exact Algebra.adjoin_mono (Set.image_mono (by simp)) ht

/-- The colour of a generator, if any. -/
def Gen.colours : Gen I X → Finset I
  | .one _ => ∅
  | .e i _ => {i}
  | .f i _ => {i}

/-- The weight of a generator. -/
def Gen.weight : Gen I X → X
  | .one μ => μ
  | .e _ μ => μ
  | .f _ μ => μ

/-- Every element of the free algebra comes from the free algebra of a window, for all seed
weight sets containing a fixed finite set. -/
theorem exists_freeInclude_eq (f : Free k I X) :
    ∃ (J : Finset I) (W₀ : Finset X), ∀ W, W₀ ⊆ W →
      f ∈ (freeInclude k D ω J W).range := by
  obtain ⟨s, hs⟩ := exists_finset_mem_adjoin f
  refine ⟨s.biUnion Gen.colours, s.image Gen.weight, fun W hW ↦ ?_⟩
  refine Algebra.adjoin_le ?_ hs
  rintro _ ⟨g, hg, rfl⟩
  have hμ : Gen.weight g ∈ Lat D ω (s.biUnion Gen.colours) W :=
    FiniteWeightWindow.weight_mem _ _ _ (hW (Finset.mem_image_of_mem _ hg))
  cases g with
  | one μ => exact ⟨Free.one k ⟨μ, hμ⟩, freeInclude_one D ω _ W _⟩
  | e i μ =>
    have hi : i ∈ s.biUnion Gen.colours := Finset.mem_biUnion.mpr ⟨_, hg, by simp [Gen.colours]⟩
    exact ⟨Free.E k ⟨i, hi⟩ ⟨μ, hμ⟩, freeInclude_E D ω _ W _ _⟩
  | f i μ =>
    have hi : i ∈ s.biUnion Gen.colours := Finset.mem_biUnion.mpr ⟨_, hg, by simp [Gen.colours]⟩
    exact ⟨Free.F k ⟨i, hi⟩ ⟨μ, hμ⟩, freeInclude_F D ω _ W _ _⟩

/-- Every element of BE2's modified algebra comes from the modified algebra of a window. -/
theorem exists_modifiedHom_eq (x : modified D q π) :
    ∃ (J : Finset I) (W : Finset X) (x' : modified (Dw D ω J W) q π),
      modifiedHom D ω J W q π x' = x := by
  classical
  obtain ⟨s, hs₁, hs₂⟩ := exists_localUnit D q π x.property
  obtain ⟨f, hf⟩ := mk_surjective D q π x.1
  obtain ⟨J, W₀, hJ⟩ := exists_freeInclude_eq D ω f
  let W := W₀ ∪ s
  obtain ⟨f', hf'⟩ := hJ W Finset.subset_union_left
  let lift : s → Lat D ω J W := fun η ↦
    ⟨η, FiniteWeightWindow.weight_mem _ _ _ (Finset.mem_union_right _ η.2)⟩
  let y := mk (Dw D ω J W) q π f'
  have hy : windowHom D ω J W q π y = x := by
    simp only [y, windowHom_mk]
    exact (congrArg (mk D q π) hf').trans hf
  let x' := ∑ a : s, ∑ b : s, blockProj (Dw D ω J W) q π (lift a) (lift b) y
  have hx' : x' ∈ modified (Dw D ω J W) q π :=
    Submodule.sum_mem _ fun a _ ↦ Submodule.sum_mem _ fun b _ ↦
      block_le_modified _ _ _ _ _ (blockProj_mem _ _ _ _ _ y)
  refine ⟨J, W, ⟨x', hx'⟩, Subtype.ext ?_⟩
  change windowHom D ω J W q π x' = x.1
  simp only [x', map_sum, blockProj_apply, map_mul, windowHom_one, hy]
  calc ∑ a : s, ∑ b : s, one D q π ((lift a : Lat D ω J W) : X) * x.1 *
        one D q π ((lift b : Lat D ω J W) : X)
      = (∑ a : s, one D q π (a : X)) * x.1 * (∑ b : s, one D q π (b : X)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum]
    _ = x.1 := by
        rw [Finset.sum_coe_sort s (fun η ↦ one D q π η), hs₁, hs₂]

/-! ### Descent of nondegeneracy -/

/-- If the form of Theorem 10.1 is nondegenerate on every finite weight window, it is
nondegenerate on BE2's modified algebra. -/
theorem sesquilinearForm_nondegenerate_of_windows
    (hW : ∀ (J : Finset I) (W : Finset X) (x : modified (Dw D ω J W) Coefficients.q pi),
      (∀ y, sesquilinearForm (Dw D ω J W) x y = 0) → x = 0)
    (x : modified D Coefficients.q pi) (hx : ∀ y, sesquilinearForm D x y = 0) : x = 0 := by
  obtain ⟨J, W, x', rfl⟩ := exists_modifiedHom_eq D ω Coefficients.q pi x
  rw [hW J W x' fun y ↦ by rw [← sesquilinearForm_modifiedHom]; exact hx _, map_zero]

/-- **The form of BE2 Theorem 10.1 is nondegenerate** for a torsion-free weight group with
linearly independent roots and integral weights `ω` separating the coroots
(`⟨hᵢ, ωⱼ⟩ = δᵢⱼ`, which makes the coroots independent). The colour set may be infinite and the
weight group need not be finitely generated. -/
theorem sesquilinearForm_nondegenerate_of_separating [Module.IsTorsionFree ℤ X]
    (hω : ∀ i j, D.h i (ω j) = if i = j then 1 else 0) (hα : LinearIndependent ℤ D.α)
    (x : modified D Coefficients.q pi) (hx : ∀ y, sesquilinearForm D x y = 0) : x = 0 := by
  classical
  refine sesquilinearForm_nondegenerate_of_windows D ω (fun J W x' hx' ↦ ?_) x hx
  exact FiniteWeightForm.sesquilinearForm_nondegenerate (Dw D ω J W)
    (D.weightWindow_root_linearIndependent J W _ (hα.comp _ Subtype.val_injective))
    (D.weightWindow_coroot_linearIndependent J W _ fun i j ↦ by
      rw [hω]; simp only [Subtype.ext_iff]) x' hx'

open SourceWeightLattice in
/-- **The form of BE2 Theorem 10.1 is nondegenerate on BE2's own weight lattice**
`P = {λ ∈ 𝔥* | ⟨hᵢ, λ⟩ ∈ ℤ}` of a complex realization (arXiv:1701.04133v2, §1), for linearly
independent roots and coroots, an arbitrary colour set and arbitrary complex `𝔥`. -/
theorem sourceWeightLattice_nondegenerate {I H : Type*} [AddCommGroup H] [Module ℂ H]
    [DecidableEq I] (h : I → H) [DecidableEq (weightLattice h)]
    (C : SuperCartanDatum I) (α : I → Module.Dual ℂ H)
    (ha : ∀ i j, α j (h i) = (C.a i j : ℂ))
    (hh : LinearIndependent ℂ h) (hα : LinearIndependent ℂ α)
    (x : modified (datum h C α ha) Coefficients.q pi)
    (hx : ∀ y, sesquilinearForm (datum h C α ha) x y = 0) : x = 0 :=
  sesquilinearForm_nondegenerate_of_separating (datum h C α ha) (SourceWeightLattice.omega h hh)
    (fun i j ↦ coroot_omega h hh i j) (root_linearIndependent h C α ha hα) x hx

end OddMath.CoveringQuantum.UDot.WindowForm
