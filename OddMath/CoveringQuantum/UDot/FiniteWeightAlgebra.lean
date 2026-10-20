/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.FiniteWeightDuality
import OddMath.CoveringQuantum.UDot.Blocks

/-!
# Evaluation transport of the modified covering algebra

The finite-free-lattice step toward Brundan–Ellis, arXiv:1701.04133v2,
Theorem 12.1: the presentation in §9 is unchanged by evaluation into the
additive dual of the full integral dual. Unlike simple-coroot coordinates,
this identification retains central weights (Clark, arXiv:1312.4855v2, §2.1).
The coefficient ring here may be any commutative ring, whereas BE2 uses its
covering rational-function ring. No bar-consistency or root independence is
needed for this change of weight labels. This is not form compatibility or
nondegeneracy, and does not remove either hypothesis of conditional Theorem 12.1.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot.FiniteWeightAlgebra

open FiniteWeightDuality

variable {k I L : Type*} [CommRing k] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]

/-- Relabel the free generators by integral evaluation. -/
def freeForward : Free k I L →ₐ[k] Free k I (coweight L →+ ℤ) :=
  FreeAlgebra.lift k fun g ↦ match g with
    | .one μ => Free.one k ((weightEquiv L) μ)
    | .e i μ => Free.E k i ((weightEquiv L) μ)
    | .f i μ => Free.F k i ((weightEquiv L) μ)

@[simp] theorem freeForward_one (μ : L) :
    freeForward (Free.one k μ : Free k I L) = Free.one k ((weightEquiv L) μ) := by
  simp [freeForward, Free.one]

@[simp] theorem freeForward_E (i : I) (μ : L) :
    freeForward (Free.E k i μ : Free k I L) = Free.E k i ((weightEquiv L) μ) := by
  simp [freeForward, Free.E]

@[simp] theorem freeForward_F (i : I) (μ : L) :
    freeForward (Free.F k i μ : Free k I L) = Free.F k i ((weightEquiv L) μ) := by
  simp [freeForward, Free.F]

/-- Relabel the free generators by integral inverse evaluation. -/
def freeBackward : Free k I (coweight L →+ ℤ) →ₐ[k] Free k I L :=
  FreeAlgebra.lift k fun g ↦ match g with
    | .one μ => Free.one k ((weightEquiv L).symm μ)
    | .e i μ => Free.E k i ((weightEquiv L).symm μ)
    | .f i μ => Free.F k i ((weightEquiv L).symm μ)

@[simp] theorem freeBackward_one (μ : (coweight L →+ ℤ)) :
    freeBackward (Free.one k μ : Free k I (coweight L →+ ℤ)) =
      Free.one k ((weightEquiv L).symm μ) := by
  simp [freeBackward, Free.one]

@[simp] theorem freeBackward_E (i : I) (μ : (coweight L →+ ℤ)) :
    freeBackward (Free.E k i μ : Free k I (coweight L →+ ℤ)) =
      Free.E k i ((weightEquiv L).symm μ) := by
  simp [freeBackward, Free.E]

@[simp] theorem freeBackward_F (i : I) (μ : (coweight L →+ ℤ)) :
    freeBackward (Free.F k i μ : Free k I (coweight L →+ ℤ)) =
      Free.F k i ((weightEquiv L).symm μ) := by
  simp [freeBackward, Free.F]

variable [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)]
variable (D : RootDatum I L) (q : kˣ) (π : k)

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
@[simp] theorem freeForward_epow (i : I) (n : ℕ) (μ : L) :
    freeForward (epow (k := k) D i n μ) = epow (dualDatum D) i n ((weightEquiv L) μ) := by
  induction n with
  | zero => simp [epow]
  | succ n ih =>
    simp only [epow, map_mul, freeForward_E, map_add, map_nsmul, weightEquiv_root, ih]

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
@[simp] theorem freeForward_fpow (i : I) (n : ℕ) (μ : L) :
    freeForward (fpow (k := k) D i n μ) = fpow (dualDatum D) i n ((weightEquiv L) μ) := by
  induction n with
  | zero => simp [fpow]
  | succ n ih =>
    simp only [fpow, map_mul, freeForward_F, map_sub, map_nsmul, weightEquiv_root, ih]

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
theorem freeForward_serreE (i j : I) (μ : L) :
    freeForward (serreE D q π i j μ) = serreE (dualDatum D) q π i j ((weightEquiv L) μ) := by
  simp [serreE, map_sum, weightEquiv_root]

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
theorem freeForward_serreF (i j : I) (μ : L) :
    freeForward (serreF D q π i j μ) = serreF (dualDatum D) q π i j ((weightEquiv L) μ) := by
  simp [serreF, map_sum, weightEquiv_root]

/-- Every defining relation is preserved, including both Serre sums. -/
theorem rel_freeForward {x y : Free k I L} (h : Rel D q π x y) :
    Rel (dualDatum D) q π (freeForward x) (freeForward y) := by
  cases h with
  | one_one μ ν =>
    simpa only [map_mul, freeForward_one, apply_ite, map_zero,
      (weightEquiv L).injective.eq_iff] using
      (Rel.one_one (D := (dualDatum D)) (q := q) (π := π) ((weightEquiv L) μ) ((weightEquiv L) ν))
  | one_E i μ =>
    simpa only [map_mul, freeForward_one, freeForward_E, freeForward_F,
      map_add, map_sub, weightEquiv_root] using
      (Rel.one_E (D := (dualDatum D)) (q := q) (π := π) i ((weightEquiv L) μ))
  | E_one i μ =>
    simpa only [map_mul, freeForward_one, freeForward_E, freeForward_F,
      map_add, map_sub, weightEquiv_root] using
      (Rel.E_one (D := (dualDatum D)) (q := q) (π := π) i ((weightEquiv L) μ))
  | one_F i μ =>
    simpa only [map_mul, freeForward_one, freeForward_E, freeForward_F,
      map_add, map_sub, weightEquiv_root] using
      (Rel.one_F (D := (dualDatum D)) (q := q) (π := π) i ((weightEquiv L) μ))
  | F_one i μ =>
    simpa only [map_mul, freeForward_one, freeForward_E, freeForward_F,
      map_add, map_sub, weightEquiv_root] using
      (Rel.F_one (D := (dualDatum D)) (q := q) (π := π) i ((weightEquiv L) μ))
  | comm i j μ =>
    simpa only [map_sub, map_mul, map_smul, apply_ite, map_zero,
      freeForward_one, freeForward_E, freeForward_F, map_add,
      weightEquiv_root, coroot_weightEquiv] using
      (Rel.comm (D := (dualDatum D)) (q := q) (π := π) i j ((weightEquiv L) μ))
  | serreE i j μ h =>
    rw [freeForward_serreE, map_zero]
    exact Rel.serreE i j ((weightEquiv L) μ) h
  | serreF i j μ h =>
    rw [freeForward_serreF, map_zero]
    exact Rel.serreF i j ((weightEquiv L) μ) h

/-- The induced forward homomorphism of unital envelopes. -/
def forward : CoveringUDot k D q π →ₐ[k] CoveringUDot k (dualDatum D) q π :=
  RingQuot.liftAlgHom k ⟨(mk (dualDatum D) q π).comp freeForward, fun _ _ h ↦
    mk_rel (dualDatum D) q π (rel_freeForward D q π h)⟩

@[simp] theorem forward_mk (x : Free k I L) :
    forward D q π (mk D q π x) = mk (dualDatum D) q π (freeForward x) := by
  simp only [forward, mk, RingQuot.liftAlgHom_mkAlgHom_apply, AlgHom.comp_apply]

@[simp] theorem forward_one (μ : L) :
    forward D q π (one D q π μ) = one (dualDatum D) q π ((weightEquiv L) μ) := by
  rw [one, forward_mk, freeForward_one]
  rfl

@[simp] theorem forward_E (i : I) (μ : L) :
    forward D q π (E D q π i μ) = E (dualDatum D) q π i ((weightEquiv L) μ) := by
  rw [E, forward_mk, freeForward_E]
  rfl

@[simp] theorem forward_F (i : I) (μ : L) :
    forward D q π (F D q π i μ) = F (dualDatum D) q π i ((weightEquiv L) μ) := by
  rw [F, forward_mk, freeForward_F]
  rfl

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
@[simp] theorem freeBackward_epow (i : I) (n : ℕ) (μ : (coweight L →+ ℤ)) :
    freeBackward (epow (k := k) (dualDatum D) i n μ) = epow D i n ((weightEquiv L).symm μ) := by
  induction n with
  | zero => simp [epow]
  | succ n ih =>
    simp only [epow, map_mul, freeBackward_E, map_add, map_nsmul, weightEquiv_symm_root, ih]

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
@[simp] theorem freeBackward_fpow (i : I) (n : ℕ) (μ : (coweight L →+ ℤ)) :
    freeBackward (fpow (k := k) (dualDatum D) i n μ) = fpow D i n ((weightEquiv L).symm μ) := by
  induction n with
  | zero => simp [fpow]
  | succ n ih =>
    simp only [fpow, map_mul, freeBackward_F, map_sub, map_nsmul, weightEquiv_symm_root, ih]

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
theorem freeBackward_serreE (i j : I) (μ : (coweight L →+ ℤ)) :
    freeBackward (serreE (dualDatum D) q π i j μ) = serreE D q π i j ((weightEquiv L).symm μ) := by
  simp only [serreE, map_sum, map_smul, map_mul, freeBackward_epow,
    freeBackward_E, map_add, map_nsmul, weightEquiv_symm_root]

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
theorem freeBackward_serreF (i j : I) (μ : (coweight L →+ ℤ)) :
    freeBackward (serreF (dualDatum D) q π i j μ) = serreF D q π i j ((weightEquiv L).symm μ) := by
  simp only [serreF, map_sum, map_smul, map_mul, freeBackward_fpow,
    freeBackward_F, map_sub, map_nsmul, weightEquiv_symm_root]

/-- Every defining relation is preserved, including both Serre sums. -/
theorem rel_freeBackward {x y : Free k I (coweight L →+ ℤ)} (h : Rel (dualDatum D) q π x y) :
    Rel D q π (freeBackward x) (freeBackward y) := by
  cases h with
  | one_one μ ν =>
    simpa only [map_mul, freeBackward_one, apply_ite, map_zero,
      (weightEquiv L).symm.injective.eq_iff] using
      (Rel.one_one (D := D) (q := q) (π := π) ((weightEquiv L).symm μ) ((weightEquiv L).symm ν))
  | one_E i μ =>
    simpa only [map_mul, freeBackward_one, freeBackward_E, freeBackward_F,
      map_add, map_sub, weightEquiv_symm_root] using
      (Rel.one_E (D := D) (q := q) (π := π) i ((weightEquiv L).symm μ))
  | E_one i μ =>
    simpa only [map_mul, freeBackward_one, freeBackward_E, freeBackward_F,
      map_add, map_sub, weightEquiv_symm_root] using
      (Rel.E_one (D := D) (q := q) (π := π) i ((weightEquiv L).symm μ))
  | one_F i μ =>
    simpa only [map_mul, freeBackward_one, freeBackward_E, freeBackward_F,
      map_add, map_sub, weightEquiv_symm_root] using
      (Rel.one_F (D := D) (q := q) (π := π) i ((weightEquiv L).symm μ))
  | F_one i μ =>
    simpa only [map_mul, freeBackward_one, freeBackward_E, freeBackward_F,
      map_add, map_sub, weightEquiv_symm_root] using
      (Rel.F_one (D := D) (q := q) (π := π) i ((weightEquiv L).symm μ))
  | comm i j μ =>
    simpa only [map_sub, map_mul, map_smul, apply_ite, map_zero,
      freeBackward_one, freeBackward_E, freeBackward_F, map_add,
      weightEquiv_symm_root, coroot_weightEquiv_symm] using
      (Rel.comm (D := D) (q := q) (π := π) i j ((weightEquiv L).symm μ))
  | serreE i j μ h =>
    rw [freeBackward_serreE, map_zero]
    exact Rel.serreE i j ((weightEquiv L).symm μ) h
  | serreF i j μ h =>
    rw [freeBackward_serreF, map_zero]
    exact Rel.serreF i j ((weightEquiv L).symm μ) h

/-- The induced inverse homomorphism of unital envelopes. -/
def backward : CoveringUDot k (dualDatum D) q π →ₐ[k] CoveringUDot k D q π :=
  RingQuot.liftAlgHom k ⟨(mk D q π).comp freeBackward, fun _ _ h ↦
    mk_rel D q π (rel_freeBackward D q π h)⟩

@[simp] theorem backward_mk (x : Free k I (coweight L →+ ℤ)) :
    backward D q π (mk (dualDatum D) q π x) = mk D q π (freeBackward x) := by
  simp only [backward, mk, RingQuot.liftAlgHom_mkAlgHom_apply, AlgHom.comp_apply]

@[simp] theorem backward_one (μ : (coweight L →+ ℤ)) :
    backward D q π (one (dualDatum D) q π μ) = one D q π ((weightEquiv L).symm μ) := by
  rw [one, backward_mk, freeBackward_one]
  rfl

@[simp] theorem backward_E (i : I) (μ : (coweight L →+ ℤ)) :
    backward D q π (E (dualDatum D) q π i μ) = E D q π i ((weightEquiv L).symm μ) := by
  rw [E, backward_mk, freeBackward_E]
  rfl

@[simp] theorem backward_F (i : I) (μ : (coweight L →+ ℤ)) :
    backward D q π (F (dualDatum D) q π i μ) = F D q π i ((weightEquiv L).symm μ) := by
  rw [F, backward_mk, freeBackward_F]
  rfl

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
@[simp] theorem freeBackward_freeForward (x : Free k I L) :
    freeBackward (freeForward x) = x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes]
  | grade1 g =>
    cases g with
    | one μ =>
      change freeBackward (freeForward (Free.one k μ)) = Free.one k μ
      simp
    | e i μ =>
      change freeBackward (freeForward (Free.E k i μ)) = Free.E k i μ
      simp
    | f i μ =>
      change freeBackward (freeForward (Free.F k i μ)) = Free.F k i μ
      simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
@[simp] theorem freeForward_freeBackward (x : Free k I (coweight L →+ ℤ)) :
    freeForward (freeBackward x) = x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes]
  | grade1 g =>
    cases g with
    | one μ =>
      change freeForward (freeBackward (Free.one k μ)) = Free.one k μ
      simp
    | e i μ =>
      change freeForward (freeBackward (Free.E k i μ)) = Free.E k i μ
      simp
    | f i μ =>
      change freeForward (freeBackward (Free.F k i μ)) = Free.F k i μ
      simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

@[simp] theorem backward_forward (x : CoveringUDot k D q π) :
    backward D q π (forward D q π x) = x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  simp only [forward_mk, backward_mk, freeBackward_freeForward]

@[simp] theorem forward_backward (x : CoveringUDot k (dualDatum D) q π) :
    forward D q π (backward D q π x) = x := by
  obtain ⟨y, rfl⟩ := mk_surjective (dualDatum D) q π x
  simp only [backward_mk, forward_mk, freeForward_freeBackward]

/-- Evaluation gives an equivalence of the unital envelopes. -/
def envelopeEquiv : CoveringUDot k D q π ≃ₐ[k] CoveringUDot k (dualDatum D) q π :=
  AlgEquiv.ofAlgHom (forward D q π) (backward D q π)
    (AlgHom.ext (forward_backward D q π))
    (AlgHom.ext (backward_forward D q π))

/-- Evaluation transports both endpoints of every existing weight block. -/
theorem forward_mem_block {μ η : L} {x : CoveringUDot k D q π}
    (hx : x ∈ block D q π μ η) :
    forward D q π x ∈ block (dualDatum D) q π ((weightEquiv L) μ) ((weightEquiv L) η) := by
  constructor
  · rw [← forward_one, ← map_mul, hx.1]
  · rw [← forward_one, ← map_mul, hx.2]

/-- The actual finite block sum is preserved, not merely its unital envelope. -/
theorem forward_mem_modified {x : CoveringUDot k D q π}
    (hx : x ∈ modified D q π) : forward D q π x ∈ modified (dualDatum D) q π := by
  refine Submodule.iSup_induction (fun b : L × L ↦ block D q π b.1 b.2)
    (motive := fun x ↦ forward D q π x ∈ modified (dualDatum D) q π) hx ?_ ?_ ?_
  · intro b x hx
    exact block_le_modified (dualDatum D) q π _ _ (forward_mem_block D q π hx)
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

/-- Evaluation transports both endpoints of every existing weight block. -/
theorem backward_mem_block {μ η : (coweight L →+ ℤ)} {x : CoveringUDot k (dualDatum D) q π}
    (hx : x ∈ block (dualDatum D) q π μ η) :
    backward D q π x ∈ block D q π ((weightEquiv L).symm μ) ((weightEquiv L).symm η) := by
  constructor
  · rw [← backward_one, ← map_mul, hx.1]
  · rw [← backward_one, ← map_mul, hx.2]

/-- The actual finite block sum is preserved, not merely its unital envelope. -/
theorem backward_mem_modified {x : CoveringUDot k (dualDatum D) q π}
    (hx : x ∈ modified (dualDatum D) q π) : backward D q π x ∈ modified D q π := by
  refine Submodule.iSup_induction
    (fun b : (coweight L →+ ℤ) × (coweight L →+ ℤ) ↦ block (dualDatum D) q π b.1 b.2)
    (motive := fun x ↦ backward D q π x ∈ modified D q π) hx ?_ ?_ ?_
  · intro b x hx
    exact block_le_modified D q π _ _ (backward_mem_block D q π hx)
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

/-- Evaluation equivalence on BE2's nonunital modified algebra.
Its multiplication compatibility is `modifiedEquiv_mul`. -/
def modifiedEquiv : modified D q π ≃ₗ[k] modified (dualDatum D) q π where
  toFun x := ⟨forward D q π x, forward_mem_modified D q π x.property⟩
  invFun x := ⟨backward D q π x, backward_mem_modified D q π x.property⟩
  left_inv x := Subtype.ext (backward_forward D q π x)
  right_inv x := Subtype.ext (forward_backward D q π x)
  map_add' x y := Subtype.ext (map_add (forward D q π) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (forward D q π) c x.1)

@[simp] theorem coe_modifiedEquiv (x : modified D q π) :
    (modifiedEquiv D q π x : CoveringUDot k (dualDatum D) q π) = forward D q π x := rfl

@[simp] theorem coe_modifiedEquiv_symm (x : modified (dualDatum D) q π) :
    ((modifiedEquiv D q π).symm x : CoveringUDot k D q π) = backward D q π x := rfl

/-- The linear equivalence preserves the existing nonunital multiplication. -/
theorem modifiedEquiv_mul (x y : modified D q π) :
    modifiedEquiv D q π (x * y) = modifiedEquiv D q π x * modifiedEquiv D q π y :=
  Subtype.ext (map_mul (forward D q π) x.1 y.1)

end OddMath.CoveringQuantum.UDot.FiniteWeightAlgebra
