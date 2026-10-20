/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.SourceWeightLattice
import OddMath.CoveringQuantum.UDot.LusztigComparison

/-!
# Full integral dual realization of a finite weight window

The finite-lattice realization prerequisite for the finite-support route to
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 12.1.
Evaluation identifies a finite free weight lattice with the additive dual of its
full integral dual, retaining central directions. The LieLean datum uses the
original coroots and evaluated roots; its Cartan matrix is not transposed.

`source_root_independent` and `source_coroot_independent` discharge the realization
premises in the representation used by `UDot.sesquilinearForm_nondegenerate`.
They impose no finiteness on the ambient complex realization. This implements
only the finite-perfect-lattice step (cf. Clark, *Quantum supergroups IV*,
arXiv:1312.4855v2, §2.1), not algebra/form transport or nondegeneracy on the
original weight lattice. The conditional categorical theorem still requires
Nondegeneracy and BarConsistent.
-/

noncomputable section

namespace OddMath.CoveringQuantum.FiniteWeightDuality

section Lattice

variable {J L : Type*} [AddCommGroup L]

/-- The entire integral dual, including functionals on central directions. -/
abbrev coweight (L : Type*) [AddCommGroup L] := Module.Dual ℤ L

variable (L) [Module.Free ℤ L] [Module.Finite ℤ L]

/-- Integral biduality, with the target expressed as additive homomorphisms. -/
def weightEquiv : L ≃ₗ[ℤ] (coweight L →+ ℤ) :=
  (Module.evalEquiv ℤ L).trans (addMonoidHomLequivInt ℤ).symm

/-- The same evaluation identification as an additive equivalence. -/
def weightAddEquiv : L ≃+ (coweight L →+ ℤ) := (weightEquiv L).toAddEquiv

@[simp] theorem weightEquiv_apply (x : L) (y : coweight L) :
    weightEquiv L x y = y x := rfl

@[simp] theorem weightEquiv_symm_apply_apply (x : L) :
    (weightEquiv L).symm (weightEquiv L x) = x :=
  (weightEquiv L).symm_apply_apply x

@[simp] theorem weightEquiv_apply_symm_apply (μ : coweight L →+ ℤ) :
    weightEquiv L ((weightEquiv L).symm μ) = μ :=
  (weightEquiv L).apply_symm_apply μ

/-- The inverse recovers all evaluations, not just simple-coroot coordinates. -/
theorem weightEquiv_symm_eval (μ : coweight L →+ ℤ) (y : coweight L) :
    y ((weightEquiv L).symm μ) = μ y :=
  congrArg (fun f : coweight L →+ ℤ ↦ f y) (weightEquiv_apply_symm_apply L μ)

theorem coweight_finite : Module.Finite ℤ (coweight L) := inferInstance

theorem coweight_free : Module.Free ℤ (coweight L) := inferInstance

variable {L} (D : RootDatum J L)

/-- The LieLean realization on the full dual of the given finite free lattice. -/
def realization : D.toSuperCartanDatum.lusztigDatum.RootDatum (coweight L) where
  coroot := D.cd.coroot
  root j := weightEquiv L (D.α j)
  root_coroot i j := by
    change D.h i (D.α j) = _
    rw [D.h_α, SuperCartanDatum.lusztigDatum_cartanMatrix]

/-- The datum on additive-dual weights used by Lusztig comparison. -/
abbrev dualDatum : RootDatum J (coweight L →+ ℤ) :=
  D.toSuperCartanDatum.rootDatumOf (realization D)

@[simp] theorem realization_coroot (i : J) :
    (realization D).coroot i = D.cd.coroot i := rfl

@[simp] theorem weightEquiv_root (j : J) :
    weightEquiv L (D.α j) = (dualDatum D).α j := rfl

@[simp] theorem weightEquiv_symm_root (j : J) :
    (weightEquiv L).symm ((dualDatum D).α j) = D.α j :=
  (weightEquiv L).symm_apply_apply _

@[simp] theorem coroot_weightEquiv (i : J) (x : L) :
    (dualDatum D).h i (weightEquiv L x) = D.h i x := rfl

@[simp] theorem coroot_weightEquiv_symm (i : J) (μ : coweight L →+ ℤ) :
    D.h i ((weightEquiv L).symm μ) = (dualDatum D).h i μ :=
  weightEquiv_symm_eval L μ (D.cd.coroot i)

@[simp] theorem dualDatum_cartan (i j : J) : (dualDatum D).a i j = D.a i j := rfl

@[simp] theorem dualDatum_symmetrizer (i : J) : (dualDatum D).d i = D.d i := rfl

@[simp] theorem dualDatum_parity (i : J) : (dualDatum D).parity i = D.parity i := rfl

@[simp] theorem dualDatum_barConsistent :
    (dualDatum D).toSuperCartanDatum.BarConsistent ↔ D.toSuperCartanDatum.BarConsistent :=
  Iff.rfl

/-- Independence in precisely the additive-dual representation of `rootDatumOf`. -/
theorem root_independent (hα : LinearIndependent ℤ D.α) :
    LinearIndependent ℤ (D.toSuperCartanDatum.rootDatumOf (realization D)).α :=
  hα.map' (weightEquiv L).toLinearMap (LinearMap.ker_eq_bot.mpr (weightEquiv L).injective)

/-- The LieLean coroots are literally the original integral linear forms. -/
theorem coroot_independent (hh : LinearIndependent ℤ D.cd.coroot) :
    LinearIndependent ℤ (realization D).coroot := hh

end Lattice

section Window

variable {J X : Type*} [AddCommGroup X] [Finite J] [Module.IsTorsionFree ℤ X]
    (W : Finset X) (α ω : J → X)

/-- Compatibility with the finite-window perfect pairing already constructed. -/
theorem weightEquiv_eq_perfect :
    weightEquiv (FiniteWeightWindow.lattice W α ω) =
      (FiniteWeightWindow.perfect W α ω).trans (addMonoidHomLequivInt ℤ).symm := rfl

end Window

section Source

variable {I H : Type*} [AddCommGroup H] [Module ℂ H]
    (h : I → H) (C : SuperCartanDatum I) (α : I → Module.Dual ℂ H)
    (ha : ∀ i j, α j (h i) = (C.a i j : ℂ))
    (hh : LinearIndependent ℂ h) (J : Finset I)
    (W : Finset (SourceWeightLattice.weightLattice h))

/-- Realization of the source window, without finite ambient colours or dimension. -/
abbrev sourceRealization :=
  realization (SourceWeightLattice.windowDatum h C α ha hh J W)

/-- Source complex independence implies additive-dual root independence. -/
theorem source_root_independent (hα : LinearIndependent ℂ α) :
    LinearIndependent ℤ
      ((SourceWeightLattice.windowDatum h C α ha hh J W).toSuperCartanDatum.rootDatumOf
        (sourceRealization h C α ha hh J W)).α :=
  root_independent _ (SourceWeightLattice.window_root_linearIndependent h C α ha hh J W hα)

/-- Source complex coroot independence supplies the LieLean coroot premise. -/
theorem source_coroot_independent :
    LinearIndependent ℤ (sourceRealization h C α ha hh J W).coroot :=
  coroot_independent _ (SourceWeightLattice.window_coroot_linearIndependent h C α ha hh J W)

end Source

end OddMath.CoveringQuantum.FiniteWeightDuality
