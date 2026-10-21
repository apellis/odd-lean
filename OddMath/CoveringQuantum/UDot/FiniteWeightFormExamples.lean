/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.FiniteWeightForm
import OddMath.CoveringQuantum.UDot.FiniteWeightAlgebraExamples

/-! # Generic-coefficient consumers on finite source windows and an odd rank-one lattice -/

noncomputable section

namespace OddMath.CoveringQuantum.FiniteWeightFormConsumer

open UDot GenericTensor FiniteWeightDuality UDot.FiniteWeightAlgebra
open SourceWeightLatticeConsumer

local instance : DecidableEq lattice := Classical.decEq _
local instance : DecidableEq (coweight lattice →+ ℤ) := Classical.decEq _

/-- The infinite-colour complex fixture's finite window, at generic q and pi. -/
theorem window_form (x y : modified restrictedDatum Coefficients.q Coefficients.pi) :
    sesquilinearForm (dualDatum restrictedDatum)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi x)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi y) =
        sesquilinearForm restrictedDatum x y :=
  FiniteWeightForm.sesquilinearForm_modifiedEquiv restrictedDatum x y

/-- The central and infinite-support seed weight idempotents use the original form. -/
theorem central_seed_one :
    let x : modified restrictedDatum Coefficients.q Coefficients.pi :=
      ⟨one restrictedDatum Coefficients.q Coefficients.pi centralInWindow,
        one_mem_modified restrictedDatum Coefficients.q Coefficients.pi centralInWindow⟩
    let y : modified restrictedDatum Coefficients.q Coefficients.pi :=
      ⟨one restrictedDatum Coefficients.q Coefficients.pi seedInWindow,
        one_mem_modified restrictedDatum Coefficients.q Coefficients.pi seedInWindow⟩
    sesquilinearForm (dualDatum restrictedDatum)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi x)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi y) =
        sesquilinearForm restrictedDatum x y := window_form _ _

/-- E at the central weight and F at the retained seed, without nonzero assertions. -/
theorem central_seed_EF (i j : colours) :
    let x : modified restrictedDatum Coefficients.q Coefficients.pi :=
      ⟨E restrictedDatum Coefficients.q Coefficients.pi i centralInWindow,
        E_mem_modified restrictedDatum Coefficients.q Coefficients.pi i centralInWindow⟩
    let y : modified restrictedDatum Coefficients.q Coefficients.pi :=
      ⟨F restrictedDatum Coefficients.q Coefficients.pi j seedInWindow,
        F_mem_modified restrictedDatum Coefficients.q Coefficients.pi j seedInWindow⟩
    sesquilinearForm (dualDatum restrictedDatum)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi x)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi y) =
        sesquilinearForm restrictedDatum x y := window_form _ _

/-- F at the central weight and E at the seed test the other two generators. -/
theorem central_seed_FE (i j : colours) :
    let x : modified restrictedDatum Coefficients.q Coefficients.pi :=
      ⟨F restrictedDatum Coefficients.q Coefficients.pi i centralInWindow,
        F_mem_modified restrictedDatum Coefficients.q Coefficients.pi i centralInWindow⟩
    let y : modified restrictedDatum Coefficients.q Coefficients.pi :=
      ⟨E restrictedDatum Coefficients.q Coefficients.pi j seedInWindow,
        E_mem_modified restrictedDatum Coefficients.q Coefficients.pi j seedInWindow⟩
    sesquilinearForm (dualDatum restrictedDatum)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi x)
      (modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi y) =
        sesquilinearForm restrictedDatum x y := window_form _ _

/-- A separate bar-consistent odd fixture, with weights ℤ, root 2 and coroot identity. -/
def oddDatum : RootDatum Unit ℤ where
  a := Matrix.of fun _ _ ↦ 2
  isGCM :=
    { diag := fun _ ↦ rfl
      offDiag_nonpos := fun i j h ↦ absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ ↦ Iff.rfl }
  d := fun _ ↦ 1
  d_pos := fun _ ↦ one_pos
  d_mul_symm := fun _ _ ↦ rfl
  parity := fun _ ↦ 1
  even_of_odd := fun _ _ _ ↦ even_two
  cd :=
    { root := fun _ ↦ 2
      coroot := fun _ ↦ LinearMap.id
      coroot_root_self := fun _ ↦ rfl }
  coroot_root := fun _ _ ↦ rfl

theorem odd_barConsistent : oddDatum.toSuperCartanDatum.BarConsistent := fun _ ↦ rfl

theorem odd_root_independent : LinearIndependent ℤ oddDatum.α := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h : g () * 2 = 0 := by simpa [oddDatum] using hg
  have hz : g () = 0 := (mul_eq_zero.mp h).resolve_right (by decide)
  simpa only [Subsingleton.elim i ()] using hz

theorem odd_coroot_independent : LinearIndependent ℤ oddDatum.cd.coroot := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun f : Module.Dual ℤ ℤ ↦ f 1) hg
  simpa [oddDatum] using h

open scoped Classical in
/-- Every radical premise is discharged except the tested vector's radical membership. -/
theorem odd_leftRadical (x : modified oddDatum Coefficients.q Coefficients.pi)
    (hx : ∀ y, sesquilinearForm oddDatum x y = 0) : x = 0 :=
  FiniteWeightForm.sesquilinearForm_nondegenerate oddDatum odd_barConsistent
    odd_root_independent odd_coroot_independent x hx

end OddMath.CoveringQuantum.FiniteWeightFormConsumer
