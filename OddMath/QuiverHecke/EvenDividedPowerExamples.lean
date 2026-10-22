/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EvenDividedPower

/-!
# Even principal-projective consumers

BE2, arXiv:1701.04133v2, Lemma 11.1 for an even colour, over `ZMod 2`: the even rank-one
datum needs no inverse of two.
-/

noncomputable section
namespace OddMath.QuiverHecke.EvenDividedPowerExamples
open DividedPowerModules

/-- The even rank-one datum on integral weights. -/
def datum : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 0
  even_of_odd := fun _ _ _ => even_two

/-- Parameters in characteristic two. -/
def scalars : SKM.Scalars datum (ZMod 2) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by
    rintro ⟨i, hi⟩
    exact (zero_ne_one hi).elim

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h

/-- Unit symmetrizer. -/
def symmetrizer : SKM.Symmetrizer datum where
  d := fun _ => 1
  pos := fun _ => one_pos
  symm := fun _ _ => rfl

/-- Every rank, including zero and one. -/
def decomposition (r : ℕ) :
    wordProjective datum scalars () r ≃ₗ[ModuleRing datum scalars r]
      (evenIndex r → evenProjective datum scalars () rfl r) :=
  evenDecompositionInHn datum scalars () rfl r

example (r : ℕ) : Module.Projective (ModuleRing datum scalars r)
    (evenProjective datum scalars () rfl r) := inferInstance

example (r : ℕ) : Fintype.card (evenIndex r) = r.factorial := card_evenIndex r

example (r : ℕ) (x : wordProjective datum scalars () r) :
    (decomposition r).symm (decomposition r x) = x :=
  (decomposition r).symm_apply_apply x

/-- The summand `j` is shifted by `evenShift j` in integer degree; parity is preserved. -/
example (r : ℕ) {d : ℤ × ZMod 2} (x : wordProjective datum scalars () r)
    (hx : PrincipalDegree datum scalars symmetrizer homogeneous d x) (j : evenIndex r) :
    PrincipalDegree datum scalars symmetrizer homogeneous (d + (evenShift r j, 0))
      (decomposition r x j) := by
  simpa [symmetrizer, decomposition] using
    evenDecompositionInHn_degree datum scalars symmetrizer homogeneous () rfl x hx j

#print axioms decomposition

end OddMath.QuiverHecke.EvenDividedPowerExamples
