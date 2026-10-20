/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.ContextualExchange

/-!
# Contextual mixed-word commutators

Algebraic steps for BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 5, correcting (10.7).
The form is antilinear in its first slot: the same-colour scalar is the
bar of the quantum integer at the left endpoint of the suffix. This differs
from the unbarred coefficient printed in the proof of Claim 5; the barred scalar
is forced by the mixed defining relation and first-slot antilinearity. The importing
examples distinguish these coefficients and refute the unbarred form identity.
The form allows arbitrary colours without bar consistency, over the purely-even
generic covering coefficient ring.
These identities do not assert the graphical matching comparisons.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram
open Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- The same-colour defining relation after the physical suffix. -/
private theorem algebraWord_comm_self_suffix (ζ : X) (i : I) (b : List (Bool × I)) :
    algebraWord D ζ ((true, i) :: (false, i) :: b) -
        pi ^ (D.parity i * D.parity i).val •
          algebraWord D ζ ((false, i) :: (true, i) :: b) =
      qpInt (D.qi Coefficients.q i) (D.pii pi i)
        (D.h i (ζ + shift D b)) • algebraWord D ζ b := by
  apply Subtype.ext
  change E D Coefficients.q pi i (ζ + (-D.α i + shift D b)) *
      (F D Coefficients.q pi i (ζ + shift D b) * (algebraWord D ζ b).val) -
    pi ^ (D.parity i * D.parity i).val •
      (F D Coefficients.q pi i (ζ + (D.α i + shift D b)) *
        (E D Coefficients.q pi i (ζ + shift D b) * (algebraWord D ζ b).val)) = _
  rw [show ζ + (-D.α i + shift D b) = ζ + shift D b - D.α i by abel,
    show ζ + (D.α i + shift D b) = ζ + shift D b + D.α i by abel,
    ← mul_assoc, ← mul_assoc, ← smul_mul_assoc, ← sub_mul, comm_rel, ite_eq_left rfl,
    smul_mul_assoc, (algebraWord_mem_block D ζ b).1]
  rfl

/-- Same-colour commutator in arbitrary physical prefix/suffix context. -/
theorem algebraWord_context_EF (ζ : X) (a b : List (Bool × I)) (i : I) :
    algebraWord D ζ (a ++ (true, i) :: (false, i) :: b) -
        D.pii pi i • algebraWord D ζ (a ++ (false, i) :: (true, i) :: b) =
      qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (ζ + shift D b)) •
        algebraWord D ζ (a ++ b) := by
  have h := algebraWord_comm_self_suffix D ζ i b
  have hp : D.parity i * D.parity i = D.parity i :=
    (by decide : ∀ p : ZMod 2, p * p = p) (D.parity i)
  rw [hp] at h
  rw [algebraWord_append, algebraWord_append, algebraWord_append]
  have hs₁ : shift D ((true, i) :: (false, i) :: b) = shift D b := by
    simp [shift, halfRoot]
  have hs₂ : shift D ((false, i) :: (true, i) :: b) = shift D b := by
    simp [shift, halfRoot]
  rw [hs₁, hs₂]
  apply Subtype.ext
  have hc := congrArg Subtype.val h
  change (algebraWord D ζ ((true, i) :: (false, i) :: b)).val -
    D.pii pi i • (algebraWord D ζ ((false, i) :: (true, i) :: b)).val =
    qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (ζ + shift D b)) •
      (algebraWord D ζ b).val at hc
  change _ * _ - _ • (_ * _) = _ • (_ * _)
  rw [← mul_smul_comm, ← mul_sub, hc, mul_smul_comm]

end OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram

namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients GenericVerma.MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- Algebraic adjacent commutator for Claim 5. The quantum integer must be
conjugated because the contextual word is in the first slot. The suffix weight
is its physical endpoint, not the endpoint of the prefix or of the whole word. -/
theorem sesquilinearForm_context_EF (ζ : X) (a b : List (Bool × I)) (i : I) :
    sesquilinearForm D (algebraWord D ζ (a ++ (true, i) :: (false, i) :: b))
        (algebraWord D ζ []) -
      D.pii pi i *
        sesquilinearForm D (algebraWord D ζ (a ++ (false, i) :: (true, i) :: b))
          (algebraWord D ζ []) =
      bar (qpInt (D.qi Coefficients.q i) (D.pii pi i)
        (D.h i (OddMath.SKM.wt D.toSKM ζ b))) *
        sesquilinearForm D (algebraWord D ζ (a ++ b)) (algebraWord D ζ []) := by
  have h := algebraWord_context_EF D ζ a b i
  have he : algebraWord D ζ (a ++ (true, i) :: (false, i) :: b) =
      qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (ζ + shift D b)) •
        algebraWord D ζ (a ++ b) +
      D.pii pi i • algebraWord D ζ (a ++ (false, i) :: (true, i) :: b) := by
    apply Subtype.ext
    exact sub_eq_iff_eq_add.mp (congrArg Subtype.val h)
  apply sub_eq_iff_eq_add.mpr
  have hf := congrArg (fun x => sesquilinearForm D x (algebraWord D ζ [])) he
  simpa only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, barData.map_pii, mixed_word_physical_weight] using hf

end OddMath.CoveringQuantum.UDot.GenericTensor
