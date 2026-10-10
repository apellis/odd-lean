import OddMath.CoveringQuantum.Twistor.Serre
import OddMath.CoveringQuantum.SerreIdeal
import OddMath.CoveringQuantum.Ordinary

/-!
# Nondegeneracy at the negative sign after adjoining a square root of minus one

The ordered free twist transports the full ordinary Serre ideal into the
negative-sign Serre ideal. Together with the free-form comparison and the
ordinary quantum Gabber–Kac theorem, this proves nondegeneracy at `π = -1`
over a characteristic-zero field containing a square root of `-1`.
Descent to the rational-function field and then to the generic covering
coefficient ring are not asserted here.
-/

noncomputable section

namespace OddMath.CoveringQuantum

namespace SuperCartanDatum

variable {I k : Type*} [LinearOrder I] [CommRing k]
  (C : SuperCartanDatum I) (q t : kˣ) (hC : C.BarConsistent) (ht : t ^ 2 = -1)

include hC ht in
/-- Transport of the entire ordinary Serre ideal, not just its chosen generators. -/
theorem freeTwist_mem_serreIdeal {x : PreF k I} (hx : x ∈ C.serreIdeal (t * q) 1) :
    C.freeTwist t x ∈ C.serreIdeal q (-1) := by
  apply C.wordGauge_mem_serreIdeal (t * q) 1 q (-1) (fun i j ↦ t ^ C.twistPhi i j) _ hx
  intro i j hij
  change C.freeTwist t (C.serreElt (t * q) 1 i j) ∈ C.serreIdeal q (-1)
  rw [C.freeTwist_serreElt t hC ht q hij]
  apply (C.mem_serreIdeal q (-1) _).mpr
  rw [map_smul, C.toSerreF_serreElt q (-1) hij, smul_zero]

end SuperCartanDatum

namespace SuperCartanDatum

variable {I k : Type*} [DecidableEq I] [Finite I] [Field k] [CharZero k]
  (C : SuperCartanDatum I) (q t : kˣ) (hC : C.BarConsistent) (ht : t ^ 2 = -1)
  (hq : Transcendental ℚ (q : k))

include ht hq in
private theorem twisted_parameter_transcendental : Transcendental ℚ ((t * q : kˣ) : k) := by
  have hta : IsAlgebraic ℚ (t : k) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    have h := congrArg (fun u : kˣ ↦ (u : k)) ht
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
    rw [h]
    exact isAlgebraic_one.neg
  intro h
  apply hq
  simpa [Units.val_mul, ← mul_assoc] using hta.inv.mul h

include hC ht hq in
/-- The negative-sign form radical equals the Serre ideal over a field containing
an element whose square is minus one. -/
theorem serreIdeal_neg_one_eq_radical :
    C.serreIdeal q (-1) = PreF.radical (C.chi q (-1)) (C.norm q (-1)) := by
  let d : DecidableEq I := inferInstance
  let := Fintype.ofFinite I
  let o : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  apply le_antisymm (C.serreIdeal_le_radical q (-1) (by simp))
  intro x hx
  obtain ⟨y, rfl⟩ := (C.freeTwist t).surjective x
  apply C.freeTwist_mem_serreIdeal q t hC ht
  rw [C.serreIdeal_one_eq_radical (t * q) (twisted_parameter_transcendental q t ht hq)]
  have he := congrArg (fun e : DecidableEq I ↦
    C.freeTwist t y ∈ @PreF.radical k I _ e (C.chi q (-1)) (C.norm q (-1)))
      (Subsingleton.elim d (fun a b ↦ o.toDecidableEq a b))
  have he' := congrArg (fun e : DecidableEq I ↦
    y ∈ @PreF.radical k I _ e (C.chi (t * q) 1) (C.norm (t * q) 1))
      (Subsingleton.elim d (fun a b ↦ o.toDecidableEq a b))
  exact he'.mpr ((C.freeTwist_mem_radical_iff q t hC ht y).mp (he.mp hx))

include hC ht hq in
/-- Nondegeneracy of the negative-sign Serre presentation over a characteristic-zero
field containing a square root of minus one, with finite index type and transcendental q. -/
theorem serreForm_neg_one_nondegenerate :
    (C.serreForm q (-1) (by simp)).Nondegenerate :=
  (C.serreForm_nondegenerate_iff_ideal_eq q (-1) (by simp)).mpr
    (C.serreIdeal_neg_one_eq_radical q t hC ht hq)

end SuperCartanDatum

end OddMath.CoveringQuantum
