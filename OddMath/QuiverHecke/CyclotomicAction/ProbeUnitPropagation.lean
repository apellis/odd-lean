import OddMath.QuiverHecke.CyclotomicAction.ProbeFirstDot

/-! # Direct units in same-colour nilHecke probe blocks

The even intertwiner conjugates the two dots. The odd intertwiner square
and an inverse of the preceding dot construct a right inverse of the next dot;
existing kernel propagation makes this a two-sided inverse. Both arguments work
over every ring without finite-dimensionality.
-/
namespace OddMath.QuiverHecke.SignedNilHecke
variable {B : Type*} [Ring B]

theorem EvenTwo.isUnit_right_direct {u v T : B} (h : EvenTwo u v T) (hu : IsUnit u) :
    IsUnit v := by
  have hp : IsUnit (phiEven u v T) :=
    ⟨⟨phiEven u v T, phiEven u v T, h.phiEven_mul_phiEven, h.phiEven_mul_phiEven⟩, rfl⟩
  have he : phiEven u v T * u * phiEven u v T = v := by
    rw [mul_assoc, h.x_mul_phiEven, ← mul_assoc, h.phiEven_mul_phiEven, one_mul]
  rw [← he]
  exact (hp.mul hu).mul hp

/-- The odd intertwiner square supplies a right inverse; kernel propagation
then makes it a two-sided unit. No finite-dimensionality is required. -/
theorem OddTwo.isUnit_right_direct {u v T : B} (h : OddTwo u v T) (hu : IsUnit u) :
    IsUnit v := by
  rcases hu with ⟨U, rfl⟩
  let a : B := ↑(U⁻¹)
  let φ : B := phiOdd (U : B) v T
  have hua : (U : B) * a = 1 := U.val_inv
  have hphi : v * φ * a = -φ := by
    have he := congrArg (fun z : B => z * a) h.x_succ_mul_phiOdd
    change (v * φ) * a = -(φ * (U : B)) * a at he
    simpa only [neg_mul, mul_assoc, hua, mul_one] using he
  have hs : φ * φ = (U : B) * U + v * v := by
    change phiOdd (U : B) v T * phiOdd (U : B) v T = _
    rw [h.phiOdd_mul_phiOdd]
    simp only [sub_mul, mul_sub, h.vu']
    noncomm_ring
  have hf : v * (-φ * a * φ - v) = (U : B) * U := by
    calc
      v * (-φ * a * φ - v) = -(v * φ * a) * φ - v * v := by noncomm_ring
      _ = φ * φ - v * v := by rw [hphi, neg_neg]
      _ = (U : B) * U := by rw [hs]; noncomm_ring
  have hr : v * ((-φ * a * φ - v) * (a * a)) = 1 := by
    rw [← mul_assoc, hf]
    calc
      ((U : B) * U) * (a * a) = (U : B) * ((U : B) * a) * a := by noncomm_ring
      _ = 1 := by rw [hua, mul_one, hua]
  have hinj := h.right_mul_injective (IsUnit.isUnit_iff_mulLeft_bijective.mp U.isUnit).1
  apply IsUnit.isUnit_iff_mulLeft_bijective.mpr
  refine ⟨hinj, ?_⟩
  intro z
  refine ⟨((-φ * a * φ - v) * (a * a)) * z, ?_⟩
  change v * (((-φ * a * φ - v) * (a * a)) * z) = z
  calc
    _ = (v * ((-φ * a * φ - v) * (a * a))) * z := (mul_assoc _ _ _).symm
    _ = z := by rw [hr, one_mul]

end OddMath.QuiverHecke.SignedNilHecke

namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

/-- The direct unit step in the actual word corner, for either parity. -/
theorem cyclotomicBlock_dot_isUnit (pre post : List I) (i : I)
    (hu : IsUnit (cyclotomicBlockDot D Sc a pre post i pre.length)) :
    IsUnit (cyclotomicBlockDot D Sc a pre post i (pre.length+1)) := by
  rcases StringDiagrams.Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · exact (cyclotomicBlock_evenTwo D Sc a pre post i hi).isUnit_right_direct hu
  · exact (cyclotomicBlock_oddTwo D Sc a pre post i hi).isUnit_right_direct hu

end OddMath.QuiverHecke
