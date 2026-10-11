/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlides
/-!
# Degree-zero obstruction to the unscaled disconnected slides

The printed (7.13)–(7.14) of Brundan–Ellis, arXiv:1701.04133v2,
Proposition 7.3(iv), force `(tᵢⱼ - 1) • id = 0` at shifted degree zero.
Over a general ring this is an annihilator condition, not by itself a
contradiction. The final two results give the precise contradiction when
`tᵢⱼ - 1` is a unit and the strand identity is nonzero. They do not assert
nonvanishing, nondegeneracy, or inconsistency of the defining presentation.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- An unscaled degree-zero clockwise bubble slide forces a scalar constraint. -/
theorem unscaled_bubbleRs_zero_constraint (i j : I) (μ : X)
    (h : plcL D Sc μ [up j] [] [] [] (bubRs cs i (wt D μ []) 0) =
      plcL D Sc μ [] [up j] [] [] (bubRs cs i (wt D μ [up j]) 0)) :
    ((Sc.t i j : k) - 1) • 𝟙 ((pres D Sc).obj (ob D μ [up j])) = 0 := by
  rw [bubRs_zero, bubRs_zero, map_smul, map_smul, plcL_id, plcL_id] at h
  have E := congrArg (((Sc.t i j : k) * (cs.c μ i : k)) • ·) h
  simp only [smul_smul, c_wt_upj, wt_nil, mul_inv, Units.val_mul] at E
  have h1 : ((Sc.t i j : k) * (cs.c μ i : k)) * (↑(cs.c μ i)⁻¹ : k) = (Sc.t i j : k) := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h2 : ((Sc.t i j : k) * (cs.c μ i : k)) *
      ((↑(Sc.t i j)⁻¹ : k) * (↑(cs.c μ i)⁻¹ : k)) = 1 := by
    calc
      _ = ((Sc.t i j : k) * (↑(Sc.t i j)⁻¹ : k)) *
          ((cs.c μ i : k) * (↑(cs.c μ i)⁻¹ : k)) := by ring
      _ = 1 := by rw [Units.mul_inv, Units.mul_inv, mul_one]
  rw [h1, h2, one_smul] at E
  rw [sub_smul, one_smul]
  erw [E, sub_self]



/-- The unscaled degree-zero counterclockwise slide forces the same constraint. -/
theorem unscaled_bubbleLs_zero_constraint (i j : I) (μ : X)
    (h : lbub j μ (bubLs cs i (wt D μ [up j]) 0) =
      rbub j μ (bubLs cs i (wt D μ []) 0)) :
    ((Sc.t i j : k) - 1) • 𝟙 ((pres D Sc).obj (ob D μ [up j])) = 0 := by
  unfold lbub rbub at h
  rw [bubLs_zero, bubLs_zero, map_smul, map_smul, plcL_id, plcL_id] at h
  have E := congrArg ((↑(cs.c μ i)⁻¹ : k) • ·) h
  simp only [smul_smul, c_wt_upj, wt_nil, Units.val_mul] at E
  have hc : (↑(cs.c μ i)⁻¹ : k) * ((Sc.t i j : k) * (cs.c μ i : k)) = (Sc.t i j : k) := by
    rw [mul_left_comm, Units.inv_mul, mul_one]
  rw [hc, Units.inv_mul, one_smul] at E
  rw [sub_smul, one_smul]
  erw [E, sub_self]

/-- If the scalar difference is a unit, the unscaled (7.13) is impossible on a
nonzero strand. Nonvanishing is a hypothesis, not an established model here. -/
theorem unscaled_bubbleRs_zero_impossible (i j : I) (μ : X)
    (hu : IsUnit ((Sc.t i j : k) - 1))
    (hne : 𝟙 ((pres D Sc).obj (ob D μ [up j])) ≠ 0) :
    rbub j μ (bubRs cs i (wt D μ []) 0) ≠
      lbub j μ (bubRs cs i (wt D μ [up j]) 0) := by
  intro h
  exact hne (hu.smul_eq_zero.mp (unscaled_bubbleRs_zero_constraint cs i j μ h))

/-- The corresponding precise obstruction to unscaled (7.14). -/
theorem unscaled_bubbleLs_zero_impossible (i j : I) (μ : X)
    (hu : IsUnit ((Sc.t i j : k) - 1))
    (hne : 𝟙 ((pres D Sc).obj (ob D μ [up j])) ≠ 0) :
    lbub j μ (bubLs cs i (wt D μ [up j]) 0) ≠
      rbub j μ (bubLs cs i (wt D μ []) 0) := by
  intro h
  exact hne (hu.smul_eq_zero.mp (unscaled_bubbleLs_zero_constraint cs i j μ h))

end OddMath.SKM
