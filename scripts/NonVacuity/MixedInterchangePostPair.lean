import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePostPair
import StringDiagrams.Super.DrinfeldCenterPiCounterexample

/-! Nonzero odd post crossings with independently shifted letters. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
namespace NonVacuity.MixedInterchangePostPair
private abbrev B := TwoEnvelope ℚ (UnitTwo ℚ)
private def o : B := ⟨UnitTwo.pt⟩
private def e (p : ZMod 2) : o ⟶ o := ⟨p, ⟨⟩⟩
private def χ : e 0 ≫ e 0 ⟶ e 1 ≫ e 0 := Envelope.ofHom (1 : ℚ)
private theorem χ_odd : χ ∈ parity (R := ℚ) _ _ 1 := by
  rw [Envelope.mem_parity_iff]
  change (1 : ℚ) ∈ trivialGrading ℚ (0 : ZMod 2)
  simp

-- The two shifts differ and the normalization coefficient is negative.
example := postPairIso_cross_remove (k := ℚ) (e 0) (e 0) (e 1) (e 0) 0 1 (e 0) χ_odd
example : sign ℚ (((0 : ZMod 2) + 1) * 1) = -1 := by decide
example : χ ≠ 0 := by
  intro h
  have h' := congrArg Envelope.toHom h
  change (1 : ℚ) = 0 at h'
  norm_num at h'

example := homMixedInterchange_postPair_shifts (k := ℚ) (e 1) (e 0) (e 1) (e 0)
  1 0 0 1
example := homMixedInterchange_postPair_between (k := ℚ) (e 1) (e 0)
  (e 0) (e 0) (e 1) (e 0) 0 1 0 1 (by simp) χ

#print axioms OddMath.SKM.homMixedInterchange_postPair_shifts
#print axioms OddMath.SKM.postPairIso_cross_remove
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.resCore_mixedInterchange_pair
end NonVacuity.MixedInterchangePostPair
