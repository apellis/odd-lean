import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryWordCorner
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryParity
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendSpecialization
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPDistinct

/-! # The invertible appended dot on the ordinary probe category
The exact scalar image of the canonical old append dot is supernatural
and a word-corner unit on every appended word, including vacuum append.
This supplies the source transformation for the scalar coend comparison.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "O" => OrdinaryContentCategory D Sc a ν

/-- The literal last dot in the actual ordinary quotient category. -/
def probeOrdinaryAppendDot (i : I) (v : O) :
    (probeOrdinaryAppend D Sc m ν i).obj v ⟶ (probeOrdinaryAppend D Sc m ν i).obj v :=
  (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
    (dotE D Sc (v.word ++ [i]) v.word.length)

/-- No new dot normalization is chosen: this is the scalar image of the old component. -/
theorem probeOrdinaryAppendDot_old (i : I)
    (v : ELVOld.OldContentCategory D Sc cut ν) :
    (probeOldOrdinaryFunctor D Sc m (i :: ν)).map
      (show (ELVOld.oldContentAppend D Sc cut ν i).obj v ⟶
        (ELVOld.oldContentAppend D Sc cut ν i).obj v from
          ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v.obj) =
      probeOrdinaryAppendDot D Sc m ν i ((probeOldOrdinaryFunctor D Sc m ν).obj v) := by
  rw [ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent_eq]
  change (cycHom D Sc a _ _).mkQ
    (elvProbeScalarHom D m Sc _ _
      (ELVOld.affineUnit D Sc cut _ _ (dotE D Sc (v.obj.word ++ [i]) v.obj.word.length ^ 1))) = _
  rw [pow_one, elvProbeScalarHom_affineUnit]
  rfl

/-- The scalar dot retains its full supernatural sign on ordinary Homs. -/
theorem probeOrdinaryAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (probeOrdinaryAppendDot D Sc m ν i) := by
  refine ⟨?_, ?_⟩
  · intro v
    exact probeOrdinaryHomSpace_mk_mem D Sc m (positionedDot_parity D Sc v.word [] i)
  · intro v w q f hf
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    have h := MonoidalSupercategory.super_interchange hfr (firstDot_parity D Sc i [])
    rw [whiskerLeft_dotE D Sc w.word i rfl, whiskerLeft_dotE D Sc v.word i rfl] at h
    have hq := congrArg (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ h
    rw [map_zsmul, koszulSign_smul (R := k)] at hq
    change (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      ((fr ▷ (pres D Sc).obj (ob D [i])) ≫ dotE D Sc (w.word ++ [i]) w.word.length) =
      sign k (D.parity i * q) •
        (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
          (dotE D Sc (v.word ++ [i]) v.word.length ≫ (fr ▷ (pres D Sc).obj (ob D [i])))
    simpa only [mul_comm q (D.parity i)] using hq

variable [Fintype I]
/-- The literal appended dot is an actual endomorphism unit, including at height zero. -/
theorem probeOrdinaryAppendDot_isUnit [Fact Sc.PureNilpotent] (i : I) (v : O) :
    IsUnit (End.of (probeOrdinaryAppendDot D Sc m ν i v)) := by
  let s : Word I (v.word.length + 1) := ⟨v.word ++ [i], by simp⟩
  have hs : s.val.Perm (i :: ν) := ((probeOrdinaryAppend D Sc m ν i).obj v).wordPerm
  exact probeOrdinaryWordDot_isUnit D Sc (i :: ν) m s hs v.word.length (Nat.lt_succ_self _)

end OddMath.QuiverHecke