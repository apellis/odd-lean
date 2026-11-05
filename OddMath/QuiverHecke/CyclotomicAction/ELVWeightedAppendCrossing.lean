import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPairAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositeComparison

/-! # The equal-colour crossing through the weighted quotient

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) require the
last-strand crossing, with the prescribed sign, on the chosen two-induction
comparison. The literal quotient of `crossLast` is identified with the
existing `crossTwo` append component under word associativity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- The crossing at the last two positions on successive singleton appends. -/
def truncatedEqualCrossComponent (s : TruncatedCategory D Sc cutoff N) :
    (T ⋙ T).obj s ⟶ (T ⋙ T).obj s :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))

/-- Quotienting retains the literal affine crossing. -/
theorem oldTruncateFunctor_map_equalCross (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s) =
      truncatedEqualCrossComponent D Sc cutoff N i ((Q).obj s) := rfl

/-- Full coefficient supernaturality descends from the old crossing. -/
theorem truncatedEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i)
      (truncatedEqualCrossComponent D Sc cutoff N i) := by
  apply IsSupernatural.of_twist
  · intro s
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word i i))
  · intro s t f
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N s.word t.word).mkQ_surjective f
    let f' : (⟨s.word⟩ : OldCategory D Sc cutoff) ⟶ ⟨t.word⟩ :=
      (ideal D Sc cutoff s.word t.word).mkQ a
    have h := congrArg (fun g => (Q).map g)
      ((CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).naturality_twist f')
    simp only [Functor.map_comp, map_twist] at h
    rw [map_twist]
    exact h

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

end OddMath.QuiverHecke.ELVOld
