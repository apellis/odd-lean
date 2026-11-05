import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDoubleAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison

/-! # The chosen ordinary-adjunction crossing mate under scalar specialization

The first crossing-derived matrix entry in DeformedMatrixComparison (2), (4)
uses the ordered ordinary-adjunction mate. The scalar comparison must keep
the chosen append isomorphisms, literal restriction equality, unit and
unshifted counit. Normalized cap rows remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

section GenericMaps
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

variable {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α) (M : Superfunctor k A (SVec k))

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J]

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J]

end GenericMaps

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "K" => ELVOld.oldContentAppend D Sc cut (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "Q₀" => probeOldOrdinaryFunctor D Sc m ν
local notation "Q₁" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "Q₂" => probeOldOrdinaryFunctor D Sc m (i :: i :: ν)
variable (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN

end OddMath.QuiverHecke
