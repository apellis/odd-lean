import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridComposition

/-! # The selected scalar comparison for two append inductions

The crossing comparison in DeformedActionAssembly §§5–6 and
DeformedMatrixComparison (2), (4) uses the composite of the selected
single-letter module isomorphisms. Its generator formula retains both old
coefficient arrows and the canonical order of the two append inductions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u

section EvenMap
variable {k : Type u} [CommRing k]
  {C A : Type u} [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)

end EvenMap

section MappedAppend
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (μ : List I)
  (R : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) μ) (SVec k))
  (hR : ProbeEvaluatesCoefficients D m Sc μ R)
  (M : Superfunctor k (OrdinaryContentCategory D Sc
    (probePolynomial (k := k) (probeDotExponent D) m) μ) (SVec k))
  (c : probeOrdinaryModuleSuperfunctor D Sc m μ R hR ≅ M) (j : I)
local notation "JR" => ELVOld.oldContentAppend D Sc (probeCutoff D m) μ j
local notation "TR" => probeOrdinaryAppend D Sc m μ j
local notation "QR" => probeOldOrdinaryFunctor D Sc m μ
local notation "UR" => probeOldOrdinaryFunctor D Sc m (j :: μ)

end MappedAppend

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i j : I)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELVOld.oldContentAppend D Sc (probeCutoff D m) (i :: ν) j
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) j
local notation "L" => ELVOld.BalancedInduction.induced J N
local notation "hL" => probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN
local notation "Q₀" => probeOldOrdinaryFunctor D Sc m ν
local notation "Q₁" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "Q₂" => probeOldOrdinaryFunctor D Sc m (j :: i :: ν)

end OddMath.QuiverHecke
