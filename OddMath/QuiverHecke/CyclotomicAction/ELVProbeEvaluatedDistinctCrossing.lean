import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossMate

/-! # The positive distinct crossing and its evaluated OLD mate

Brundan–Ellis Definition 1.5, (1.12): the chosen positive rectangular
crossing restricts to scalar-evaluated OLD modules. Bending it by the
specified lower and upper right adjunctions gives the already constructed
evaluated OLD mate. The append flattenings and both bending maps are kept.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν j
local notation "K" => oldContentAppend D Sc cut ν i
local notation "L" => oldContentAppend D Sc cut (j :: ν) i
local notation "M" => oldContentDistinctUpperAppend D Sc cut ν i j
local notation "hCross" => oldContentDistinctCross_supernatural D Sc cut ν i j
local notation "P" => ProbeEvaluatesCoefficients D m Sc ν
local notation "Q" => ProbeEvaluatesCoefficients D m Sc (i :: j :: ν)
local notation "Ei" => probeEvaluatedE D Sc m ν i
local notation "Ej" => probeEvaluatedE D Sc m ν j
local notation "V" => probeEvaluatedE D Sc m (j :: ν) i
local notation "U" => probeAppendToE D Sc m (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)
local notation "A" => probeEvaluatedRightAdjunction D Sc m ν j
local notation "B" => probeAppendToRightAdjunction D Sc m (i :: ν) j (i :: j :: ν)
  (List.Perm.swap i j ν)

private theorem distinctCrossSource_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P N) :
    Q (((induction K ⋙ induction M).obj N)) :=
  ((probeEvaluatedInduction D Sc m ν i ⋙
    probeEvaluatedAppendTo D Sc m (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)).obj
      ⟨N, hN⟩).property

private theorem distinctCrossTarget_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P N) :
    Q (((induction J ⋙ induction L).obj N)) :=
  ((probeEvaluatedInduction D Sc m ν j ⋙ probeEvaluatedInduction D Sc m (j :: ν) i).obj
    ⟨N, hN⟩).property

/-- The positive OLD rectangular crossing, on the chosen evaluated E functors. -/
def probeEvaluatedDistinctCross : Ei ≫ U ⟶ Ej ≫ V :=
  fullLiftTrans P Q (distinctCrossSource_closed D Sc m ν i j)
    (distinctCrossTarget_closed D Sc m ν i j)
    (rectangularCrossComponent_supernatural J K L M hCross).toSuperNatTrans

theorem probeEvaluatedDistinctCross_mem :
    probeEvaluatedDistinctCross D Sc m ν i j ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q (distinctCrossSource_closed D Sc m ν i j)
      (distinctCrossTarget_closed D Sc m ν i j) _
      (rectangularCrossComponent_supernatural J K L M hCross).toSuperNatTrans_isHomogeneous)

/-- Every parity component retains the same OLD flatten-crossing-expand map. -/
theorem probeEvaluatedDistinctCross_native_app (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedDistinctCross D Sc m ν i j).app q N).hom =
      (rectangularCrossComponent_supernatural J K L M hCross).toSuperNatTrans.app q N.obj := rfl

/-- Bending uses the original lower counit and upper unit, with no rescaling. -/
theorem probeEvaluatedDistinctRectangularMate_eq :
    SKM.rectangularMate A B Ei V (probeEvaluatedDistinctCross D Sc m ν i j) =
      probeEvaluatedDistinctMate D Sc m ν i j := by
  apply Superfunctor.hom_ext
  intro q N
  rw [SKM.rectangularMate_piscat_app A B Ei V (probeEvaluatedDistinctCross D Sc m ν i j)
    (fun Z => Superfunctor.app_eq_zero_of_mem (B).unit_mem (by decide) Z)
    (fun Z => Superfunctor.app_eq_zero_of_mem (A).counit_mem (by decide) Z)]
  apply InducedCategory.hom_ext
  change (adjunctionUnit M).app _ ≫
      (restriction M).map
        ((rectangularCrossComponent_supernatural J K L M hCross).toSuperNatTrans.app q
          ((restriction J).obj N.obj)) ≫
      (restriction M).map ((induction L).map ((adjunctionCounit J).app N.obj)) =
    (rectangularMateHom J K L M hCross).app q N.obj
  by_cases hq : q = D.parity i * D.parity j
  · subst q
    rw [IsSupernatural.toSuperNatTrans_app]
    rw [rectangularMateHom, IsSupernatural.toSuperNatTrans_app]
    rfl
  · simp only [rectangularMateHom, IsSupernatural.toSuperNatTrans, hq, ite_false,
      Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

/-- The given bent crossing has its constructed OLD inverse at distinct colours. -/
theorem probeEvaluatedDistinctRectangularMate_isIso (hij : i ≠ j) :
    IsIso (SKM.rectangularMate A B Ei V (probeEvaluatedDistinctCross D Sc m ν i j)) := by
  rw [probeEvaluatedDistinctRectangularMate_eq,
    ← probeEvaluatedDistinctMateIso_hom D Sc m ν i j hij]
  infer_instance

/-- The presentation's ordered sideways crossing is the same chosen OLD mate. -/
theorem probeEvaluatedDistinctCrossMate_eq :
    SKM.crossMate A B (probeEvaluatedDistinctCross D Sc m ν i j) =
      probeEvaluatedDistinctMate D Sc m ν i j :=
  (SKM.crossMate_piscat_eq_rectangular A B Ei V
    (probeEvaluatedDistinctCross D Sc m ν i j)).trans
    (probeEvaluatedDistinctRectangularMate_eq D Sc m ν i j)

/-- The actual presentation sideways crossing has the constructed OLD inverse. -/
theorem probeEvaluatedDistinctCrossMate_isIso (hij : i ≠ j) :
    IsIso (SKM.crossMate A B (probeEvaluatedDistinctCross D Sc m ν i j)) := by
  rw [probeEvaluatedDistinctCrossMate_eq,
    ← probeEvaluatedDistinctMateIso_hom D Sc m ν i j hij]
  infer_instance

end OddMath.QuiverHecke
