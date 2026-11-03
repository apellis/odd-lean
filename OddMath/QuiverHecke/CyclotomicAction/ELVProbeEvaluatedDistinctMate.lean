import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctIso

/-! # Distinct mates on the scalar-evaluated OLD probe

Brundan–Ellis Definition 1.5, (1.12): restrict the prescribed OLD
cup-crossing-cap and its constructed PBW inverse through the full evaluated
module subcategories. The upper append uses its given common target list.
Both inverse identities and all input-map parity signs are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
open CyclotomicAction
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
local notation "S" => probeEvaluatedRestriction D Sc m ν j ⋙ probeEvaluatedInduction D Sc m ν i
local notation "T" => probeEvaluatedInduction D Sc m (j :: ν) i ⋙
  probeEvaluatedRestrictTo D Sc m (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)
local notation "P" => ProbeEvaluatesCoefficients D m Sc (j :: ν)
local notation "Q" => ProbeEvaluatesCoefficients D m Sc (i :: ν)

private theorem distinctMateSource_closed
    (N : Superfunctor k (OldContentCategory D Sc cut (j :: ν)) (SVec k)) (hN : P N) :
    Q ((rectangularMateSourceFunctor J K).obj N) :=
  ((S).obj ⟨N, hN⟩).property

private theorem distinctMateTarget_closed
    (N : Superfunctor k (OldContentCategory D Sc cut (j :: ν)) (SVec k)) (hN : P N) :
    Q ((rectangularMateTargetFunctor L M).obj N) :=
  ((T).obj ⟨N, hN⟩).property

/-- The lower restriction-induction, retaining all scalar-evaluated inputs. -/
abbrev probeEvaluatedDistinctMateSource :
    Superfunctor k (ProbeEvaluatedModules D Sc m (j :: ν))
      (ProbeEvaluatedModules D Sc m (i :: ν)) :=
  fullLiftSuperfunctor P Q (rectangularMateSourceFunctor J K)
    (distinctMateSource_closed D Sc m ν i j)

/-- The upper induction-restriction with the prescribed target certificate. -/
abbrev probeEvaluatedDistinctMateTarget :
    Superfunctor k (ProbeEvaluatedModules D Sc m (j :: ν))
      (ProbeEvaluatedModules D Sc m (i :: ν)) :=
  fullLiftSuperfunctor P Q (rectangularMateTargetFunctor L M)
    (distinctMateTarget_closed D Sc m ν i j)

/-- Restriction retains the selected lower E/F functor exactly. -/
theorem probeEvaluatedDistinctMateSource_toFunctor :
    (probeEvaluatedDistinctMateSource D Sc m ν i j).toFunctor = S := rfl

/-- Restriction retains the selected upper E/F functor exactly. -/
theorem probeEvaluatedDistinctMateTarget_toFunctor :
    (probeEvaluatedDistinctMateTarget D Sc m ν i j).toFunctor = T := rfl

/-- The entire OLD positive cup-crossing-cap as an evaluated module map. -/
def probeEvaluatedDistinctMateComponent (N : ProbeEvaluatedModules D Sc m (j :: ν)) :
    (probeEvaluatedDistinctMateSource D Sc m ν i j).obj N ⟶
      (probeEvaluatedDistinctMateTarget D Sc m ν i j).obj N :=
  ⟨oldContentDistinctMateComponent D Sc cut ν i j N.obj⟩

/-- The given distinct mate, homogeneous and natural on every input map. -/
def probeEvaluatedDistinctMate :
    probeEvaluatedDistinctMateSource D Sc m ν i j ⟶
      probeEvaluatedDistinctMateTarget D Sc m ν i j :=
  fullLiftTrans P Q (distinctMateSource_closed D Sc m ν i j)
    (distinctMateTarget_closed D Sc m ν i j) (rectangularMateHom J K L M hCross)

theorem probeEvaluatedDistinctMate_mem :
    probeEvaluatedDistinctMate D Sc m ν i j ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q (distinctMateSource_closed D Sc m ν i j)
      (distinctMateTarget_closed D Sc m ν i j) (rectangularMateHom J K L M hCross)
      (Superfunctor.mem_parity_iff_isHomogeneous.mp (rectangularMateHom_mem J K L M hCross)))

/-- The chosen total forward is the literal OLD mate on the same module. -/
theorem probeEvaluatedDistinctMate_total (N : ProbeEvaluatedModules D Sc m (j :: ν)) :
    (probeEvaluatedDistinctMate D Sc m ν i j).total N =
      probeEvaluatedDistinctMateComponent D Sc m ν i j N := by
  apply InducedCategory.hom_ext
  change (rectangularMateHom J K L M hCross).total N.obj = _
  exact rectangularMateHom_total J K L M hCross N.obj

/-- The actual PBW inverse remains a map of the full evaluated category. -/
def probeEvaluatedDistinctMateModuleIso (hij : i ≠ j)
    (N : ProbeEvaluatedModules D Sc m (j :: ν)) :
    (probeEvaluatedDistinctMateSource D Sc m ν i j).obj N ≅
      (probeEvaluatedDistinctMateTarget D Sc m ν i j).obj N :=
  ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc (i :: ν))
    (oldContentDistinctMateModuleIso D Sc cut ν i j hij N.obj)

theorem probeEvaluatedDistinctMateModuleIso_hom (hij : i ≠ j)
    (N : ProbeEvaluatedModules D Sc m (j :: ν)) :
    (probeEvaluatedDistinctMateModuleIso D Sc m ν i j hij N).hom =
      (probeEvaluatedDistinctMate D Sc m ν i j).total N := by
  rw [probeEvaluatedDistinctMate_total]
  apply InducedCategory.hom_ext
  exact oldContentDistinctMateModuleIso_hom D Sc cut ν i j hij N.obj

/-- The inverse is the previously constructed OLD inverse without a gauge change. -/
theorem probeEvaluatedDistinctMateModuleIso_inv_native (hij : i ≠ j)
    (N : ProbeEvaluatedModules D Sc m (j :: ν)) :
    (probeEvaluatedDistinctMateModuleIso D Sc m ν i j hij N).inv.hom =
      (oldContentDistinctMateModuleIso D Sc cut ν i j hij N.obj).inv := rfl

/-- The whole chosen distinct mate is invertible on scalar-evaluated inputs. -/
def probeEvaluatedDistinctMateIso (hij : i ≠ j) :
    probeEvaluatedDistinctMateSource D Sc m ν i j ≅
      probeEvaluatedDistinctMateTarget D Sc m ν i j :=
  OddMath.HomogeneousSuperfunctorIso.ofHom
    (probeEvaluatedDistinctMate D Sc m ν i j) (probeEvaluatedDistinctMate_mem D Sc m ν i j)
    (probeEvaluatedDistinctMateModuleIso D Sc m ν i j hij)
    (probeEvaluatedDistinctMateModuleIso_hom D Sc m ν i j hij)

@[simp] theorem probeEvaluatedDistinctMateIso_hom (hij : i ≠ j) :
    (probeEvaluatedDistinctMateIso D Sc m ν i j hij).hom =
      probeEvaluatedDistinctMate D Sc m ν i j :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

/-- The input-natural inverse has the same crossing parity. -/
theorem probeEvaluatedDistinctMateIso_inv_mem (hij : i ≠ j) :
    (probeEvaluatedDistinctMateIso D Sc m ν i j hij).inv ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_inv_mem _ _ _ _

end OddMath.QuiverHecke
