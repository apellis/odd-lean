import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridCrossSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations

/-! # The chosen equal crossing on scalar-evaluated OLD probes

Brundan–Ellis Definition 1.5, (1.7): restrict the prescribed negative
double-induction crossing to the full scalar-evaluated module category.
The actual balanced flattening, every input module map, and odd crossing
parity are retained. No inverse or complete-factor hypothesis is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν i
local notation "K" => oldContentAppend D Sc cut (i :: ν) i
local notation "hCross" => oldContentMatrixCross_supernatural D Sc cut ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i
local notation "E'" => probeEvaluatedInduction D Sc m (i :: ν) i

/-- The prescribed negative crossing, with its full underlying module map. -/
def probeEvaluatedEqualCrossComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (E ⋙ E').obj N ⟶ (E ⋙ E').obj N :=
  ⟨-gridDoubleCrossComponent J K hCross N.obj⟩

/-- Restriction retains supernaturality on every even or odd input map. -/
theorem probeEvaluatedEqualCrossComponent_supernatural :
    IsSupernatural k (D.parity i) (F := E ⋙ E') (G := E ⋙ E')
      (probeEvaluatedEqualCrossComponent D Sc m ν i) where
  mem N := (parity (R := k) _ _ (D.parity i)).neg_mem
    (gridDoubleCrossComponent_mem J K hCross N.obj)
  naturality := by
    intro M N p f hf
    apply InducedCategory.hom_ext
    change f.hom ∈ parity (R := k) _ _ p at hf
    simpa only [Preadditive.comp_neg, Preadditive.neg_comp, smul_neg] using
      congrArg Neg.neg ((gridDoubleCrossComponent_supernatural J K hCross).naturality hf)

/-- The homogeneous crossing on the actual evaluated double induction. -/
def probeEvaluatedEqualCross :
    End (⟨E ⋙ E'⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: i :: ν))) :=
  (probeEvaluatedEqualCrossComponent_supernatural D Sc m ν i).toSuperNatTrans

theorem probeEvaluatedEqualCross_mem :
    probeEvaluatedEqualCross D Sc m ν i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem
    (probeEvaluatedEqualCrossComponent_supernatural D Sc m ν i)

/-- Each parity component is the identical chosen OLD component. -/
theorem probeEvaluatedEqualCross_native_app (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedEqualCross D Sc m ν i).app q N).hom =
      (inductionModuleCross J K hCross).app q N.obj := by
  rw [inductionModuleCross_app]
  change (if q = D.parity i then probeEvaluatedEqualCrossComponent D Sc m ν i N else 0).hom = _
  split_ifs <;> rfl

/-- Total evaluation retains the specified component without changing its sign. -/
theorem probeEvaluatedEqualCross_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedEqualCross D Sc m ν i).total N =
      probeEvaluatedEqualCrossComponent D Sc m ν i N :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := (⟨E ⋙ E'⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: i :: ν))))
    (G := (⟨E ⋙ E'⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: i :: ν))))
    (probeEvaluatedEqualCrossComponent_supernatural D Sc m ν i) N

/-- The faithful full inclusion sends the crossing to the chosen OLD crossing. -/
theorem probeEvaluatedEqualCross_native_total (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedEqualCross D Sc m ν i).total N).hom =
      (inductionModuleCross J K hCross).total N.obj := by
  rw [probeEvaluatedEqualCross_total, inductionModuleCross_total]
  rfl

/-- Naturality for an arbitrary input arrow, including sums of both parities. -/
theorem probeEvaluatedEqualCrossComponent_naturality_twist
    {M N : ProbeEvaluatedModules D Sc m ν} (f : M ⟶ N) :
    (E ⋙ E').map f ≫
        probeEvaluatedEqualCrossComponent D Sc m ν i N =
      probeEvaluatedEqualCrossComponent D Sc m ν i M ≫
        (E ⋙ E').map (twist k (D.parity i) f) :=
  (probeEvaluatedEqualCrossComponent_supernatural D Sc m ν i).naturality_twist f

/-- The square-zero identity holds on the entire evaluated probe category. -/
theorem probeEvaluatedEqualCross_square :
    probeEvaluatedEqualCross D Sc m ν i ≫ probeEvaluatedEqualCross D Sc m ν i = 0 := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeEvaluatedEqualCross D Sc m ν i).total N).hom ≫
    ((probeEvaluatedEqualCross D Sc m ν i).total N).hom = 0
  simp only [probeEvaluatedEqualCross_native_total]
  rw [← Superfunctor.comp_total,
    inductionModuleCross_square J K hCross (oldContentEqualCross_square D Sc cut ν i)]
  rfl

end OddMath.QuiverHecke
