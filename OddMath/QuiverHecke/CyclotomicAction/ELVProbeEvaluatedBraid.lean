import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentBraid

/-! # The equal-colour braid on evaluated old probes

Brundan–Ellis Definition 1.5: the prescribed negative crossings on the
three successive evaluated content inductions satisfy the braid. The
full inclusion retains the chosen old maps and their super signs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u v w z t
private theorem whiskerRight_total
    {k : Type u} [CommRing k] {C A B : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{t} B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C A} (x : F ⟶ G) (H : Superfunctor k A B) (M : C) :
    (Superfunctor.whiskerRight x H).total M = H.map (x.total M) := by
  change H.map (x.app 0 M) + H.map (x.app 1 M) = H.map (x.app 0 M + x.app 1 M)
  exact H.toFunctor.map_add.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "E₀" => probeEvaluatedInduction D Sc m ν i
local notation "E₁" => probeEvaluatedInduction D Sc m (i :: ν) i
local notation "E₂" => probeEvaluatedInduction D Sc m (i :: i :: ν) i
local notation "t₀" => probeEvaluatedEqualCross D Sc m ν i
local notation "t₁" => probeEvaluatedEqualCross D Sc m (i :: ν) i

/-- The evaluated braid retains the exact threefold chosen induction maps. -/
theorem probeEvaluatedEqualCross_braid (N : ProbeEvaluatedModules D Sc m ν) :
    (E₂).map ((t₀).total N) ≫ (t₁).total ((E₀).obj N) ≫ (E₂).map ((t₀).total N) =
      (t₁).total ((E₀).obj N) ≫ (E₂).map ((t₀).total N) ≫ (t₁).total ((E₀).obj N) := by
  apply InducedCategory.hom_ext
  change (induction (oldContentAppend D Sc (probeCutoff D m) (i :: i :: ν) i)).map
      (((t₀).total N).hom) ≫ (((t₁).total ((E₀).obj N)).hom) ≫
        (induction (oldContentAppend D Sc (probeCutoff D m) (i :: i :: ν) i)).map
          (((t₀).total N).hom) =
    (((t₁).total ((E₀).obj N)).hom) ≫
      (induction (oldContentAppend D Sc (probeCutoff D m) (i :: i :: ν) i)).map
        (((t₀).total N).hom) ≫ (((t₁).total ((E₀).obj N)).hom)
  rw [probeEvaluatedEqualCross_native_total, probeEvaluatedEqualCross_native_total]
  exact oldContentInductionCross_braid D Sc (probeCutoff D m) ν i N.obj

/-- Three consecutive chosen evaluated inductions. -/
abbrev probeEvaluatedTripleInduction :
    Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: i :: i :: ν)) := ⟨E₀ ⋙ E₁ ⋙ E₂⟩

/-- The chosen first-pair crossing mapped by the third evaluated induction. -/
abbrev probeEvaluatedBraidPrefix : End (probeEvaluatedTripleInduction D Sc m ν i) :=
  Superfunctor.whiskerRight t₀ ⟨E₂⟩

/-- The independently chosen second-pair crossing after the first induction. -/
abbrev probeEvaluatedBraidSuffix : End (probeEvaluatedTripleInduction D Sc m ν i) :=
  Superfunctor.whiskerLeft ⟨E₀⟩ t₁

theorem probeEvaluatedBraidPrefix_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedBraidPrefix D Sc m ν i).total N = (E₂).map ((t₀).total N) :=
  whiskerRight_total _ _ N

theorem probeEvaluatedBraidSuffix_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedBraidSuffix D Sc m ν i).total N = (t₁).total ((E₀).obj N) := rfl

/-- The whole natural braid uses the selected negative crossings on both pairs. -/
theorem probeEvaluatedBraid :
    probeEvaluatedBraidPrefix D Sc m ν i ≫ probeEvaluatedBraidSuffix D Sc m ν i ≫
      probeEvaluatedBraidPrefix D Sc m ν i =
    probeEvaluatedBraidSuffix D Sc m ν i ≫ probeEvaluatedBraidPrefix D Sc m ν i ≫
      probeEvaluatedBraidSuffix D Sc m ν i := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    Superfunctor.comp_total, Superfunctor.comp_total,
    probeEvaluatedBraidPrefix_total, probeEvaluatedBraidSuffix_total]
  exact probeEvaluatedEqualCross_braid D Sc m ν i N
end OddMath.QuiverHecke
