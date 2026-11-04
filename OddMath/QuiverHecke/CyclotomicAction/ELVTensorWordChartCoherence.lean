import OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomContexts

/-! # Append coherence of the prescribed tensor word chart

SwappedVacuumCoordinates §§2–5: the global selected tensor-word chart
agrees with its prescribed single-letter append chart through the literal
whole-functor append equality. This is the first coherence input for an
observation independent of the chosen local layer decomposition.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorVacuumWords
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP

/-- The global whole-Hom word chart is exactly its given append chart,
including the original tensor-Hom word equality. -/
theorem chart_append_hom (ν : List I) (i : I) :
    (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom =
      eqToHom (congrArg (fun F => F.obj R) (wordHom_append D Sc m cutoff L ΛP ΛR ν i)) ≫
        (dotChart D Sc m cutoff L ΛP ΛR ν i).hom := by
  simp only [chart,dotChart,valueIso,List.reverseRecOn_concat,
    PowerWordEvaluation.chart_append, PowerWordEvaluation.appendChart,
    Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Iso.symm_hom]
  simp only [eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end OddMath.QuiverHecke.ELVOld.TensorVacuumWords
