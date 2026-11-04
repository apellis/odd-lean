import OddMath.QuiverHecke.CyclotomicAction.ELVTensorWordChartCoherence

/-! # Pair coherence of the prescribed tensor word chart

SwappedVacuumCoordinates §§2–5: compare the global whole-word chart
with the prescribed two-letter chart at the canonical successive weights.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorVacuumWords
open CyclotomicAction SwappedAssembly
private theorem eqToHom_comp_heq {C : Type*} [Category* C]
    {A B T : C} (h : A = B) (f : B ⟶ T) : HEq (eqToHom h ≫ f) f := by
  subst B
  simp only [eqToHom_refl, Category.id_comp]
  rfl

universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR

/-- The global whole tensor Hom retains the two chronological appends. -/
theorem wordHom_pair (ν : List I) (i j : I) :
    wordHom D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i]) =
      wordHom D Sc m cutoff L ΛP ΛR ν ≫
        (W).E j (PowerWordWeight.wordWeight_append D ΛR ν j) ≫
          (W).E i (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i) := by
  rw [wordHom_append, wordHom_append]
  rfl

/-- The prescribed global chart equals the pair chart through the equality
of the entire tensor Hom, before any generator is applied. -/
theorem chart_pair_hom (ν : List I) (i j : I) :
    (chart D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i])).hom =
      eqToHom (congrArg (fun F => F.obj R) (wordHom_pair D Sc m cutoff L ΛP ΛR ν i j)) ≫
        (pairChart D Sc m cutoff L ΛP ΛR ν i j
          (PowerWordWeight.wordWeight_append D ΛR ν j)
          (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i)).hom := by
  simp only [chart, pairChart, valueIso, List.reverseRecOn_concat,
    PowerWordEvaluation.chart_append, PowerWordEvaluation.pairChart,
    PowerWordWeightCross.recursivePairIso, PowerWordWeightCross.appendIsoAtWeights,
    Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.map_comp,
    Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  simp only [eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- Reading the canonical source-functor equality as a transport gives
one and the same append chart on the entire value Hom. -/
theorem chart_append_heq (ν : List I) (i : I) :
    HEq (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom
      (dotChart D Sc m cutoff L ΛP ΛR ν i).hom :=
  (heq_of_eq (chart_append_hom D Sc m cutoff L ΛP ΛR ν i)).trans
    (eqToHom_comp_heq _ _)

/-- The two-letter local chart has the same whole-map value as the global
word chart, including both equal and distinct colours. -/
theorem chart_pair_heq (ν : List I) (i j : I) :
    HEq (chart D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i])).hom
      (pairChart D Sc m cutoff L ΛP ΛR ν i j
        (PowerWordWeight.wordWeight_append D ΛR ν j)
        (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i)).hom :=
  (heq_of_eq (chart_pair_hom D Sc m cutoff L ΛP ΛR ν i j)).trans
    (eqToHom_comp_heq _ _)

end OddMath.QuiverHecke.ELVOld.TensorVacuumWords
