import OddMath.QuiverHecke.CyclotomicAction.ELVTensorPairChartCoherence

/-! # Global tensor word charts in arbitrary outer contexts

SwappedVacuumCoordinates §§2–5: the prescribed recursive outer E charts
retain the same global concatenated-word chart on whole regular-probe
values. All comparisons in the final dot and pair statements are supplied
by the actual word constructions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorVacuumWords
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP

private theorem postValue_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {A : ELVWeightProduct D Sc cutoff N ΛR x} {A' : ELVWeightProduct D Sc cutoff N ΛR x'}
    (hA : HEq A A') :
    HEq ((elvE D Sc cutoff N i ΛR h).obj A) ((elvE D Sc cutoff N i ΛR h').obj A') := by
  cases hx
  cases hy
  cases hA
  rfl

private theorem appendChart_heq (ν : List I) (i : I) {x y : X}
    (hx : x = PowerWordWeight.wordWeight D ΛR ν)
    (hy : y = PowerWordWeight.wordWeight D ΛR (ν ++ [i])) (h : x + D.α i = y)
    (A : ELVWeightProduct D Sc cutoff N ΛR x)
    (hA : HEq A ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R))
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR x ν)
    (he : HEq e.hom (chart D Sc m cutoff L ΛP ΛR ν).hom) :
    HEq (((elvE D Sc cutoff N i ΛR h).toFunctor.mapIso e ≪≫
      PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR ν i x y hx hy h).hom)
      (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom := by
  cases hx
  cases hy
  cases hA
  have heq : e = chart D Sc m cutoff L ΛP ΛR ν := Iso.ext (eq_of_heq he)
  subst e
  have hd : (((elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).toFunctor.mapIso
      (chart D Sc m cutoff L ΛP ΛR ν) ≪≫ PowerWordWeight.weightAppendIso D Sc cutoff L ΛR ν i).hom) =
      (dotChart D Sc m cutoff L ΛP ΛR ν i).hom := by
    simp only [chart, dotChart, PowerWordEvaluation.appendChart, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  exact (heq_of_eq hd).trans (chart_append_heq D Sc m cutoff L ΛP ΛR ν i).symm

/-- Intermediate transport lemma. Its base comparisons are supplied by
whole-word and global-chart identities in the final context statements. -/
private theorem contextChart_heq (ν η : List I) (x : X)
    (hx : x = PowerWordWeight.wordWeight D ΛR ν)
    (A : ELVWeightProduct D Sc cutoff N ΛR x)
    (hA : HEq A ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R))
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR x ν)
    (he : HEq e.hom (chart D Sc m cutoff L ΛP ΛR ν).hom) :
    HEq (PowerWordWeightContexts.contextChart D Sc cutoff L ΛR ν η x hx e).hom
      (chart D Sc m cutoff L ΛP ΛR (PowerWordContexts.extendedWord ν η)).hom := by
  induction η generalizing ν x with
  | nil =>
    cases hx
    cases hA
    have heq : e = chart D Sc m cutoff L ΛP ΛR ν := Iso.ext (eq_of_heq he)
    subst e
    simp only [PowerWordWeightContexts.contextChart, PowerWordWeightContexts.contextFunctor,
      PowerWordWeightContexts.contextIso, Functor.mapIso_hom, Functor.id_map, Iso.trans_hom,
      Iso.refl_hom, Category.comp_id, PowerWordContexts.extendedWord]
    rfl
  | cons i η ih =>
    cases hx
    cases hA
    have heq : e = chart D Sc m cutoff L ΛP ΛR ν := Iso.ext (eq_of_heq he)
    subst e
    let y := PowerWordWeight.wordWeight D ΛR ν + D.α i
    have hy : y = PowerWordWeight.wordWeight D ΛR (ν ++ [i]) :=
      PowerWordWeight.wordWeight_append D ΛR ν i
    let A' := (elvE D Sc cutoff N i ΛR (rfl : PowerWordWeight.wordWeight D ΛR ν + D.α i = y)).obj
      ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R)
    have hA' : HEq A' ((wordHom D Sc m cutoff L ΛP ΛR (ν ++ [i])).obj R) :=
      (postValue_heq D Sc cutoff L ΛR i rfl hy rfl
        (PowerWordWeight.wordWeight_append D ΛR ν i) (HEq.rfl : HEq
          ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R) _)).trans
            (heq_of_eq (congrArg (fun F => F.obj R) (wordHom_append D Sc m cutoff L ΛP ΛR ν i)).symm)
    let e' := (elvE D Sc cutoff N i ΛR (rfl : PowerWordWeight.wordWeight D ΛR ν + D.α i = y)).toFunctor.mapIso
      (chart D Sc m cutoff L ΛP ΛR ν) ≪≫
        PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR ν i _ y rfl hy rfl
    have he' : HEq e'.hom (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom :=
      appendChart_heq D Sc m cutoff L ΛP ΛR ν i rfl hy rfl _ HEq.rfl _ HEq.rfl
    have hc : (PowerWordWeightContexts.contextChart D Sc cutoff L ΛR ν (i :: η) _ rfl
        (chart D Sc m cutoff L ΛP ΛR ν)).hom =
        (PowerWordWeightContexts.contextChart D Sc cutoff L ΛR (ν ++ [i]) η y hy e').hom := by
      simp only [PowerWordWeightContexts.contextChart, PowerWordWeightContexts.contextFunctor,
        PowerWordWeightContexts.contextIso, e', Iso.trans_hom, Functor.mapIso_hom,
        Functor.comp_map, Functor.map_comp, Category.assoc]
      rfl
    exact (heq_of_eq hc).trans (ih (ν ++ [i]) y hy A' hA' e' he')

private theorem chart_word_heq {ν ρ : List I} (h : ν = ρ) :
    HEq (chart D Sc m cutoff L ΛP ΛR ν).hom (chart D Sc m cutoff L ΛP ΛR ρ).hom := by
  cases h
  rfl

/-- The given local dot chart in every outer context is the single global
chart of its concatenated word. No comparison premise is supplied. -/
theorem dotContextChart_global_heq (ν η : List I) (i : I) :
    HEq (TensorHomContexts.dotChart D Sc m cutoff L ΛP ΛR ν η i).hom
      (chart D Sc m cutoff L ΛP ΛR ((ν ++ [i]) ++ η)).hom := by
  have hA := heq_of_eq (congrArg (fun F => F.obj R) (wordHom_append D Sc m cutoff L ΛP ΛR ν i)).symm
  exact (contextChart_heq D Sc m cutoff L ΛP ΛR (ν ++ [i]) η _ rfl _ hA
      (dotChart D Sc m cutoff L ΛP ΛR ν i) (chart_append_heq D Sc m cutoff L ΛP ΛR ν i).symm).trans
    (chart_word_heq D Sc m cutoff L ΛP ΛR (PowerWordContexts.extendedWord_eq (ν ++ [i]) η))

/-- The given local pair chart in every outer context is the single global
chart, including equal and distinct colours and all original intermediate weights. -/
theorem pairContextChart_global_heq (ν η : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    HEq (TensorHomContexts.pairChart D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂).hom
      (chart D Sc m cutoff L ΛP ΛR (((ν ++ [j]) ++ [i]) ++ η)).hom := by
  have hxj : xj = PowerWordWeight.wordWeight D ΛR (ν ++ [j]) :=
    h₁.symm.trans (PowerWordWeight.wordWeight_append D ΛR ν j)
  have hxu : xu = PowerWordWeight.wordWeight D ΛR ((ν ++ [j]) ++ [i]) :=
    h₂.symm.trans ((congrArg (fun x => x + D.α i) hxj).trans
      (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i))
  cases hxj
  cases hxu
  have hA := heq_of_eq (congrArg (fun F => F.obj R) (wordHom_pair D Sc m cutoff L ΛP ΛR ν i j)).symm
  exact (contextChart_heq D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i]) η _ rfl _ hA
      (pairChart D Sc m cutoff L ΛP ΛR ν i j
        (PowerWordWeight.wordWeight_append D ΛR ν j)
        (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i))
      (chart_pair_heq D Sc m cutoff L ΛP ΛR ν i j).symm).trans
    (chart_word_heq D Sc m cutoff L ΛP ΛR
      (PowerWordContexts.extendedWord_eq ((ν ++ [j]) ++ [i]) η))

end OddMath.QuiverHecke.ELVOld.TensorVacuumWords
