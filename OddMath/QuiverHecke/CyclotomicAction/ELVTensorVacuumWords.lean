import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates

/-! # Word contexts on the tensor-vacuum Hom

SwappedVacuumCoordinates §§2–6: postcompose the specified tensor Hom by
arbitrary words of the given reservoir E functors. The same selected native
word charts identify its literal whiskered dot and crossing on every vector,
and give the existing full old-Hom coordinates on these actual Hom values.
Words here are reservoir append tuples: the source strand word is reversed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorVacuumWords
open CyclotomicAction SwappedAssembly
universe u

section Generic
variable {k : Type u} [CommRing k] {C : Type*} [Category* C]
private theorem square_comp {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (x : A ⟶ A) (y : B ⟶ B) (z : E ⟶ E)
    (he : x ≫ e.hom = e.hom ≫ y) (hf : y ≫ f.hom = f.hom ≫ z) :
    x ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, he, Category.assoc, hf]
private theorem cross_comp {A B E F S T : C} (e : A ≅ B) (f : E ≅ F)
    (s : B ≅ S) (t : F ≅ T) (x : A ⟶ E) (y : B ⟶ F) (z : S ⟶ T)
    (hn : x ≫ f.hom = e.hom ≫ y) (hc : y ≫ t.hom = s.hom ≫ z) :
    x ≫ (f ≪≫ t).hom = (e ≪≫ s).hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc, hc]
private theorem natural_even {A E : Type*} [Category* A] [Preadditive A]
    [Linear k A] [Supercategory k A] [Category* E] [Preadditive E]
    [Linear k E] [Supercategory k E]
    (F G : A ⥤ E) (a : SuperNatTrans k F G) {X Y : A} (e : X ≅ Y)
    (he : e.hom ∈ parity (R := k) _ _ 0) (p : ZMod 2) :
    a.app p X ≫ G.map e.hom = F.map e.hom ≫ a.app p Y := by
  simpa only [koszulSign_zero_right, one_smul] using (a.naturality p e.hom he).symm
variable [Preadditive C] [Linear k C] [Supercategory k C]
private theorem even_comp {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (he : e.hom ∈ parity (R := k) _ _ 0) (hf : f.hom ∈ parity (R := k) _ _ 0) :
    (e ≪≫ f).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [Iso.trans_hom, zero_add] using comp_mem he hf
end Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P₀" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff N ΛR

private def reindexHom {x y : X} (h : x = y)
    (Z : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x) :
    probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR y := h ▸ Z

private def reindexIso {x y : X} (h : x = y)
    (Z : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (e : Z.obj P₀ ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR x []) :
    (reindexHom D Sc m cutoff L ΛP ΛR h Z).obj P₀ ≅
      PowerWordWeight.wordFamily D Sc cutoff L ΛR y [] := by
  cases h
  exact e

private theorem reindexIso_even {x y : X} (h : x = y)
    (Z : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (e : Z.obj P₀ ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR x [])
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (reindexIso D Sc m cutoff L ΛP ΛR h Z e).hom ∈ parity (R := k) _ _ 0 := by
  cases h
  exact he

omit [Fintype I] in
private theorem initial_weight :
    ReservoirWord.weight D ΛR 0 = PowerWordWeight.wordWeight D ΛR [] := by
  simp [ReservoirWord.weight, PowerWordWeight.wordWeight]

private def initialHom : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
    elvWeightSpace D Sc cutoff N ΛR (PowerWordWeight.wordWeight D ΛR []) :=
  reindexHom D Sc m cutoff L ΛP ΛR (initial_weight D ΛR)
    (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)

private def initialIso : (initialHom D Sc m cutoff L ΛP ΛR).obj P₀ ≅
    PowerWordEvaluation.value D Sc cutoff L ΛR [] :=
  reindexIso D Sc m cutoff L ΛP ΛR (initial_weight D ΛR)
    (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)
    (WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L) ≪≫
      (eqToIso (PowerWordEvaluation.value_nil D Sc cutoff L ΛR)).symm

private theorem initialIso_even :
    (initialIso D Sc m cutoff L ΛP ΛR).hom ∈ parity (R := k) _ _ 0 :=
  even_comp _ _
    (reindexIso_even D Sc m cutoff L ΛP ΛR (initial_weight D ΛR)
      (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)
      (WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L)
      (WeightTensorVacuum.regularIso_hom_mem D Sc m cutoff N ΛP ΛR _))
    (eqToHom_mem_parity_zero (PowerWordEvaluation.value_nil D Sc cutoff L ΛR).symm)

/-- Literal successive reservoir postcomposition of the selected tensor Hom.
Only the empty-weight equality is normalized; the original weight group is unchanged. -/
def wordHom (ν : List I) : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
    elvWeightSpace D Sc cutoff N ΛR (PowerWordWeight.wordWeight D ΛR ν) :=
  ν.reverseRecOn (initialHom D Sc m cutoff L ΛP ΛR)
    (fun ρ i Z => Z ≫ (W).E i (PowerWordWeight.wordWeight_append D ΛR ρ i))

private theorem wordHom_nil : wordHom D Sc m cutoff L ΛP ΛR [] =
    initialHom D Sc m cutoff L ΛP ΛR := by
  simp only [wordHom, List.reverseRecOn_nil]

private theorem wordValue_nil : (wordHom D Sc m cutoff L ΛP ΛR []).obj P₀ =
    (initialHom D Sc m cutoff L ΛP ΛR).obj P₀ := by
  rw [wordHom_nil]

theorem wordHom_append (ν : List I) (i : I) :
    wordHom D Sc m cutoff L ΛP ΛR (ν ++ [i]) =
      wordHom D Sc m cutoff L ΛP ΛR ν ≫
        (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) := by
  simp only [wordHom, List.reverseRecOn_concat]

private theorem wordValue_append (ν : List I) (i : I) :
    (wordHom D Sc m cutoff L ΛP ΛR (ν ++ [i])).obj P₀ =
      (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).obj
        ((wordHom D Sc m cutoff L ΛP ΛR ν).obj P₀) := by
  rw [wordHom_append]
  rfl

/-- The evaluated tensor Hom word and the selected native E-word value,
using the original regular-probe comparison under the same E functors. -/
def valueIso (ν : List I) : (wordHom D Sc m cutoff L ΛP ΛR ν).obj P₀ ≅
    PowerWordEvaluation.value D Sc cutoff L ΛR ν :=
  ν.reverseRecOn
    (eqToIso (wordValue_nil D Sc m cutoff L ΛP ΛR) ≪≫ initialIso D Sc m cutoff L ΛP ΛR)
    (fun ρ i e =>
    eqToIso (wordValue_append D Sc m cutoff L ΛP ΛR ρ i) ≪≫
      (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ρ i)).toFunctor.mapIso e ≪≫
        (eqToIso (PowerWordEvaluation.value_append D Sc cutoff L ΛR ρ i)).symm)

private theorem valueIso_append (ν : List I) (i : I) :
    valueIso D Sc m cutoff L ΛP ΛR (ν ++ [i]) =
      eqToIso (wordValue_append D Sc m cutoff L ΛP ΛR ν i) ≪≫
        (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).toFunctor.mapIso
          (valueIso D Sc m cutoff L ΛP ΛR ν) ≪≫
        (eqToIso (PowerWordEvaluation.value_append D Sc cutoff L ΛR ν i)).symm := by
  simp only [valueIso, List.reverseRecOn_concat]

theorem valueIso_even (ν : List I) :
    (valueIso D Sc m cutoff L ΛP ΛR ν).hom ∈ parity (R := k) _ _ 0 := by
  induction ν using List.reverseRecOn with
  | nil =>
    simpa only [valueIso, List.reverseRecOn_nil] using even_comp
      (eqToIso (wordValue_nil D Sc m cutoff L ΛP ΛR)) (initialIso D Sc m cutoff L ΛP ΛR)
      (eqToHom_mem_parity_zero (wordValue_nil D Sc m cutoff L ΛP ΛR))
      (initialIso_even D Sc m cutoff L ΛP ΛR)
  | append_singleton ν i ih =>
    rw [valueIso_append]
    exact even_comp _ _ (eqToHom_mem_parity_zero (wordValue_append D Sc m cutoff L ΛP ΛR ν i))
      (even_comp _ _ (IsSuperfunctor.map_mem (F :=
        (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).toFunctor) ih)
        (eqToHom_mem_parity_zero (PowerWordEvaluation.value_append D Sc cutoff L ΛR ν i).symm))

/-- The unchanged selected full word chart on the evaluated tensor Hom word. -/
def chart (ν : List I) : (wordHom D Sc m cutoff L ΛP ΛR ν).obj P₀ ≅
    PowerWordWeight.wordFamily D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR ν) ν :=
  valueIso D Sc m cutoff L ΛP ΛR ν ≪≫ PowerWordEvaluation.chart D Sc cutoff L ΛR ν

theorem chart_even (ν : List I) :
    (chart D Sc m cutoff L ΛP ΛR ν).hom ∈ parity (R := k) _ _ 0 :=
  even_comp _ _ (valueIso_even D Sc m cutoff L ΛP ΛR ν)
    (PowerWordEvaluation.chart_even D Sc cutoff L ΛR ν)

/-- The append chart in an arbitrary tensor-Hom word context. -/
def dotChart (ν : List I) (i : I) :
    (wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i)).obj P₀ ≅
    PowerWordWeight.wordFamily D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) (ν ++ [i]) :=
  (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).toFunctor.mapIso
    (valueIso D Sc m cutoff L ΛP ΛR ν) ≪≫ PowerWordEvaluation.appendChart D Sc cutoff L ΛR ν i

/-- The pair chart in an arbitrary tensor-Hom word context. -/
def pairChart (ν : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    (wordHom D Sc m cutoff L ΛP ΛR ν ≫ (W).E j h₁ ≫ (W).E i h₂).obj P₀ ≅
      PowerWordWeight.wordFamily D Sc cutoff L ΛR xu ((ν ++ [j]) ++ [i]) :=
  (elvEFunctor D Sc cutoff N j ΛR h₁ ⋙ elvEFunctor D Sc cutoff N i ΛR h₂).mapIso
    (valueIso D Sc m cutoff L ΛP ΛR ν) ≪≫ PowerWordEvaluation.pairChart D Sc cutoff L ΛR ν i j h₁ h₂

/-- The literal whiskered reservoir dot in every word context. -/
theorem dot (ν : List I) (i : I) :
    (wordHom D Sc m cutoff L ΛP ΛR ν ◁
      (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)).total P₀ ≫
      (dotChart D Sc m cutoff L ΛP ΛR ν i).hom =
    (dotChart D Sc m cutoff L ΛP ΛR ν i).hom ≫
      PowerWordWeightDot.wordFamilyDot D Sc cutoff L ΛR ν i := by
  change (elvActionDot D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).total
    ((wordHom D Sc m cutoff L ΛP ΛR ν).obj P₀) ≫ _ = _
  rw [supernatural_total_of_mem (elvActionDot_mem D Sc cutoff N i ΛR
    (PowerWordWeight.wordWeight_append D ΛR ν i)) _]
  exact square_comp _ _ _ _ _
    (natural_even _ _ (elvActionDot D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i))
      (valueIso D Sc m cutoff L ΛP ΛR ν) (valueIso_even D Sc m cutoff L ΛP ΛR ν) (D.parity i))
    (PowerWordEvaluation.dot_append_value D Sc cutoff L ΛR ν i)

/-- The literal whiskered reservoir crossing in every word context,
including equal and distinct colours and all original intermediate weights. -/
theorem cross (ν : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu) :
    (wordHom D Sc m cutoff L ΛP ΛR ν ◁ (W).cross i j h₁ h₂ h₃ h₄).total P₀ ≫
      (pairChart D Sc m cutoff L ΛP ΛR ν j i h₃ h₄).hom =
    (pairChart D Sc m cutoff L ΛP ΛR ν i j h₁ h₂).hom ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L ΛR ν i j (xu := xu) := by
  change (elvActionCross D Sc cutoff N i j ΛR h₁ h₂ h₃ h₄).total
    ((wordHom D Sc m cutoff L ΛP ΛR ν).obj P₀) ≫ _ = _
  rw [supernatural_total_of_mem (elvActionCross_mem D Sc cutoff N i j ΛR h₁ h₂ h₃ h₄) _]
  exact cross_comp _ _ _ _ _ _ _
    (natural_even _ _ (elvActionCross D Sc cutoff N i j ΛR h₁ h₂ h₃ h₄)
      (valueIso D Sc m cutoff L ΛP ΛR ν) (valueIso_even D Sc m cutoff L ΛP ΛR ν)
      (D.parity i * D.parity j))
    (PowerWordEvaluation.cross_pair_value D Sc cutoff L ΛR ν i j h₁ h₂ h₃ h₄)

/-- Whole Hom coordinates for the tensor-Hom word value, retaining the
same-weight target word family and the existing selected native coordinates. -/
def homEquiv (ν τ : List I) :
    ((wordHom D Sc m cutoff L ΛP ΛR ν).obj P₀ ⟶
      PowerWordWeight.wordFamily D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR ν) τ) ≃ₗ[k]
    (PowerWordWeight.wordAt D Sc cutoff L τ (ν : Multiset I)).obj
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl) :=
  (Linear.homCongr k (valueIso D Sc m cutoff L ΛP ΛR ν) (Iso.refl _)).trans
    (PowerWordHomCoordinates.homEquiv D Sc cutoff L ΛR ν τ)

/-- The dot identity on every vector of every full original-weight block. -/
theorem dot_apply (ν : List I) (i : I)
    (β : WeightBlocks D ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])))
    (c : ContentCategory D Sc cutoff N β.1)
    (z : (((wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i)).obj P₀) β).obj c) :
    (((dotChart D Sc m cutoff L ΛP ΛR ν i).hom β).total c)
      ((((wordHom D Sc m cutoff L ΛP ΛR ν ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)).total P₀) β).total c z) =
    (PowerWordWeightDot.wordFamilyDot D Sc cutoff L ΛR ν i β).total c
      (((dotChart D Sc m cutoff L ΛP ΛR ν i).hom β).total c z) := by
  have hs := congrArg (fun f => (f β).total c) (dot D Sc m cutoff L ΛP ΛR ν i)
  change ((((wordHom D Sc m cutoff L ΛP ΛR ν ◁
      (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)).total P₀) β) ≫
      (dotChart D Sc m cutoff L ΛP ΛR ν i).hom β).total c =
    ((dotChart D Sc m cutoff L ΛP ΛR ν i).hom β ≫
      PowerWordWeightDot.wordFamilyDot D Sc cutoff L ΛR ν i β).total c at hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at hs
  exact congrArg (fun f => f z) hs

/-- The crossing identity on every vector in an arbitrary word context. -/
theorem cross_apply (ν : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu)
    (β : WeightBlocks D ΛR xu) (c : ContentCategory D Sc cutoff N β.1)
    (z : (((wordHom D Sc m cutoff L ΛP ΛR ν ≫ (W).E j h₁ ≫ (W).E i h₂).obj P₀) β).obj c) :
    (((pairChart D Sc m cutoff L ΛP ΛR ν j i h₃ h₄).hom β).total c)
      ((((wordHom D Sc m cutoff L ΛP ΛR ν ◁ (W).cross i j h₁ h₂ h₃ h₄).total P₀) β).total c z) =
    (PowerWordWeightCross.wordFamilyCross D Sc cutoff L ΛR ν i j (xu := xu) β).total c
      (((pairChart D Sc m cutoff L ΛP ΛR ν i j h₁ h₂).hom β).total c z) := by
  have hs := congrArg (fun f => (f β).total c) (cross D Sc m cutoff L ΛP ΛR ν i j h₁ h₂ h₃ h₄)
  change ((((wordHom D Sc m cutoff L ΛP ΛR ν ◁ (W).cross i j h₁ h₂ h₃ h₄).total P₀) β) ≫
      (pairChart D Sc m cutoff L ΛP ΛR ν j i h₃ h₄).hom β).total c =
    ((pairChart D Sc m cutoff L ΛP ΛR ν i j h₁ h₂).hom β ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L ΛR ν i j (xu := xu) β).total c at hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at hs
  exact congrArg (fun f => f z) hs

end OddMath.QuiverHecke.ELVOld.TensorVacuumWords
