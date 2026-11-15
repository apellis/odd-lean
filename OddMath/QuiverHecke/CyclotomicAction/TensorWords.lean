import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords

/-!
# Tensor words

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

/-! # Tensor-vacuum Homs along the given reservoir words

SwappedVacuumCoordinates §§2–6: identify the entire selected tensor Hom
postcomposed by the actual reservoir path word with the chosen append
word Hom. The original weight equality is proved, and labels are reversed.
This is a comparison of whole functors, not only their regular-probe value.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorReservoirWords
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => elvRouquierData D Sc cutoff N ΛR
local notation "R₀" => WeightTensorVacuum.regularProbe D Sc m ΛP

private def atWeight {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x) :
    probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR y := h ▸ F

private theorem atWeight_heq {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x) :
    HEq (atWeight D Sc m cutoff L ΛP ΛR h F) F := by
  subst y
  rfl

omit [Fintype I] in
private theorem initial_weight : ReservoirWord.weight D ΛR 0 = PowerWordWeight.wordWeight D ΛR [] := by
  simp [ReservoirWord.weight, PowerWordWeight.wordWeight]

omit [Fintype I] in
private theorem edge (i : I) (c : I →₀ ℕ) (hc : 1 ≤ c i) :
    ReservoirWord.weight D ΛR (c - Finsupp.single i 1) + D.α i = ReservoirWord.weight D ΛR c := by
  simp only [ReservoirWord.weight]
  rw [add_assoc, contentWeight_sub_single hc]

private theorem postE_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    {F' : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x'}
    (hF : HEq F F') : HEq (F ≫ (W).E i h) (F' ≫ (W).E i h') := by
  cases hx
  cases hy
  cases hF
  rfl

private theorem wordHom_word_heq {ν τ : List I} (h : ν = τ) :
    HEq (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR τ) := by
  subst τ
  rfl

/-- Postcompose the actual selected tensor-vacuum Hom by the given
reservoir path word, retaining its original formal-content weight. -/
def pathHom {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c) :=
  WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫ ReservoirWord.word (W) ΛR p hl

private theorem comparison {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR ((l.map (fun a => a.l.2)).reverse) ∧
    HEq (pathHom D Sc m cutoff L ΛP ΛR p hl)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ((l.map (fun a => a.l.2)).reverse)) := by
  induction l generalizing c with
  | nil =>
    cases p
    refine ⟨initial_weight D ΛR, ?_⟩
    change HEq (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫
      ReservoirWord.word (W) ΛR (SPath.nil (0,0)) hl)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR [])
    rw [ReservoirWord.word_nil]
    apply (heq_of_eq (show WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫
      (𝟙 (elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0))) =
        WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L from rfl)).trans
    unfold TensorVacuumWords.wordHom
    simp only [List.reverseRecOn_nil]
    change HEq (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)
      (atWeight D Sc m cutoff L ΛP ΛR (initial_weight D ΛR)
        (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L))
    exact (atWeight_heq D Sc m cutoff L ΛP ΛR (initial_weight D ΛR) _).symm
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b,i⟩,r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        change SPath l (0,c - Finsupp.single i 1) (0,0) at p
        have hp := ih p ht
        have hci : 1 ≤ c i := hv
        have hy : ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR
            (((l.map (fun a => a.l.2)).reverse) ++ [i]) :=
          (edge D ΛR i c hci).symm.trans ((congrArg (fun x => x + D.α i) hp.1).trans
            (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun a => a.l.2)).reverse) i))
        refine ⟨by simpa only [List.map_cons, List.reverse_cons] using hy, ?_⟩
        have hc : pathHom D Sc m cutoff L ΛP ΛR
            (SPath.cons ⟨(true,i),r⟩ false (0,c) hci p) hl =
            pathHom D Sc m cutoff L ΛP ΛR p ht ≫ (W).E i (edge D ΛR i c hci) :=
          congrArg (fun (F : elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0) ⟶
              elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c)) =>
            WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L ≫ F)
              (ReservoirWord.word_cons (W) ΛR i r hci p ht)
        have hwords : ((l.map (fun a => a.l.2)).reverse) ++ [i] =
            (((⟨(true,i),r⟩ :: l).map (fun a => a.l.2)).reverse) := by
          rw [List.map_cons, List.reverse_cons]
        have hpost := postE_heq D Sc m cutoff L ΛP ΛR i hp.1 hy (edge D ΛR i c hci)
          (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun a => a.l.2)).reverse) i) hp.2
        have happ := heq_of_eq (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR
          ((l.map (fun a => a.l.2)).reverse) i).symm
        have hlist := wordHom_word_heq D Sc m cutoff L ΛP ΛR hwords
        exact (heq_of_eq hc).trans (hpost.trans (happ.trans hlist))

omit [Fintype I] in
/-- The actual endpoint weight is the unchanged original weight of the
reversed labelled colour word. -/
theorem path_weight {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR ((l.map (fun a => a.l.2)).reverse) := by
  induction l generalizing c with
  | nil => cases p; exact initial_weight D ΛR
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b,i⟩,r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        have hy := (edge D ΛR i c hv).symm.trans ((congrArg (fun x => x + D.α i) (ih p ht)).trans
          (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun a => a.l.2)).reverse) i))
        simpa only [List.map_cons, List.reverse_cons] using hy

/-- The entire postcomposed tensor Hom is the chosen reversed append Hom,
with only its proved original-weight endpoint presentation changed. -/
theorem pathHom_heq {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    HEq (pathHom D Sc m cutoff L ΛP ΛR p hl)
      (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ((l.map (fun a => a.l.2)).reverse)) :=
  (comparison D Sc m cutoff L ΛP ΛR p hl).2

/-- The literal reservoir postcomposition at the proved reversed-word weight. -/
def pathHomAt {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR
      (PowerWordWeight.wordWeight D ΛR ((l.map (fun a => a.l.2)).reverse)) :=
  atWeight D Sc m cutoff L ΛP ΛR (path_weight D ΛR p hl)
    (pathHom D Sc m cutoff L ΛP ΛR p hl)

/-- Equality of whole chosen functors, not an agreement only on a probe
vector or on the coefficient vacuum. -/
theorem pathHomAt_eq_wordHom {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    pathHomAt D Sc m cutoff L ΛP ΛR p hl =
      TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ((l.map (fun a => a.l.2)).reverse) :=
  eq_of_heq ((atWeight_heq D Sc m cutoff L ΛP ΛR _ _).trans
    (pathHom_heq D Sc m cutoff L ΛP ΛR p hl))

end OddMath.QuiverHecke.ELVOld.TensorReservoirWords
end

end

section

/-! # Outer E contexts on surviving tensor-Hom entries

SwappedVacuumCoordinates §§2–6: apply the prescribed outer reservoir E
functors to the literal whiskered dot or crossing, then postcompose an
arbitrary whole Hom entry. The selected context charts give the extended
signed old-Hom arrow on every source vector. No faithfulness is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorHomContexts
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P₀" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff N ΛR

private instance context_additive (x : X) (η : List I) :
    (PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η).Additive := by
  induction η generalizing x with
  | nil => change (𝟭 _).Additive; infer_instance
  | cons i η ih =>
    let := ih (x + D.α i)
    change (elvEFunctor D Sc cutoff N i ΛR rfl ⋙ _).Additive
    infer_instance

private instance context_linear (x : X) (η : List I) :
    (PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η).Linear k := by
  induction η generalizing x with
  | nil => change (𝟭 _).Linear k; infer_instance
  | cons i η ih =>
    let := ih (x + D.α i)
    change (elvEFunctor D Sc cutoff N i ΛR rfl ⋙ _).Linear k
    infer_instance

private instance context_super (x : X) (η : List I) :
    IsSuperfunctor k (PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η) := by
  induction η generalizing x with
  | nil => change IsSuperfunctor k (𝟭 _); infer_instance
  | cons i η ih =>
    let := ih (x + D.α i)
    change IsSuperfunctor k (elvEFunctor D Sc cutoff N i ΛR rfl ⋙ _)
    infer_instance

/-- The already defined context functor, bundled with its given super structure. -/
def context (x : X) (η : List I) : elvWeightSpace D Sc cutoff N ΛR x ⟶
    elvWeightSpace D Sc cutoff N ΛR (PowerWordWeightContexts.contextWeight D x η) :=
  ⟨PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η⟩

private theorem whiskerRight_total {A B C : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (a : F ⟶ G) (K : B ⟶ C) (p : A) :
    (a ▷ K).total p = K.map (a.total p) := by
  change K.map (a.app 0 p) + K.map (a.app 1 p) = K.map (a.app 0 p + a.app 1 p)
  exact (K.toFunctor.map_add).symm

private theorem mapped_square {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {M N₀ S T : A} {U V : B}
    (e : M ≅ S) (f : N₀ ≅ T) (c : F.obj S ≅ U) (d : F.obj T ≅ V)
    (a : M ⟶ N₀) (b : S ⟶ T) (z : U ⟶ V)
    (ha : a ≫ f.hom = e.hom ≫ b) (hb : F.map b ≫ d.hom = c.hom ≫ z) :
    F.map a ≫ (F.mapIso f ≪≫ d).hom = (F.mapIso e ≪≫ c).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, ha, F.map_comp, Category.assoc, hb]

/-- The same append chart followed by the existing outer context chart. -/
def dotChart (ν η : List I) (i : I) :
    (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η).obj P₀ ≅
    PowerWordWeight.wordFamily D Sc cutoff L ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
      (PowerWordContexts.extendedWord (ν ++ [i]) η) :=
  PowerWordWeightContexts.contextChart D Sc cutoff L ΛR (ν ++ [i]) η _ rfl
    (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i)

omit [Fintype I] in
private theorem pair_weight (ν : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    xu = PowerWordWeight.wordWeight D ΛR ((ν ++ [j]) ++ [i]) :=
  h₂.symm.trans ((congrArg (fun x => x + D.α i)
    (h₁.symm.trans (PowerWordWeight.wordWeight_append D ΛR ν j))).trans
      (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i))

/-- The same pair chart followed by the existing outer context chart. -/
def pairChart (ν η : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫ (W).E j h₁ ≫ (W).E i h₂ ≫
      context D Sc cutoff L ΛR xu η).obj P₀ ≅
    PowerWordWeight.wordFamily D Sc cutoff L ΛR (PowerWordWeightContexts.contextWeight D xu η)
      (PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η) :=
  PowerWordWeightContexts.contextChart D Sc cutoff L ΛR ((ν ++ [j]) ++ [i]) η xu
    (pair_weight D ΛR ν i j h₁ h₂) (TensorVacuumWords.pairChart D Sc m cutoff L ΛP ΛR ν i j h₁ h₂)

/-- The literal whiskered dot under an arbitrary outer E-word context. -/
theorem dot (ν η : List I) (i : I) :
    ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
      (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)) ▷
      context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η).total P₀ ≫
      (dotChart D Sc m cutoff L ΛP ΛR ν η i).hom =
    (dotChart D Sc m cutoff L ΛP ΛR ν η i).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
        (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
        (PowerWordContexts.extendedWord (ν ++ [i]) η) (PowerWordContexts.extendedWord (ν ++ [i]) η)
        (PowerWordContexts.extendedArrow D Sc cutoff (ν ++ [i]) (ν ++ [i]) η
          (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))) := by
  rw [whiskerRight_total]
  exact mapped_square _ _ _ _ _ _ _ _
    (TensorVacuumWords.dot D Sc m cutoff L ΛP ΛR ν i)
    (PowerWordWeightContexts.context_family_arrow D Sc cutoff L ΛR (ν ++ [i]) (ν ++ [i]) η _
      rfl rfl rfl (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν)))

/-- The literal crossing under an arbitrary outer E-word context, retaining
the old extended arrow and every actual intermediate original weight. -/
theorem cross (ν η : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu) :
    ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁ (W).cross i j h₁ h₂ h₃ h₄) ▷
      context D Sc cutoff L ΛR xu η).total P₀ ≫ (pairChart D Sc m cutoff L ΛP ΛR ν η j i h₃ h₄).hom =
    (pairChart D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR (PowerWordWeightContexts.contextWeight D xu η)
        (PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η)
        (PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η)
        (PowerWordContexts.extendedArrow D Sc cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
          (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j)) := by
  rw [whiskerRight_total]
  have hst : (((ν ++ [j]) ++ [i] : List I) : Multiset I) = (((ν ++ [i]) ++ [j] : List I) : Multiset I) := by
    rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add]
    ac_rfl
  exact mapped_square _ _ _ _ _ _ _ _
    (TensorVacuumWords.cross D Sc m cutoff L ΛP ΛR ν i j h₁ h₂ h₃ h₄)
    (PowerWordWeightContexts.context_family_arrow D Sc cutoff L ΛR ((ν ++ [j]) ++ [i])
      ((ν ++ [i]) ++ [j]) η xu (pair_weight D ΛR ν i j h₁ h₂) (pair_weight D ΛR ν j i h₃ h₄) hst
      (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j))

private theorem entry_comp {x : X}
    {G Y Z : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    (f : G ⟶ Y) (g : Y ⟶ Z) (β : WeightBlocks D ΛR x)
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((f ≫ g).total P₀) β).total c z =
      ((g.total P₀) β).total c (((f.total P₀) β).total c z) := by
  rw [Superfunctor.comp_total]
  change (((f.total P₀) β ≫ (g.total P₀) β).total c) z = _
  rw [Superfunctor.comp_total, SVec.comp_apply]

private theorem square_apply {x : X}
    {A B C E : ELVWeightProduct D Sc cutoff N ΛR x}
    (a : A ⟶ B) (e : A ⟶ C) (f : B ⟶ E) (b : C ⟶ E)
    (h : a ≫ f = e ≫ b) (β : WeightBlocks D ΛR x)
    (c : ContentCategory D Sc cutoff N β.1) (z : (A β).obj c) :
    (f β).total c ((a β).total c z) = (b β).total c ((e β).total c z) := by
  have hs := congrArg (fun g => (g β).total c) h
  change (a β ≫ f β).total c = (e β ≫ b β).total c at hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at hs
  exact congrArg (fun g => g z) hs

/-- The outer-context dot entry square for arbitrary whole Hom entries
and every source vector. -/
theorem dot_apply (ν η : List I) (i : I)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (f : G ⟶ TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
    (β : WeightBlocks D ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((dotChart D Sc m cutoff L ΛP ΛR ν η i).hom β).total c)
      ((((f ≫ ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)) ▷
        context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)).total P₀) β).total c z) =
    (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
      (PowerWordContexts.extendedWord (ν ++ [i]) η) (PowerWordContexts.extendedWord (ν ++ [i]) η)
      (PowerWordContexts.extendedArrow D Sc cutoff (ν ++ [i]) (ν ++ [i]) η
        (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))) β).total c
      (((dotChart D Sc m cutoff L ΛP ΛR ν η i).hom β).total c (((f.total P₀) β).total c z)) := by
  rw [entry_comp]
  exact square_apply D Sc cutoff L ΛR _ _ _ _
    (dot D Sc m cutoff L ΛP ΛR ν η i) β c (((f.total P₀) β).total c z)

/-- The outer-context crossing entry square, for arbitrary whole input
transformations and every vector, without a faithfulness premise. -/
theorem cross_apply (ν η : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D xu η))
    (f : G ⟶ TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E j h₁ ≫ (W).E i h₂ ≫ context D Sc cutoff L ΛR xu η)
    (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D xu η))
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((pairChart D Sc m cutoff L ΛP ΛR ν η j i h₃ h₄).hom β).total c)
      ((((f ≫ ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
        (W).cross i j h₁ h₂ h₃ h₄) ▷ context D Sc cutoff L ΛR xu η)).total P₀) β).total c z) =
    (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR (PowerWordWeightContexts.contextWeight D xu η)
      (PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η) (PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η)
      (PowerWordContexts.extendedArrow D Sc cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
        (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j)) β).total c
      (((pairChart D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂).hom β).total c (((f.total P₀) β).total c z)) := by
  rw [entry_comp]
  exact square_apply D Sc cutoff L ΛR _ _ _ _
    (cross D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂ h₃ h₄) β c (((f.total P₀) β).total c z)

end OddMath.QuiverHecke.ELVOld.TensorHomContexts
end

end
