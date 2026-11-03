import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum

/-! # Reservoir generators on the tensor-vacuum Hom input

SwappedVacuumCoordinates §§2–6: evaluate the literal reservoir dot and
crossing whiskered by the specified tensor-vacuum Hom. Its checked regular
probe comparison followed by the existing append and pair charts identifies
these maps with the full signed old-Hom word operators. All original-weight
blocks and all coefficient vectors are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorVacuumGenerators
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
end Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "x₀" => ReservoirWord.weight D ΛR 0
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "M" => Superfunctor.obj (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)
  (WeightTensorVacuum.regularProbe D Sc m ΛP)
local notation "e₀" => WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L
local notation "W" => elvRouquierData D Sc cutoff N ΛR

omit [Fintype I] in
private theorem initial_weight : x₀ = PowerWordWeight.wordWeight D ΛR [] := by
  simp [ReservoirWord.weight, PowerWordWeight.wordWeight]

omit [Fintype I] in
private theorem append_weight (i : I) {y : X} (h : x₀ + D.α i = y) :
    y = PowerWordWeight.wordWeight D ΛR [i] :=
  h.symm.trans ((congrArg (fun x => x + D.α i) (initial_weight D ΛR)).trans
    (PowerWordWeight.wordWeight_append D ΛR [] i))

/-- The same selected append chart, preceded by the proved tensor-vacuum
comparison under the given reservoir E. -/
def dotChart (i : I) {y : X} (h : x₀ + D.α i = y) :
    (Z ≫ (W).E i h).obj R ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR y [i] :=
  (elvE D Sc cutoff N i ΛR h).toFunctor.mapIso e₀ ≪≫
    PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR [] i x₀ y
      (initial_weight D ΛR) (append_weight D ΛR i h) h

private theorem append_dot_at (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D ΛR [])
    (hy : y = PowerWordWeight.wordWeight D ΛR [i]) (h : x + D.α i = y) :
    (elvActionDot D Sc cutoff N i ΛR h).app (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L ΛR x []) ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR [] i x y hx hy h).hom =
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR [] i x y hx hy h).hom ≫
        (fun δ => PowerWordWeightDot.wordDotAt D Sc cutoff L [] i δ.1) := by
  cases hx
  cases hy
  exact PowerWordWeightDot.weight_append_dot D Sc cutoff L ΛR [] i

/-- The literal factor dot whiskered by the specified tensor Hom, evaluated
at its actual regular probe, is the signed old-Hom dot on every block. -/
theorem dot (i : I) {y : X} (h : x₀ + D.α i = y) :
    (Z ◁ (W).dot i h).total R ≫ (dotChart D Sc m cutoff L ΛP ΛR i h).hom =
      (dotChart D Sc m cutoff L ΛP ΛR i h).hom ≫
        (fun δ => PowerWordWeightDot.wordDotAt D Sc cutoff L [] i δ.1) := by
  change (elvActionDot D Sc cutoff N i ΛR h).total M ≫ _ = _
  rw [supernatural_total_of_mem (elvActionDot_mem D Sc cutoff N i ΛR h) M]
  exact square_comp
    ((elvE D Sc cutoff N i ΛR h).toFunctor.mapIso e₀)
    (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR [] i x₀ y
      (initial_weight D ΛR) (append_weight D ΛR i h) h) _ _ _
    (natural_even _ _ (elvActionDot D Sc cutoff N i ΛR h) e₀
      (WeightTensorVacuum.regularIso_hom_mem D Sc m cutoff N ΛP ΛR _) (D.parity i))
    (append_dot_at D Sc cutoff L ΛR i x₀ y (initial_weight D ΛR) (append_weight D ΛR i h) h)

/-- The unchanged recursive pair chart, preceded by the checked tensor
comparison under the two literal reservoir E functors. -/
def pairChart (i j : I) {xj xu : X}
    (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu) :
    (Z ≫ (W).E j h₁ ≫ (W).E i h₂).obj R ≅
      PowerWordWeight.wordFamily D Sc cutoff L ΛR xu [j, i] :=
  (elvEFunctor D Sc cutoff N j ΛR h₁ ⋙ elvEFunctor D Sc cutoff N i ΛR h₂).mapIso e₀ ≪≫
    PowerWordWeightCross.recursivePairIso D Sc cutoff L ΛR [] i j (initial_weight D ΛR) h₁ h₂

/-- The literal factor crossing on the tensor Hom agrees with the existing
signed old-Hom crossing in the same selected pair charts. Both colour cases
and every full-coefficient vector are included. -/
theorem cross (i j : I) {xj xu xi : X}
    (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu) :
    (Z ◁ (W).cross i j h₁ h₂ h₃ h₄).total R ≫
      (pairChart D Sc m cutoff L ΛP ΛR j i h₃ h₄).hom =
    (pairChart D Sc m cutoff L ΛP ΛR i j h₁ h₂).hom ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L ΛR [] i j (xu := xu) := by
  change (elvActionCross D Sc cutoff N i j ΛR h₁ h₂ h₃ h₄).total M ≫ _ = _
  rw [supernatural_total_of_mem (elvActionCross_mem D Sc cutoff N i j ΛR h₁ h₂ h₃ h₄) M]
  exact cross_comp
    ((elvEFunctor D Sc cutoff N j ΛR h₁ ⋙ elvEFunctor D Sc cutoff N i ΛR h₂).mapIso e₀)
    ((elvEFunctor D Sc cutoff N i ΛR h₃ ⋙ elvEFunctor D Sc cutoff N j ΛR h₄).mapIso e₀)
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L ΛR [] i j (initial_weight D ΛR) h₁ h₂)
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L ΛR [] j i (initial_weight D ΛR) h₃ h₄) _ _ _
    (natural_even _ _ (elvActionCross D Sc cutoff N i j ΛR h₁ h₂ h₃ h₄) e₀
      (WeightTensorVacuum.regularIso_hom_mem D Sc m cutoff N ΛP ΛR _) (D.parity i * D.parity j))
    (PowerWordPairCoherence.recursive_pair_cross D Sc cutoff L ΛR [] i j
      (initial_weight D ΛR) h₁ h₂ h₃ h₄)

/-- The dot identity on an arbitrary vector of an arbitrary original-weight block. -/
theorem dot_apply (i : I) {y : X} (h : x₀ + D.α i = y)
    (β : WeightBlocks D ΛR y) (c : ContentCategory D Sc cutoff N β.1)
    (z : (((Z ≫ (W).E i h).obj R) β).obj c) :
    (((dotChart D Sc m cutoff L ΛP ΛR i h).hom β).total c)
      ((((Z ◁ (W).dot i h).total R) β).total c z) =
    (PowerWordWeightDot.wordDotAt D Sc cutoff L [] i β.1).total c
      (((dotChart D Sc m cutoff L ΛP ΛR i h).hom β).total c z) := by
  have hs := congrArg (fun f => (f β).total c) (dot D Sc m cutoff L ΛP ΛR i h)
  change ((((Z ◁ (W).dot i h).total R) β) ≫
      (dotChart D Sc m cutoff L ΛP ΛR i h).hom β).total c =
    ((dotChart D Sc m cutoff L ΛP ΛR i h).hom β ≫
      PowerWordWeightDot.wordDotAt D Sc cutoff L [] i β.1).total c at hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at hs
  exact congrArg (fun f => f z) hs

/-- The crossing identity on every vector, with its distinct source and target words. -/
theorem cross_apply (i j : I) {xj xu xi : X}
    (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
    (β : WeightBlocks D ΛR xu) (c : ContentCategory D Sc cutoff N β.1)
    (z : (((Z ≫ (W).E j h₁ ≫ (W).E i h₂).obj R) β).obj c) :
    (((pairChart D Sc m cutoff L ΛP ΛR j i h₃ h₄).hom β).total c)
      ((((Z ◁ (W).cross i j h₁ h₂ h₃ h₄).total R) β).total c z) =
    (PowerWordWeightCross.wordFamilyCross D Sc cutoff L ΛR [] i j (xu := xu) β).total c
      (((pairChart D Sc m cutoff L ΛP ΛR i j h₁ h₂).hom β).total c z) := by
  have hs := congrArg (fun f => (f β).total c) (cross D Sc m cutoff L ΛP ΛR i j h₁ h₂ h₃ h₄)
  change ((((Z ◁ (W).cross i j h₁ h₂ h₃ h₄).total R) β) ≫
      (pairChart D Sc m cutoff L ΛP ΛR j i h₃ h₄).hom β).total c =
    ((pairChart D Sc m cutoff L ΛP ΛR i j h₁ h₂).hom β ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L ΛR [] i j (xu := xu) β).total c at hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at hs
  exact congrArg (fun f => f z) hs

end OddMath.QuiverHecke.ELVOld.TensorVacuumGenerators
