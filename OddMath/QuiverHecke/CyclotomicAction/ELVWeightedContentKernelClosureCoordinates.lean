import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedKernelClosureCoordinates

/-! # Weighted kernel closure evaluation at arbitrary stored content

The G8 coefficient attachment retains arbitrary stored content and evaluates
the literal weighted local closure by the truncated raw kernel coefficient.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u v
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

attribute [local irreducible] positiveKernelClosure negativeKernelClosure
  weightedContentUnitClosureValue weightedContentCapClosureValue

private def contentRec
    {P : ∀ β : Multiset I, ContentCategory D Sc cutoff N β → Sort v}
    (h : ∀ l : List I,
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : P β w := by
  rcases w with ⟨t, ht⟩
  cases ht
  exact h t.word

private theorem contentRec_atWord
    {P : ∀ β : Multiset I, ContentCategory D Sc cutoff N β → Sort v}
    (h : ∀ l : List I,
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩)
    (l : List I) :
    contentRec D Sc cutoff N h (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ = h l := rfl

private def unitWordCoefficient (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ) :
    (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ :=
  truncateOld D Sc cutoff N l l
    (positiveKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))

private def capWordCoefficient (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ) :
    (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ :=
  truncateOld D Sc cutoff N l l
    (negativeKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))

/-- The represented source endomorphism for the prescribed unit closure. -/
def weightedContentUnitClosureCoefficient (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) : w.obj ⟶ w.obj :=
  contentRec D Sc cutoff N
    (P := fun β w => (0 ≤ contentCrossingHeight D cutoff i β) → ℕ → ℕ → (w.obj ⟶ w.obj))
    (unitWordCoefficient D Sc cutoff N i) β w hh r s

/-- The represented source endomorphism for the prescribed cap closure. -/
def weightedContentCapClosureCoefficient (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) : w.obj ⟶ w.obj :=
  contentRec D Sc cutoff N
    (P := fun β w => (contentCrossingHeight D cutoff i β ≤ 0) → ℕ → ℕ → (w.obj ⟶ w.obj))
    (capWordCoefficient D Sc cutoff N i) β w hh r s

private theorem unitCoefficient_atWord (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ) :
    weightedContentUnitClosureCoefficient D Sc cutoff N i (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s =
    unitWordCoefficient D Sc cutoff N i l hh r s := by
  exact congrFun (congrFun (congrFun
    (contentRec_atWord D Sc cutoff N
      (P := fun β w => (0 ≤ contentCrossingHeight D cutoff i β) → ℕ → ℕ → (w.obj ⟶ w.obj))
      (unitWordCoefficient D Sc cutoff N i) l) hh) r) s

private theorem capCoefficient_atWord (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ) :
    weightedContentCapClosureCoefficient D Sc cutoff N i (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s =
    capWordCoefficient D Sc cutoff N i l hh r s := by
  exact congrFun (congrFun (congrFun
    (contentRec_atWord D Sc cutoff N
      (P := fun β w => (contentCrossingHeight D cutoff i β ≤ 0) → ℕ → ℕ → (w.obj ⟶ w.obj))
      (capWordCoefficient D Sc cutoff N i) l) hh) r) s

private theorem restriction_map_value (t w : OldCategory D Sc cutoff) (f : t ⟶ w)
    (b : (RM).obj t) :
    (RM).map f b = M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj w)
      ((oldTruncateFunctor D Sc cutoff N).map f) b := rfl
private theorem quotient_map_value (t w : OldCategory D Sc cutoff) (f : t ⟶ w) :
    (oldTruncateFunctor D Sc cutoff N).map f =
      truncateOld D Sc cutoff N t.word w.word f := rfl

private theorem restriction_truncate_value (t w : OldCategory D Sc cutoff) (f : t ⟶ w)
    (b : (RM).obj t) :
    (RM).map f b = M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj w)
      (truncateOld D Sc cutoff N t.word w.word f) b := by
  exact (restriction_map_value D Sc cutoff N M t w f b).trans
    (congrArg (fun a : (oldTruncateFunctor D Sc cutoff N).obj t ⟶
      (oldTruncateFunctor D Sc cutoff N).obj w =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj w) a b)
      (quotient_map_value D Sc cutoff N t w f))

private theorem unit_atWord_raw (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I))
    (r s : ℕ) (b : (RM).obj ⟨l⟩) :
    weightedContentUnitClosureValue D Sc cutoff N i M (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s b =
    M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (unitWordCoefficient D Sc cutoff N i l hh r s) b := by
  exact (weightedContentUnitClosureValue_atWord D Sc cutoff N i M ⟨l⟩ hh r s b).trans
    (restriction_truncate_value D Sc cutoff N M ⟨l⟩ ⟨l⟩
      (positiveKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _)) b)

private theorem cap_atWord_raw (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0)
    (r s : ℕ) (b : (RM).obj ⟨l⟩) :
    weightedContentCapClosureValue D Sc cutoff N i M (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s b =
    M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (capWordCoefficient D Sc cutoff N i l hh r s) b := by
  exact (weightedContentCapClosureValue_atWord D Sc cutoff N i M ⟨l⟩ hh r s b).trans
    (restriction_truncate_value D Sc cutoff N M ⟨l⟩ ⟨l⟩
      (negativeKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _)) b)

attribute [local irreducible] unitWordCoefficient capWordCoefficient
  weightedContentUnitClosureCoefficient weightedContentCapClosureCoefficient

private def UnitEvaluation (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ) (b : M.obj w.obj),
    weightedContentUnitClosureValue D Sc cutoff N i M β hh w r s b =
      M.map (X := w.obj) (Y := w.obj)
        (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) b

private def CapEvaluation (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ) (b : M.obj w.obj),
    weightedContentCapClosureValue D Sc cutoff N i M β hh w r s b =
      M.map (X := w.obj) (Y := w.obj)
        (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) b

private theorem unit_atWord_evaluate (l : List I) :
    UnitEvaluation D Sc cutoff N i M (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ := by
  intro hh r s b
  exact (unit_atWord_raw D Sc cutoff N i M l hh r s b).trans
    (congrArg (fun f : (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩) f b)
      (unitCoefficient_atWord D Sc cutoff N i l hh r s).symm)

private theorem cap_atWord_evaluate (l : List I) :
    CapEvaluation D Sc cutoff N i M (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ := by
  intro hh r s b
  exact (cap_atWord_raw D Sc cutoff N i M l hh r s b).trans
    (congrArg (fun f : (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩) f b)
      (capCoefficient_atWord D Sc cutoff N i l hh r s).symm)

/-- The specified unit closure is the action of its original represented coefficient. -/
theorem weightedContentUnitClosureValue_evaluate (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :
    weightedContentUnitClosureValue D Sc cutoff N i M β hh w r s b =
    M.map (X := w.obj) (Y := w.obj)
      (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) b :=
  (contentRec D Sc cutoff N (P := UnitEvaluation D Sc cutoff N i M)
    (unit_atWord_evaluate D Sc cutoff N i M) β w) hh r s b

/-- The specified cap closure retains the same represented coefficient at arbitrary content. -/
theorem weightedContentCapClosureValue_evaluate (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :
    weightedContentCapClosureValue D Sc cutoff N i M β hh w r s b =
    M.map (X := w.obj) (Y := w.obj)
      (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) b :=
  (contentRec D Sc cutoff N (P := CapEvaluation D Sc cutoff N i M)
    (cap_atWord_evaluate D Sc cutoff N i M) β w) hh r s b

private theorem unitWordCoefficient_degree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (l : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ) :
    unitWordCoefficient D Sc cutoff N i l hh r s ∈
      truncatedDegree D Sc cutoff sy hc N l l (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold unitWordCoefficient
  change truncateOld D Sc cutoff N l l _ ∈ _
  apply truncateOld_mem_degree
  have h := positiveKernelClosure_degree D Sc cutoff sy hc i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree ⟨l⟩)
  simpa only [zero_add] using h

private theorem capWordCoefficient_degree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (l : List I) (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ) :
    capWordCoefficient D Sc cutoff N i l hh r s ∈
      truncatedDegree D Sc cutoff sy hc N l l (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold capWordCoefficient
  change truncateOld D Sc cutoff N l l _ ∈ _
  apply truncateOld_mem_degree
  have h := negativeKernelClosure_degree D Sc cutoff sy hc i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree ⟨l⟩)
  simpa only [zero_add] using h

private def UnitCoefficientDegree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ),
    weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ))

private def CapCoefficientDegree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ),
    weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ))

/-- The represented unit coefficient has the positive source integer degree. -/
theorem weightedContentUnitClosureCoefficient_degree
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h : UnitCoefficientDegree D Sc cutoff N i sy hc β w :=
    contentRec D Sc cutoff N (P := UnitCoefficientDegree D Sc cutoff N i sy hc)
      (fun l hh r s => (unitCoefficient_atWord D Sc cutoff N i l hh r s).symm ▸
        unitWordCoefficient_degree D Sc cutoff N i sy hc l hh r s) β w
  exact h hh r s

/-- The represented cap coefficient has the same positive source integer degree. -/
theorem weightedContentCapClosureCoefficient_degree
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h : CapCoefficientDegree D Sc cutoff N i sy hc β w :=
    contentRec D Sc cutoff N (P := CapCoefficientDegree D Sc cutoff N i sy hc)
      (fun l hh r s => (capCoefficient_atWord D Sc cutoff N i l hh r s).symm ▸
        capWordCoefficient_degree D Sc cutoff N i sy hc l hh r s) β w
  exact h hh r s

/-- Properties of the represented unit coefficient are checked on the truncated raw closure at
each stored word. -/
theorem weightedContentUnitClosureCoefficient_induction
    {P : ∀ (β : Multiset I) (w : ContentCategory D Sc cutoff N β), ℕ → ℕ → (w.obj ⟶ w.obj) → Prop}
    (h : ∀ (l : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ),
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
        (truncateOld D Sc cutoff N l l
          (positiveKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))))
    (β : Multiset I) (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    P β w r s (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) := by
  have hw : ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ),
      P β w r s (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) :=
    contentRec D Sc cutoff N
      (P := fun β w => ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ),
        P β w r s (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s))
      (fun l hh r s => (unitCoefficient_atWord D Sc cutoff N i l hh r s).symm ▸
        (h l hh r s : P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
          (unitWordCoefficient D Sc cutoff N i l hh r s))) β w
  exact hw hh r s

/-- Properties of the represented cap coefficient are checked on the truncated raw closure at
each stored word. -/
theorem weightedContentCapClosureCoefficient_induction
    {P : ∀ (β : Multiset I) (w : ContentCategory D Sc cutoff N β), ℕ → ℕ → (w.obj ⟶ w.obj) → Prop}
    (h : ∀ (l : List I) (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ),
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
        (truncateOld D Sc cutoff N l l
          (negativeKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))))
    (β : Multiset I) (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    P β w r s (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) := by
  have hw : ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ),
      P β w r s (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) :=
    contentRec D Sc cutoff N
      (P := fun β w => ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ),
        P β w r s (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s))
      (fun l hh r s => (capCoefficient_atWord D Sc cutoff N i l hh r s).symm ▸
        (h l hh r s : P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
          (capWordCoefficient D Sc cutoff N i l hh r s))) β w
  exact hw hh r s

end OddMath.QuiverHecke.ELVOld
