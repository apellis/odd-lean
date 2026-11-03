import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedExtension
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteMatrixComponents

/-! # Missing-colour support and the zero predecessor boundary

DeformedMatrixComparison (4) at an output content containing no i has zero
lower E/F term. Full-content extension is zero after restriction by append i,
so the principal shifted source coordinate is zero. Off-diagonal Cartan signs
also give the required nonnegative height, including the genuinely empty
output content. This is separate from an empty predecessor with output[i].
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

/-- A balanced induction coend of zero input values has only the zero vector. -/
theorem obj_subsingleton_of_values_subsingleton
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] (J : C ⥤ A) (M : C ⥤ SVec k)
    (hM : ∀ s, Subsingleton (M.obj s)) (w : A) : Subsingleton (Obj J M w) := by
  have hz : (LinearMap.id : Obj J M w →ₗ[k] Obj J M w) = 0 := by
    apply hom_ext J M
    intro s g b
    change tensor J M s g b = 0
    rw [(hM s).elim b 0, tensor_zero_right]
  exact ⟨fun x y => (LinearMap.congr_fun hz x).trans (LinearMap.congr_fun hz y).symm⟩

end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

private theorem absentCartanSum_nonpos (i : I) :
    ∀ γ : List I, i ∉ γ → (γ.map (fun j => D.h i (D.α j))).sum ≤ 0 := by
  intro γ
  induction γ with
  | nil => intro _; simp only [List.map_nil, List.sum_nil, le_refl]
  | cons j γ ih =>
    intro hi
    have hij : i ≠ j := fun h => hi (by simp only [h, List.mem_cons, true_or])
    have hγ : i ∉ γ := fun hm => hi (List.mem_cons_of_mem j hm)
    have hj := D.d_nonneg hij
    dsimp only [SKM.Datum.d] at hj
    have hj' : D.h i (D.α j) ≤ 0 := neg_nonneg.mp hj
    simpa only [List.map_cons, List.sum_cons] using add_nonpos hj' (ih hγ)

/-- Missing i forces nonnegative Cartan height, for every cutoff and also γ=[]. -/
theorem contentCrossingHeight_nonneg_of_not_mem (cutoff : I → ℕ) (γ : List I) (i : I)
    (hi : i ∉ γ) : 0 ≤ contentCrossingHeight D cutoff i (γ : Multiset I) := by
  rw [contentCrossingHeight_coe]
  have hs := absentCartanSum_nonpos D i γ hi
  have hc : (0 : ℤ) ≤ cutoff i := Int.natCast_nonneg _
  omega

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
include hi
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "J" => append D Sc cutoff i
local notation "G" => induced Q N

/-- An appended i can never lie in an output block lacking i. -/
theorem oldContentAppend_offContent_of_not_mem (v : OldCategory D Sc cutoff) :
    (((J).obj v).word : Multiset I) ≠ (γ : Multiset I) := by
  intro he
  have hm : i ∈ (((J).obj v).word : Multiset I) := by
    change i ∈ (v.word ++ [i] : List I)
    simp only [List.mem_append, List.mem_singleton, or_true]
  have hmγ : i ∈ (γ : Multiset I) := by
    rw [← he]
    exact hm
  exact hi hmγ

/-- The actual append restriction of the full-content extension is zero on
all old words, not just on the chosen output object. -/
theorem oldContentRestriction_subsingleton_of_not_mem (v : OldCategory D Sc cutoff) :
    Subsingleton (((restriction J).obj G).obj v) :=
  oldContentExtension_supported D Sc cutoff γ N ((J).obj v)
    (oldContentAppend_offContent_of_not_mem D Sc cutoff γ i hi v)

/-- The actual lower E/F coend is zero throughout a missing-colour block. -/
theorem oldContentIndRes_subsingleton_of_not_mem (w : OldCategory D Sc cutoff) :
    Subsingleton ((induced J ((restriction J).obj G)).obj w) :=
  obj_subsingleton_of_values_subsingleton J ((restriction J).obj G).toFunctor
    (oldContentRestriction_subsingleton_of_not_mem D Sc cutoff γ i hi N) w

local instance absentColourGlobalPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The principal canonical source slot of the GIVEN global unit matrix is
zero; it can be dropped without an inverse or compatibility hypothesis. -/
theorem oldContentUnitPrincipal_subsingleton_of_not_mem
    (b : ℕ) (w : OldCategory D Sc cutoff) :
    Subsingleton ((unitMatrixFamily D Sc cutoff i G b none).obj w) := by
  have := oldContentIndRes_subsingleton_of_not_mem D Sc cutoff γ i hi N w
  exact Function.Injective.subsingleton
    (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
      (induced J ((restriction J).obj G))) w).injective

end OddMath.QuiverHecke.ELVOld
