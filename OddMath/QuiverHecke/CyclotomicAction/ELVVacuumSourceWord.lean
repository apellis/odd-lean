import OddMath.QuiverHecke.CyclotomicAction.ELVContentYoneda
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceCrossing
/-! # Iterated vacuum-word sources

`wordPairCoordinates_comparison` proves compatibility of the canonical source
comparison with the existing recursive prefix isomorphism `wordIsoAt`.
`wordPairCross_mixed`, `wordPairCross_equal`, and `wordPairCross_of_mem` compute
the actual normalized pair crossing on two single-letter inductions of any
vacuum-word prefix, with arbitrary repetitions and full coefficient parity.
The two letters are ordered as inductions, so `[i,j]` corresponds to `j::i::ρ`.
A direct comparison with `wordIsoAt` for the entire extended word, and the
source-and-reservoir Hom pairing, are not asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem representableIso_even (β : Multiset I) (σ : List I)
    (v : ContentCategory D Sc cutoff N β) :
    (InductionRepresentable.iso D Sc cutoff N β σ v).hom ∈ parity (R := k) _ _ 0 := by
  rw [Superfunctor.mem_parity_iff_isHomogeneous]
  intro q hq
  funext w
  change (if q = 0 then InductionRepresentable.forward D Sc cutoff N β σ v w else 0) = 0
  exact ite_eq_right_iff.mpr (fun h => (hq h).elim)

theorem wordIso_even (ρ : List I) :
    (VacuumRepresentable.wordIso D Sc cutoff N ρ).hom ∈ parity (R := k) _ _ 0 := by
  induction ρ with
  | nil => exact id_mem _
  | cons i ρ ih =>
    have hc := comp_mem
      (IsSuperfunctor.map_mem (F := contentInduction D Sc cutoff N _ [i]) ih)
      (representableIso_even D Sc cutoff N _ [i] (VacuumRepresentable.wordObject D Sc cutoff N ρ))
    simp only [zero_add] at hc
    convert hc using 1 <;> rfl

theorem wordIsoAt_even (ρ : List I) (β : Multiset I) (hρ : VacuumRepresentable.content ρ = β) :
    (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).hom ∈ parity (R := k) _ _ 0 := by
  subst β
  exact wordIso_even D Sc cutoff N ρ

def pairMap (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) {M L : ContentModules D Sc cutoff N β}
    (f : M ⟶ L) (w : ContentCategory D Sc cutoff N γ) :
    ContentEPairSpace D Sc cutoff N β i j γ h M w →ₗ[k]
      ContentEPairSpace D Sc cutoff N β i j γ h L w :=
  ((contentEPairTo D Sc cutoff N β i j γ h).map f).total w

theorem pairCross_even_naturality (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    {M L : ContentModules D Sc cutoff N β} (f : M ⟶ L) (hf : f ∈ parity (R := k) _ _ 0)
    (w : ContentCategory D Sc cutoff N γ) :
    contentEPairCross D Sc cutoff N β i j γ hij hji L w ∘ₗ
      pairMap D Sc cutoff N β j i γ hji f w =
    pairMap D Sc cutoff N β i j γ hij f w ∘ₗ
      contentEPairCross D Sc cutoff N β i j γ hij hji M w := by
  have hn := (contentEPairCrossTransform D Sc cutoff N β i j γ hij hji).naturality
    (D.parity i * D.parity j) f hf
  simp only [koszulSign_zero_right, one_smul] at hn
  have ht := congrArg (fun g => g.total w) hn
  simp only [Superfunctor.comp_total, contentEPairCross_total] at ht
  convert ht using 1 <;> rfl

/-- Coordinates on two actual single-letter inductions of a vacuum-word prefix.
The prefix is evaluated by the existing recursive `wordIsoAt`; the two new
letters are evaluated successively, as in `pairCoordinates`. -/
def wordPairCoordinates (ρ : List I) (β : Multiset I) (hρ : VacuumRepresentable.content ρ = β)
    (i j : I) (γ : Multiset I) (h : β + ([i,j] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff N γ) :
    ContentEPairSpace D Sc cutoff N β i j γ h
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w →ₗ[k]
      ((contentAppendTo D Sc cutoff N β [i,j] γ h).obj
        (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ⟶ w) :=
  pairCoordinates D Sc cutoff N β i j γ h
    (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) w ∘ₗ
    pairMap D Sc cutoff N β i j γ h
      (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).hom w

theorem pairCross_coordinates_of_even (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (f : M ⟶ contentRepresentable D Sc cutoff N β v) (hf : f ∈ parity (R := k) _ _ 0)
    (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji M w) :
    pairCoordinates D Sc cutoff N β i j γ hij v w
      (pairMap D Sc cutoff N β i j γ hij f w
        (contentEPairCross D Sc cutoff N β i j γ hij hji M w x)) =
    contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v ≫
      twist k (D.parity i * D.parity j)
        (pairCoordinates D Sc cutoff N β j i γ hji v w
          (pairMap D Sc cutoff N β j i γ hji f w x)) := by
  have he := congrArg (fun l => l x)
    (pairCross_even_naturality D Sc cutoff N β i j γ hij hji f hf w)
  erw [← he]
  exact pairCross_coordinates D Sc cutoff N β i j γ hij hji v w
    (pairMap D Sc cutoff N β j i γ hji f w x)

/-- Normalized crossing on an actual iterated vacuum-word source, through the
canonical source comparison, not merely on a represented reservoir target. -/
theorem wordPairCross_coordinates (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w) :
    wordPairCoordinates D Sc cutoff N ρ β hρ i j γ hij w
      (contentEPairCross D Sc cutoff N β i j γ hij hji
        (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w x) =
    contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j)
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ≫
        twist k (D.parity i * D.parity j)
          (wordPairCoordinates D Sc cutoff N ρ β hρ j i γ hji w x) := by
  exact pairCross_coordinates_of_even D Sc cutoff N β i j γ hij hji
    (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ)
    (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ)
    (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).hom
    (wordIsoAt_even D Sc cutoff N ρ β hρ) w x

/-- Naturality of the canonical block comparison on its actual balanced carriers. -/
theorem pairMap_comparison (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) {M L : ContentModules D Sc cutoff N β}
    (f : M ⟶ L) (w : ContentCategory D Sc cutoff N γ) :
    (contentEPairEquiv D Sc cutoff N β i j γ h L w).toLinearMap ∘ₗ
      pairMap D Sc cutoff N β i j γ h f w =
    ((contentInductionTo D Sc cutoff N β [i,j] γ h).map f).total w ∘ₗ
      (contentEPairEquiv D Sc cutoff N β i j γ h M w).toLinearMap := by
  have hn := (contentEPairToComparison D Sc cutoff N β i j γ h).hom.naturality f
  have ht := congrArg (fun g => g.total w) hn
  simp only [Superfunctor.comp_total] at ht
  convert ht using 1
  all_goals rfl

theorem pairCoordinates_eq (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    pairCoordinates D Sc cutoff N β i j γ h v w =
    (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] γ h v w).toLinearMap ∘ₗ
      (contentEPairEquiv D Sc cutoff N β i j γ h (contentRepresentable D Sc cutoff N β v) w).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact pairCoordinates_comparison D Sc cutoff N β i j γ h v w x

/-- The recursive prefix evaluation commutes with the canonical source comparison. -/
theorem wordPairCoordinates_comparison (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (w : ContentCategory D Sc cutoff N γ) :
    wordPairCoordinates D Sc cutoff N ρ β hρ i j γ h w =
    (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] γ h
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) w).toLinearMap ∘ₗ
      (((contentInductionTo D Sc cutoff N β [i,j] γ h).map
        (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).hom).total w ∘ₗ
        (contentEPairEquiv D Sc cutoff N β i j γ h
          (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w).toLinearMap) := by
  unfold wordPairCoordinates
  erw [pairCoordinates_eq, LinearMap.comp_assoc, pairMap_comparison]

theorem wordPairCross_mixed (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (hne : i ≠ j) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w) :
    wordPairCoordinates D Sc cutoff N ρ β hρ i j γ hij w
      (contentEPairCross D Sc cutoff N β i j γ hij hji
        (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w x) =
    contentAppendToComponent D Sc cutoff N hij hji (crossTwo D Sc i j)
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ≫
        twist k (D.parity i * D.parity j)
          (wordPairCoordinates D Sc cutoff N ρ β hρ j i γ hji w x) := by
  rw [wordPairCross_coordinates, contentCrossAffine_distinct D Sc i j hne]

theorem wordPairCross_equal (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i : I) (γ : Multiset I)
    (hij : β + ([i,i] : Multiset I) = γ) (hji : β + ([i,i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β i i γ hji
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w) :
    wordPairCoordinates D Sc cutoff N ρ β hρ i i γ hij w
      (contentEPairCross D Sc cutoff N β i i γ hij hji
        (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w x) =
    -(contentAppendToComponent D Sc cutoff N hij hji (crossTwo D Sc i i)
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ≫
        twist k (D.parity i * D.parity i)
          (wordPairCoordinates D Sc cutoff N ρ β hρ i i γ hji w x)) := by
  rw [wordPairCross_coordinates, contentCrossAffine_equal, contentAppendToComponent_neg,
    Preadditive.neg_comp]

theorem wordPairCross_of_mem (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w)
    (q : ZMod 2) (hx : wordPairCoordinates D Sc cutoff N ρ β hρ j i γ hji w x ∈
      parity (R := k) _ _ q) :
    wordPairCoordinates D Sc cutoff N ρ β hρ i j γ hij w
      (contentEPairCross D Sc cutoff N β i j γ hij hji
        (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w x) =
    sign k ((D.parity i * D.parity j) * q) •
      (contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j)
        (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ≫
          wordPairCoordinates D Sc cutoff N ρ β hρ j i γ hji w x) := by
  rw [wordPairCross_coordinates, twist_of_mem _ hx, Linear.comp_smul]

end OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
