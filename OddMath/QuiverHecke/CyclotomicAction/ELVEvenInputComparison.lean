import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputOperators

/-! # Even counit and induction-dot input comparison
The canonical even source and ordinary adjunction counit/dot in
DeformedMatrixComparison §4 agree with the prescribed raw input operators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The induction dot on the literal even-moving coefficient module. -/
def evenSourceInputDot (i : {i : I // D.parity i = 0}) (v t : List I) :
    Source D Sc cutoff i.1 v t →ₗ[k] Source D Sc cutoff i.1 v t :=
  inductionDot D Sc cutoff i.1 (evenMovingCoefficientModule D Sc cutoff i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

theorem evenSourceInputDot_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    evenSourceInputDot D Sc cutoff i v t (tensor D Sc cutoff i.1 v s t g b) =
      tensor D Sc cutoff i.1 v s t
        (oldAppendDotComponent D Sc cutoff i.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g) b := by
  change inductionDot D Sc cutoff i.1 (evenMovingCoefficientModule D Sc cutoff i v) _
    (BalancedInduction.tensor _ _ _ g b) = _
  rw [inductionDot_tensor]
  have hg : twist k (D.parity i.1)
      (X := (append D Sc cutoff i.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g = g := by
    rw [i.property, twist_zero]
  rw [hg]
  rfl

theorem evenSourceInputContraction_q (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ShortTarget D Sc cutoff i.1 v t) :
    evenSourceInputContraction D Sc cutoff i v t (q D Sc cutoff i.1 v t z) =
      evenInputContractionAffine D Sc cutoff i.1 v t z := by
  suffices h : (evenSourceInputContraction D Sc cutoff i v t).comp
      (q D Sc cutoff i.1 v t) = evenInputContractionAffine D Sc cutoff i.1 v t from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputContraction D Sc cutoff i v t
    (q D Sc cutoff i.1 v t (shortTensor D Sc cutoff i.1 v s.word t g b)) = _
  rw [q_shortTensor, evenSourceInputContraction_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i.1])).mkQ_surjective b
  change _ = appendC0InputDefect D Sc cutoff i.1 v t
    (shortCross D Sc cutoff i.1 v t
      (shortTensor D Sc cutoff i.1 v s.word t g ((ideal D Sc cutoff _ _).mkQ r))) 0
  rw [ShortCrossCoordinates.column_mk, appendC0InputDefect_crossing]
  simp only [Finsupp.neg_apply, Finsupp.single_eq_same, i.property, zero_mul,
    SKM.zsign_zero, twist_zero, neg_one_smul]
  rfl

theorem evenSourceInputDot_q (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ShortTarget D Sc cutoff i.1 v t) :
    evenSourceInputDot D Sc cutoff i v t (q D Sc cutoff i.1 v t z) =
      q D Sc cutoff i.1 v t (evenCrossingInputDotAffine D Sc cutoff i.1 v t z) := by
  suffices h : (evenSourceInputDot D Sc cutoff i v t).comp (q D Sc cutoff i.1 v t) =
      (q D Sc cutoff i.1 v t).comp (evenCrossingInputDotAffine D Sc cutoff i.1 v t) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputDot D Sc cutoff i v t
    (q D Sc cutoff i.1 v t (shortTensor D Sc cutoff i.1 v s.word t g b)) =
    q D Sc cutoff i.1 v t
      (evenCrossingInputDotAffine D Sc cutoff i.1 v t
        (shortTensor D Sc cutoff i.1 v s.word t g b))
  rw [q_shortTensor, evenSourceInputDot_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i.1])).mkQ_surjective b
  rw [evenCrossingInputDotAffine_representative D Sc cutoff i.1 i.property,
    q_shortTensor, oldAppendDotComponent_eq]
  rfl

/-- Equality on all balanced classes, not only on chosen representatives. -/
theorem evenSourceInputContraction_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenSourceInputContraction D Sc cutoff i v t =
      evenInputContraction D Sc cutoff i.1 i.property v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i.1 v t z
  rw [evenSourceInputContraction_q, evenInputContraction_q]

/-- The ordinary actual induction dot is the prescribed even input dot. -/
theorem evenSourceInputDot_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenSourceInputDot D Sc cutoff i v t =
      evenCrossingInputDot D Sc cutoff i.1 i.property v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i.1 v t z
  rw [evenSourceInputDot_q, evenCrossingInputDot_q]


/-- The canonical source comparison intertwines the ordinary actual dot.
There is no parity conjugation or higher-row scalar for an even colour. -/
theorem evenSourceInputDot_sourceEquiv (i : {i : I // D.parity i = 0})
    (v t : List I)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    evenSourceInputDot D Sc cutoff i v t (evenSourceEquiv D Sc cutoff i v t z) =
      evenSourceEquiv D Sc cutoff i v t
        (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  suffices h : (evenSourceInputDot D Sc cutoff i v t).comp
      (evenSourceEquiv D Sc cutoff i v t).toLinearMap =
      (evenSourceEquiv D Sc cutoff i v t).toLinearMap.comp
        (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff)) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputDot D Sc cutoff i v t
    (evenSourceEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i.1)
        (restrictedRepresentable D Sc cutoff i.1 v).toFunctor s g b)) =
    evenSourceEquiv D Sc cutoff i v t
      (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v) _
        (BalancedInduction.tensor _ _ s g b))
  rw [evenSourceEquiv_tensor, evenSourceInputDot_tensor, inductionDot_tensor]
  have hg : twist k (D.parity i.1)
      (X := (append D Sc cutoff i.1).obj s)
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g = g := by
    rw [i.property, twist_zero]
  rw [hg, evenSourceEquiv_tensor]


theorem evenSourceInputDot_iterate_sourceEquiv (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    (evenSourceInputDot D Sc cutoff i v t)^[n] (evenSourceEquiv D Sc cutoff i v t z) =
      evenSourceEquiv D Sc cutoff i v t ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, evenSourceInputDot_sourceEquiv,
      Function.iterate_succ_apply']

/-- Every even cap row has the same constant minus relative to the ordinary
adjunction counit, independently of the row index. -/
theorem evenCapRow_normalization (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    evenSourceInputContraction D Sc cutoff i v t
      ((evenSourceInputDot D Sc cutoff i v t)^[n] (evenSourceEquiv D Sc cutoff i v t z)) =
      -unshiftedCounitComponent D Sc cutoff i.1 v t ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  rw [evenSourceInputDot_iterate_sourceEquiv, evenSourceInputContraction_counit]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
