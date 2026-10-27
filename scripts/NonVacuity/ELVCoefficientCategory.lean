import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientCategory

noncomputable section
namespace ELVCoefficientCategoryConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
/-- Odd rank one over a ring with two invertible. -/
def datum : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

def oddColour : {i : Unit // datum.parity i = 1} := ⟨(), rfl⟩

def delta : SKM.SYM datum ℚ := SKM.SYM.delta datum ℚ oddColour

/-- The tested exterior coefficient is not specialized to zero. -/
theorem delta_ne_zero : delta ≠ 0 := by
  intro h
  have he := congrArg (SKM.SYM.exteriorProjection datum ℚ) h
  simp only [delta, SKM.SYM.exteriorProjection_delta, map_zero] at he
  have hz := (ExteriorAlgebra.ι_eq_zero_iff (R := ℚ) _).mp he
  have hz' := congrArg (fun f : SKM.SYM.OddModule datum ℚ => f oddColour) hz
  simp at hz'

open SKM.SYM

/-- The odd parameter survives the exact quotient at both positive cutoff parities. -/
theorem quotient_delta_ne_zero (N : ℕ) (hN : 1 ≤ N) :
    elvCoefficientQuotient datum (fun _ => N) delta ≠ 0 := by
  have hd : delta ∈ CoefficientAtMost datum ℚ 1 := by
    apply Submodule.subset_span
    refine ⟨(0, {oddColour}), ?_, ?_⟩
    · simp [coefficientWeight]
    · exact coefficientBasis_delta datum ℚ oddColour
  intro hz
  have hi := elvCoefficient_quotient_injective datum ℚ
    (cutoff := fun _ => N) (d := 1) (fun _ => hN)
  have he := hi (a₁ := ⟨delta, hd⟩) (a₂ := 0) hz
  exact delta_ne_zero (congrArg Subtype.val he)

example := quotient_delta_ne_zero 2 (by decide)
example := quotient_delta_ne_zero 3 (by decide)

/-- Both projections of the top-relation generator remain in the exact coefficient ideal. -/
example (p : ZMod 2) : (polynomialExteriorEquiv datum ℚ).symm
    (GradedAlgebra.proj (polynomialExteriorParity datum ℚ) p
      (polynomialExteriorEquiv datum ℚ (delta * e datum ℚ () 0))) ∈
      elvCoefficientIdeal datum ℚ (fun _ => 2) := by
  apply elvCoefficientIdeal_parity
  rw [AlgEquiv.symm_apply_apply]
  exact TwoSidedIdeal.subset_span (Or.inr ⟨oddColour, rfl, rfl⟩)

/-- The finite coefficient algebra retains the odd parity of delta. -/
example : elvCoefficientQuotient datum (fun _ => 2) delta ∈
    elvCoefficientParity datum (fun _ => 2) 1 := by
  have h := elvModelQuotient_mem (k := ℚ) datum (cutoff := fun _ => 2)
    (polynomialExterior_delta_mem_odd datum ℚ oddColour)
  change elvCoefficientQuotient datum (fun _ => 2)
    ((polynomialExteriorEquiv datum ℚ).symm (polynomialExteriorEquiv datum ℚ delta)) ∈ _ at h
  rw [AlgEquiv.symm_apply_apply] at h
  exact h

def dot : End ((pres datum scalars).obj (ob datum [()])) := dotE datum scalars [()] 0

theorem dot_odd : dot ∈ parity (R := ℚ) _ _ 1 :=
  positionedDot_parity datum scalars [] [] ()

abbrev finiteObj := elvQuotientObj datum scalars (fun _ => 2) (coefficientObj datum scalars [()])
abbrev finiteFunctor := elvQuotientFunctor datum scalars (fun _ => 2)

/-- This is composition in the quotient category, with its nontrivial sign. -/
example :
    finiteFunctor.map (sourceCoefficientHom datum scalars delta (𝟙 ((pres datum scalars).obj (ob datum [()])))) ≫
      finiteFunctor.map (sourceCoefficientHom datum scalars 1 dot) =
      -finiteFunctor.map (sourceCoefficientHom datum scalars delta dot) := by
  simpa only [Category.id_comp, delta] using
    elvQuotient_odd_comp_odd datum scalars (fun _ => 2) oddColour (𝟙 _) dot_odd

/-- Reversing the order introduces no additional coefficient sign. -/
example :
    finiteFunctor.map (sourceCoefficientHom datum scalars 1 dot) ≫
      finiteFunctor.map (sourceCoefficientHom datum scalars delta (𝟙 _)) =
      finiteFunctor.map (sourceCoefficientHom datum scalars delta dot) := by
  rw [← Functor.map_comp]
  have h := sourceCoefficientHom_comp datum scalars
    (show polynomialExteriorEquiv datum ℚ 1 ∈ polynomialExteriorParity datum ℚ 0 by
      rw [map_one]; exact SetLike.GradedOne.one_mem)
    delta dot (Supercategory.id_mem (R := ℚ) _)
  simpa [koszulSign] using congrArg finiteFunctor.map h

/-- The functor preserves the total parity, including the odd coefficient. -/
example : finiteFunctor.map (sourceCoefficientHom datum scalars delta (𝟙 _)) ∈
    parity (R := ℚ) finiteObj finiteObj 1 := by
  apply elvQuotientMap_mem
  change coefficientHom datum scalars (polynomialExteriorEquiv datum ℚ delta) (𝟙 _) ∈ _
  have h : coefficientHom datum scalars (polynomialExteriorEquiv datum ℚ delta) (𝟙 _) ∈
      parity (R := ℚ) (coefficientObj datum scalars [()]) (coefficientObj datum scalars [()]) (1 + 0) :=
    BoxProd.tmul_mem_parity (polynomialExterior_delta_mem_odd datum ℚ oddColour) (Supercategory.id_mem _)
  simpa only [add_zero] using h

/-- The even-cutoff top relation vanishes in the category, with an affine dot retained. -/
example : finiteFunctor.map
    (sourceCoefficientHom datum scalars (delta * e datum ℚ () 0) dot) = 0 := by
  apply elvQuotientMap_kills
  exact TwoSidedIdeal.subset_span (Or.inr ⟨oddColour, rfl, rfl⟩)

/-- A two-sided composite, rather than just an isolated coefficient relation, is killed. -/
example : finiteFunctor.map
    (sourceCoefficientHom datum scalars 1 dot ≫
      sourceCoefficientHom datum scalars (delta * e datum ℚ () 0) (𝟙 _) ≫
      sourceCoefficientHom datum scalars 1 dot) = 0 := by
  apply elvQuotientMap_kills_span datum scalars (fun _ => 2) [()] [()]
  apply Submodule.subset_span
  refine ⟨[()], rfl, delta * e datum ℚ () 0, ?_, _, _, rfl⟩
  exact TwoSidedIdeal.subset_span (Or.inr ⟨oddColour, rfl, rfl⟩)

/-- The Homs and the earlier tensor quotient agree on a nonempty strand word. -/
example := elvQuotientMap_eq datum scalars (fun _ => 2) [()] [()]
example := elvQuotientMap_eq datum scalars (fun _ => 3) [] []
example := elvQuotientFunctor_super datum scalars (fun _ => 2)
example := finiteFunctor.map_comp
  (sourceCoefficientHom datum scalars delta dot) (sourceCoefficientHom datum scalars 1 dot)
example := finiteFunctor.map_id (coefficientObj datum scalars [()])

/-- Cutoff zero is not excluded; the coefficient relation then kills delta. -/
example : (elvQuotientFunctor datum scalars (fun _ => 0)).map
    (sourceCoefficientHom datum scalars delta dot) = 0 := by
  apply elvQuotientMap_kills
  exact TwoSidedIdeal.subset_span (Or.inr ⟨oddColour, rfl, by simp [delta, elvChi]⟩)

/-- A nonreduced commutative ground ring with two invertible. -/
def scalarsModNine : SKM.Scalars datum (ZMod 9) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => ⟨⟨2, 5, by decide, by decide⟩, rfl⟩

example : (3 : ZMod 9) ≠ 0 ∧ (3 : ZMod 9) * 3 = 0 := by decide
example := elvQuotient_odd_comp_odd datum scalarsModNine (fun _ => 2) oddColour (𝟙 _)
  (positionedDot_parity datum scalarsModNine [] [] ())
example := elvQuotientMap_eq datum scalarsModNine (fun _ => 3) [()] [()]
example : (elvQuotientFunctor datum scalarsModNine (fun _ => 2)).map
    (sourceCoefficientHom datum scalarsModNine
      (SKM.SYM.delta datum (ZMod 9) oddColour * e datum (ZMod 9) () 0)
      (dotE datum scalarsModNine [()] 0)) = 0 := by
  apply elvQuotientMap_kills
  exact TwoSidedIdeal.subset_span (Or.inr ⟨oddColour, rfl, rfl⟩)

#print axioms elvCoefficientIdeal_parity
#print axioms elvCoefficientGradedAlgebra
#print axioms elvQuotientMap_comp
#print axioms elvQuotientMap_mem
#print axioms elvQuotientFunctor
#print axioms elvQuotientMap_eq
#print axioms elvCoefficientRelationSpan_le
#print axioms elvQuotientMap_kills_span
#print axioms elvQuotient_odd_comp_odd
#print axioms quotient_delta_ne_zero
end ELVCoefficientCategoryConsumer
