import OddMath.SKM.ScalarChangeBaseChange
import OddMath.SKM.MixedCrossingLocalExamples

/-!
Brundan–Ellis Definition 1.5 and GroundRingDescent §7: both directions of
presentation base change on two odd colours under `ZMod 9 → ZMod 3`.
The source has a nonzero coefficient killed by specialization. The inverse
is evaluated on dots, mixed inverse crossings, both same-colour inverse-entry
families, and the prescribed normalized cups and caps at every height.
-/

noncomputable section

namespace OddMath.SKM.ScalarChangeBaseChangeExamples

open CategoryTheory StringDiagrams Presentation ScalarChange MixedCrossingLocalExamples
open scoped TensorProduct

private def source : Scalars oddDatum (ZMod 9) where
  t _ _ := 1
  t_self _ := rfl
  t_symm_of_d_eq_zero _ _ _ := rfl
  s _ _ _ _ := 0
  s_symm _ _ _ _ := rfl
  s_eq_zero _ _ _ _ _ := rfl
  two_isUnit _ := (ZMod.isUnit_iff_coprime 2 9).2 (by decide)

/-- A nontrivial normalization unit, independent of weight, with trivial shifts. -/
private def bubble : CScalars source where
  c _ _ := -1
  shift _ _ _ := by simp [source]

private def specialize : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) _

local instance specializationAlgebra : Algebra (ZMod 9) (ZMod 3) := specialize.toAlgebra

example : (3 : ZMod 9) ≠ 0 ∧ specialize (3 : ZMod 9) = 0 := by
  constructor <;> decide

/-- The stated equivalence has the scalar action induced by this particular map. -/
def comparison (a b : Obj (sig oddDatum)) :
    (ZMod 3) ⊗[ZMod 9] ((pres oddDatum source).obj a ⟶ (pres oddDatum source).obj b) ≃ₗ[ZMod 3]
      ((pres oddDatum (scalars oddDatum specialize source)).obj a ⟶
        (pres oddDatum (scalars oddDatum specialize source)).obj b) :=
  homBaseChange specialize oddDatum source a b

example (a b : Obj (sig oddDatum))
    (x : (ZMod 3) ⊗[ZMod 9] ((pres oddDatum source).obj a ⟶ (pres oddDatum source).obj b)) :
    (comparison a b).symm (comparison a b x) = x := (comparison a b).symm_apply_apply x

example (a b : Obj (sig oddDatum))
    (x : (pres oddDatum (scalars oddDatum specialize source)).obj a ⟶
      (pres oddDatum (scalars oddDatum specialize source)).obj b) :
    comparison a b ((comparison a b).symm x) = x := (comparison a b).apply_symm_apply x

/-- The forward equivalence acts on an odd dot, with a nontrivial target coefficient. -/
example (μ : Bool → ℤ) (i : Bool) :
    comparison _ _ ((2 : ZMod 3) ⊗ₜ[ZMod 9]
      cl oddDatum source μ [up i] [up i] (dotsL [] i [] 1)) =
      (2 : ZMod 3) • cl oddDatum (scalars oddDatum specialize source)
        μ [up i] [up i] (dotsL [] i [] 1) := by
  change homBaseChange specialize oddDatum source _ _ _ = _
  rw [homBaseChange_tmul, homMap_cl]

/-- The inverse sends the target odd dot to the tensor of the source odd dot. -/
example (μ : Bool → ℤ) (i : Bool) :
    (comparison _ _).symm
      (cl oddDatum (scalars oddDatum specialize source) μ [up i] [up i] (dotsL [] i [] 1)) =
      1 ⊗ₜ[ZMod 9] cl oddDatum source μ [up i] [up i] (dotsL [] i [] 1) :=
  toTensor_cl specialize oddDatum source μ _ _ _

/-- Nonflat scalar extension is tested on the tensor itself, not only on scalar parameters. -/
example (μ : Bool → ℤ) (i : Bool) :
    (1 : ZMod 3) ⊗ₜ[ZMod 9]
      ((3 : ZMod 9) • cl oddDatum source μ [up i] [up i] (dotsL [] i [] 1)) = 0 := by
  apply (comparison _ _).injective
  change homBaseChange specialize oddDatum source _ _ _ = homBaseChange specialize oddDatum source _ _ 0
  rw [homBaseChange_tmul, homMap_smul]
  have h : specialize (3 : ZMod 9) = 0 := by decide
  rw [h, zero_smul, smul_zero, map_zero]

/-- Both composites are checked at the nonzero tensor coefficient `2`, on a mixed inverse. -/
example (μ : Bool → ℤ) :
    toTensor specialize oddDatum source _ _
      (fromTensor specialize oddDatum source _ _ ((2 : ZMod 3) ⊗ₜ[ZMod 9]
        cl oddDatum source μ [dn false, up true] [up true, dn false] (lcrossL false true))) =
      (2 : ZMod 3) ⊗ₜ[ZMod 9]
        cl oddDatum source μ [dn false, up true] [up true, dn false] (lcrossL false true) :=
  toTensor_fromTensor specialize oddDatum source _

example (μ : Bool → ℤ) :
    fromTensor specialize oddDatum source _ _
      (toTensor specialize oddDatum source _ _
        (cl oddDatum (scalars oddDatum specialize source) μ
          [dn false, up true] [up true, dn false] (lcrossL false true))) =
      cl oddDatum (scalars oddDatum specialize source) μ
        [dn false, up true] [up true, dn false] (lcrossL false true) :=
  fromTensor_toTensor specialize oddDatum source _

example (μ : Bool → ℤ) (i : Bool) (n : ℕ) :
    (comparison _ _).symm
      (cl oddDatum (scalars oddDatum specialize source) μ [] [up i, dn i] (dcupL i n)) =
      1 ⊗ₜ[ZMod 9] cl oddDatum source μ [] [up i, dn i] (dcupL i n) :=
  toTensor_cl specialize oddDatum source μ _ _ _

example (μ : Bool → ℤ) (i : Bool) (n : ℕ) :
    (comparison _ _).symm
      (cl oddDatum (scalars oddDatum specialize source) μ [dn i, up i] [] (dcapL i n)) =
      1 ⊗ₜ[ZMod 9] cl oddDatum source μ [dn i, up i] [] (dcapL i n) :=
  toTensor_cl specialize oddDatum source μ _ _ _

example (μ : Bool → ℤ) (i : Bool) :
    (comparison _ _).symm (etaP (cScalars oddDatum specialize bubble) i μ) =
      1 ⊗ₜ[ZMod 9] etaP bubble i μ := toTensor_etaP specialize oddDatum source bubble i μ

example (μ : Bool → ℤ) (i : Bool) :
    (comparison _ _).symm (epsP (cScalars oddDatum specialize bubble) i μ) =
      1 ⊗ₜ[ZMod 9] epsP bubble i μ := toTensor_epsP specialize oddDatum source bubble i μ

/-- Every target contextual relation is annihilated, with arbitrary linear pre/post factors. -/
example (r : (pres oddDatum (scalars oddDatum specialize source)).AllRel)
    (l : Obj (sig oddDatum)) (v : List (sig oddDatum).Colour) (h : r.dom.WhiskerOK l v)
    {a b : Obj (sig oddDatum)} (pre : LinDiagram (ZMod 3) a (r.dom.whisker l v))
    (post : LinDiagram (ZMod 3) (r.cod.whisker l v) b) :
    tensorLin specialize oddDatum source a b (pre ≫ LinDiagram.whisker r.rel l v h ≫ post) = 0 :=
  tensorLin_mem_ideal specialize oddDatum source
    (Submodule.subset_span (IdealGen.intro r l v h pre post))

#print axioms OddMath.SKM.ScalarChange.tensorLin_mem_ideal
#print axioms OddMath.SKM.ScalarChange.toTensor_fromTensor
#print axioms OddMath.SKM.ScalarChange.fromTensor_toTensor
#print axioms OddMath.SKM.ScalarChange.homBaseChange
#print axioms OddMath.SKM.ScalarChange.toTensor_etaP
#print axioms OddMath.SKM.ScalarChange.toTensor_epsP
#print axioms comparison

end OddMath.SKM.ScalarChangeBaseChangeExamples
