import OddMath

/-! # Coefficient-graded presentations

The coefficient ring is the Rees ring `ℚ[h] = MvPolynomial Unit ℚ`, graded with `h` in
degree `1`, and the generators are the quiver Hecke generators of the even datum on two
vertices with Cartan entries `-3` and symmetrizer `(1, 1)`, with their degrees `gdeg`. The
free presentation on these generators is coefficient-graded homogeneous, so its Hom groups are
the internal direct sums of their homogeneous parts, and `h` times a diagram lies one degree
above the diagram.
-/

noncomputable section
namespace NonVacuity.CoefficientGrading
open CategoryTheory OddMath OddMath.SKM OddMath.Diagrams.CoefficientGrading StringDiagrams

/-- Two even vertices with Cartan entries `-3`. -/
def datum : Datum Bool (Bool → ℤ) where
  cd := {
    root := fun j i => if i = j then 2 else -3
    coroot := fun i => LinearMap.proj i
    coroot_root_self := fun i => by simp }
  isGCM := {
    diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j hij
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => 0
  even_of_odd := by
    intro i j h
    exact absurd h (by decide)

/-- The symmetrizer `(1, 1)`. -/
def symmetrizer : Symmetrizer datum where
  d := fun _ => 1
  pos := by intro i; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

/-- The Rees ring `ℚ[h]`. -/
abbrev Rees := MvPolynomial Unit ℚ

/-- The grading of `ℚ[h]` with `h` in degree `1`. -/
abbrev reesGrading : ℤ → Submodule ℚ Rees :=
  MvPolynomial.weightedHomogeneousSubmodule ℚ (fun _ : Unit => (1 : ℤ))

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The generator degrees. -/
abbrev deg := QuiverHecke.gdeg datum symmetrizer

/-- The free presentation on the quiver Hecke generators over `ℚ[h]`. -/
def freePres : Presentation (QuiverHecke.sig datum) Rees where
  Rel := Empty
  dom := Empty.elim
  cod := Empty.elim
  rel := fun i => i.elim

theorem freePres_isHomogeneous : IsHomogeneous reesGrading deg freePres :=
  fun i => i.elim

/-- `h` times a diagram lies one degree above the diagram. -/
example {a b : Obj (QuiverHecke.sig datum)} (g : a ⟶ b) :
    (Finsupp.single g (MvPolynomial.X ()) : LinDiagram Rees a b) ∈
      part reesGrading deg a b (Diagram.degree deg g + 1) :=
  single_mem_part (𝒜 := reesGrading) (deg := deg)
    ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_X ℚ _ ()))

/-- The Hom groups are the internal direct sums of their homogeneous parts. -/
example (a b : Obj (QuiverHecke.sig datum)) :
    iSupIndep (presentedPart reesGrading deg freePres a b) ∧
      ⨆ d, presentedPart reesGrading deg freePres a b d = ⊤ :=
  ⟨iSupIndep_presentedPart freePres_isHomogeneous a b,
    iSup_presentedPart reesGrading deg freePres a b⟩

#print axioms OddMath.Diagrams.CoefficientGrading.iSupIndep_presentedPart

end NonVacuity.CoefficientGrading
