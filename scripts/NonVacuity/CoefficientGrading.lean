import OddMath

/-! # Coefficient-graded presentations

The coefficient ring is the Rees ring `ℚ[h] = MvPolynomial Unit ℚ`, graded with `h` in
degree `1`, and the generators are the quiver Hecke generators of the even datum on two
vertices with Cartan entries `-3` and symmetrizer `(1, 1)`, with their degrees `gdeg`. The
free presentation on these generators and the quiver Hecke presentation with the Rees
parameters of `Qᵢⱼ(u, v) = u³ + uv + v³` (lower-degree, not homogeneous) are
coefficient-graded homogeneous, so their Hom groups are the internal direct sums of their
homogeneous parts; `h` times a diagram lies one degree above the diagram.
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
abbrev reesGrading : ℤ → Submodule ℚ Rees := QuiverHecke.reesGrading ℚ

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

/-- `Qᵢⱼ(u, v) = u³ + uv + v³` over `ℚ`: only `s^{11}` is nonzero. These parameters are
lower-degree but not homogeneous (`scripts/NonVacuity/GradedParameters.lean`). -/
def scalars : Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun i j p q => if i ≠ j ∧ p = 1 ∧ q = 1 then 1 else 0
  s_symm := by
    intro i j p q
    by_cases h : i = j
    · subst h; simp [and_comm]
    · simp [h, Ne.symm h, and_comm]
  s_eq_zero := by
    intro i j p q h
    simp [datum] at h
  two_isUnit := by intro _; norm_num

theorem d_ne {i j : Bool} (h : i ≠ j) : datum.d i j = 3 := by
  cases i <;> cases j <;> first | exact absurd rfl h | rfl

theorem lowerDegree : scalars.LowerDegree symmetrizer := by
  intro i j p q _ _ _ _ hs
  have h : i ≠ j ∧ p = 1 ∧ q = 1 := by
    by_contra h
    exact hs (by simp [scalars, h])
  obtain ⟨hij, rfl, rfl⟩ := h
  simp [coefficientDegree, symmetrizer, d_ne hij]

/-- The quiver Hecke presentation with the Rees parameters `s^{11} h²` over `ℚ[h]` is
coefficient-graded homogeneous, so its Hom groups are graded. -/
example (a b : Obj (QuiverHecke.sig datum)) :
    iSupIndep (presentedPart reesGrading deg
      (QuiverHecke.pres datum (ReesParameters.scalars symmetrizer scalars)) a b) :=
  iSupIndep_presentedPart (QuiverHecke.isHomogeneous_rees datum symmetrizer lowerDegree) a b


/-- The quiver Hecke supercategory over `ℚ[h]` with the Rees parameters is a graded
supercategory over `ℚ`. -/
abbrev HRees := QuiverHecke.H datum (ReesParameters.scalars symmetrizer scalars)

example :
    letI := OddMath.Diagrams.Linear.restrictScalars ℚ Rees HRees
    letI := OddMath.Diagrams.Supercategory.restrictScalars ℚ Rees HRees
    GradedSupercategory ℚ HRees :=
  QuiverHecke.reesGradedSupercategory datum symmetrizer lowerDegree

/-- `h` times an identity has degree `1`. -/
example (a : Obj (QuiverHecke.sig datum)) :
    letI := OddMath.Diagrams.Linear.restrictScalars ℚ Rees HRees
    letI := OddMath.Diagrams.Supercategory.restrictScalars ℚ Rees HRees
    letI := QuiverHecke.reesGradedSupercategory datum symmetrizer lowerDegree
    (MvPolynomial.X () : Rees) • 𝟙 ((QuiverHecke.pres datum
        (ReesParameters.scalars symmetrizer scalars)).obj a) ∈
      GradedSupercategory.degree (R := ℚ) (C := HRees) _ _ 1 := by
  change _ ∈ presentedPart reesGrading deg
    (QuiverHecke.pres datum (ReesParameters.scalars symmetrizer scalars)) a a 1
  rw [← Presentation.lin_id, ← Presentation.lin_smul]
  refine lin_mem_presentedPart ?_
  have hX : (MvPolynomial.X () : Rees) ∈ reesGrading 1 :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_X ℚ _ ())
  exact smul_mem_part hX (of_mem_part' (𝒜 := reesGrading) (deg := deg) (𝟙 a)
    (Diagram.degree_id _ _))

/-- The truncation `ℚ[h]/(h³)` with `h` in degree `1` grades the quiver Hecke supercategory
with the truncated Rees parameters. -/
example :
    letI := OddMath.Diagrams.Linear.restrictScalars ℚ (TruncatedRees.TruncRing ℚ 3)
      (QuiverHecke.H datum (QuiverHecke.truncatedReesScalars datum symmetrizer scalars 3))
    letI := OddMath.Diagrams.Supercategory.restrictScalars ℚ (TruncatedRees.TruncRing ℚ 3)
      (QuiverHecke.H datum (QuiverHecke.truncatedReesScalars datum symmetrizer scalars 3))
    GradedSupercategory ℚ
      (QuiverHecke.H datum (QuiverHecke.truncatedReesScalars datum symmetrizer scalars 3)) :=
  QuiverHecke.truncatedReesGradedSupercategory datum symmetrizer lowerDegree 3

/-- The ELV coefficient category over `ℚ[h]/(h³)` with the truncated Rees parameters and
cutoff `2` is a graded supercategory over `ℚ`. -/
example :
    letI := OddMath.Diagrams.Linear.restrictScalars ℚ (TruncatedRees.TruncRing ℚ 3)
      (QuiverHecke.ELVCoefficientCategory datum
        (QuiverHecke.truncatedReesScalars datum symmetrizer scalars 3) fun _ => 2)
    letI := OddMath.Diagrams.Supercategory.restrictScalars ℚ (TruncatedRees.TruncRing ℚ 3)
      (QuiverHecke.ELVCoefficientCategory datum
        (QuiverHecke.truncatedReesScalars datum symmetrizer scalars 3) fun _ => 2)
    GradedSupercategory ℚ (QuiverHecke.ELVCoefficientCategory datum
      (QuiverHecke.truncatedReesScalars datum symmetrizer scalars 3) fun _ => 2) :=
  letI := QuiverHecke.truncGradedAlgebra ℚ 3
  QuiverHecke.elvHomGradingOver datum symmetrizer (QuiverHecke.truncGrading ℚ 3) _
    (QuiverHecke.isHomogeneous_truncatedRees datum symmetrizer lowerDegree 3) _

#print axioms OddMath.QuiverHecke.elvHomGradingOver
#print axioms OddMath.QuiverHecke.isHomogeneous_rees
#print axioms OddMath.Diagrams.CoefficientGrading.iSupIndep_presentedPart
#print axioms OddMath.QuiverHecke.reesGradedSupercategory
#print axioms OddMath.QuiverHecke.truncatedReesGradedSupercategory

end NonVacuity.CoefficientGrading
