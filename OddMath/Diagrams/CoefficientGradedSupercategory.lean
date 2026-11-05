/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Diagrams.CoefficientGrading
import OddMath.Diagrams.RestrictScalars

/-!
# Graded supercategories from coefficient-graded presentations

Let `R` be a `K`-algebra graded by `𝒜 : ℤ → Submodule K R`, and let `P` be a presentation over
`R` that is parity homogeneous and coefficient-graded homogeneous (`CoefficientGrading`). The
presented category is an `R`-linear supercategory, hence a `K`-linear one by restriction of
scalars; its Hom groups are graded by `CoefficientGrading.presentedPart`. These parts are
`K`-submodules, and they make the presented category a `GradedSupercategory K`. The grading is
not `R`-linear when `𝒜` has positive-degree elements, which is why the base is `K`.

This is route step 2 of `docs/Nondegeneracy/Phase2Plan.md`: the quiver Hecke category over
the truncated Rees ring `K[h]/(h^N)`, with `h` in positive degree, is the intended instance.

## Main definitions and results

* `CoefficientGrading.homogeneousComponent_mem_part`: parity components preserve coefficient
  degrees.
* `CoefficientGrading.presentedSubmodule`: the degree-`d` part as a `K`-submodule.
* `CoefficientGrading.gradedSupercategory`: the graded supercategory structure over `K`.
-/

noncomputable section

namespace OddMath.Diagrams.CoefficientGrading

open CategoryTheory StringDiagrams

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {K : Type*} [CommRing K] {R : Type w} [CommRing R]
  [Algebra K R] {𝒜 : ℤ → Submodule K R} {deg : S.Gen → ℤ}

variable {a b : Obj S}

/-- The parity components of a combination of diagrams preserve its coefficient degree. -/
theorem homogeneousComponent_mem_part (p : ZMod 2) {f : LinDiagram R a b} {d : ℤ}
    (hf : f ∈ part 𝒜 deg a b d) :
    LinDiagram.homogeneousComponent (Presentation.parityDeg S) p f ∈ part 𝒜 deg a b d := by
  intro g
  rw [LinDiagram.homogeneousComponent_apply]
  erw [Finsupp.filter_apply]
  split_ifs
  · exact hf g
  · exact zero_mem _

/-- A supremum of submodules lies in the supremum of the underlying additive subgroups. -/
theorem toAddSubgroup_iSup_le {M : Type*} [AddCommGroup M] [Module K M] {ι : Sort*}
    (N : ι → Submodule K M) : (⨆ i, N i).toAddSubgroup ≤ ⨆ i, (N i).toAddSubgroup := by
  intro x hx
  refine Submodule.iSup_induction N (motive := fun y => y ∈ ⨆ i, (N i).toAddSubgroup) hx
    (fun i y hy => AddSubgroup.mem_iSup_of_mem i hy) (zero_mem _) (fun _ _ => add_mem)

variable [GradedAlgebra 𝒜] (P : Presentation.{w, v} S R)

/-- The degree-`d` part of a Hom group of the presented category, as a `K`-submodule for the
restricted scalar action. -/
def presentedSubmodule (a b : Obj S) (d : ℤ) :
    letI := Linear.restrictScalars K R P.Presented
    Submodule K (P.obj a ⟶ P.obj b) :=
  letI := Linear.restrictScalars K R P.Presented
  { presentedPart 𝒜 deg P a b d with
    smul_mem' := fun r x hx => by
      change algebraMap K R r • x ∈ presentedPart 𝒜 deg P a b d
      exact smul_mem_presentedPart (SetLike.algebraMap_mem_graded 𝒜 r) hx }

variable {P}

omit [GradedAlgebra 𝒜] in
/-- Parity components in the presented category preserve coefficient degrees. -/
theorem presented_homogeneousComponent_mem (hpar : P.IsParityHomogeneous) (p : ZMod 2)
    {x : P.obj a ⟶ P.obj b} {d : ℤ} (hx : x ∈ presentedPart 𝒜 deg P a b d) :
    Presentation.homogeneousComponent hpar p x ∈ presentedPart 𝒜 deg P a b d := by
  obtain ⟨f, hf, rfl⟩ := mem_presentedPart_iff.mp hx
  rw [Presentation.homogeneousComponent_lin]
  exact lin_mem_presentedPart (homogeneousComponent_mem_part p hf)

/-- The parity projections of the restricted supercategory are the diagram parity
components. -/
theorem proj_eq_homogeneousComponent (hpar : P.IsParityHomogeneous) {X Y : P.Presented}
    (p : ZMod 2) (f : X ⟶ Y) :
    letI := Linear.restrictScalars K R P.Presented
    letI := P.supercategory hpar
    letI := Supercategory.restrictScalars K R P.Presented
    Supercategory.proj K p f = Presentation.homogeneousComponent hpar p f := by
  let := Linear.restrictScalars K R P.Presented
  let := P.supercategory hpar
  let := Supercategory.restrictScalars K R P.Presented
  refine Supercategory.induction_on (R := K) f ?_ ?_ ?_
  · exact (map_zero _).trans (map_zero (Presentation.homogeneousComponent hpar p)).symm
  · intro q g hg
    by_cases hq : q = p
    · subst hq
      exact (Supercategory.proj_of_mem hg).trans
        (Presentation.homogeneousComponent_of_mem hpar hg).symm
    · exact (Supercategory.proj_of_mem_ne hg hq).trans
        (Presentation.homogeneousComponent_of_mem_of_ne hpar hg hq).symm
  · intro g h hg hh
    exact ((map_add _ g h).trans (congrArg₂ (· + ·) hg hh)).trans
      (map_add (Presentation.homogeneousComponent hpar p) g h).symm

theorem toAddSubgroup_presentedSubmodule (a b : Obj S) (d : ℤ) :
    (presentedSubmodule (𝒜 := 𝒜) (deg := deg) P a b d).toAddSubgroup =
      presentedPart 𝒜 deg P a b d :=
  rfl

/-- The degree parts of a Hom group are a direct sum decomposition over `K`. -/
theorem isInternal_presentedSubmodule (hP : IsHomogeneous 𝒜 deg P) (a b : Obj S) :
    letI := Linear.restrictScalars K R P.Presented
    DirectSum.IsInternal (presentedSubmodule (𝒜 := 𝒜) (deg := deg) P a b) := by
  let := Linear.restrictScalars K R P.Presented
  set N := presentedSubmodule (𝒜 := 𝒜) (deg := deg) P a b with hN
  have hG : ∀ d, (N d).toAddSubgroup = presentedPart 𝒜 deg P a b d := fun d => rfl
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun d => ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 : x ∈ ⨆ e, (⨆ (_ : e ≠ d), N e).toAddSubgroup := toAddSubgroup_iSup_le _ hx'
    have hle : ⨆ e, (⨆ (_ : e ≠ d), N e).toAddSubgroup ≤
        ⨆ (e) (_ : e ≠ d), presentedPart 𝒜 deg P a b e :=
      iSup_mono fun e => by simpa only [hG] using toAddSubgroup_iSup_le (fun (_ : e ≠ d) => N e)
    have h2 := hle h1
    have hx0 : x ∈ presentedPart 𝒜 deg P a b d := by rw [← hG]; exact hx
    exact (AddSubgroup.disjoint_def.mp (iSupIndep_presentedPart hP a b d)) hx0 h2
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ d, presentedPart 𝒜 deg P a b d := by
      rw [iSup_presentedPart 𝒜 deg P a b]; exact AddSubgroup.mem_top x
    refine AddSubgroup.iSup_induction (presentedPart 𝒜 deg P a b)
      (C := fun y => y ∈ ⨆ d, N d) hx (fun d y hy => ?_) (zero_mem _) (fun _ _ => add_mem)
    have hy' : y ∈ N d := by rw [← SetLike.mem_coe, ← Submodule.coe_toAddSubgroup, hG]; exact hy
    exact Submodule.mem_iSup_of_mem d hy'

omit [GradedAlgebra 𝒜] in
theorem id_mem_presentedPart [SetLike.GradedMonoid 𝒜] (a : Obj S) :
    𝟙 (P.obj a) ∈ presentedPart 𝒜 deg P a a 0 := by
  rw [← P.lin_id]
  exact lin_mem_presentedPart (of_mem_part' (𝒜 := 𝒜) (deg := deg) (𝟙 a)
    (Diagram.degree_id deg a))

omit [GradedAlgebra 𝒜] in
theorem comp_mem_presentedPart [SetLike.GradedMonoid 𝒜] {c : Obj S} {x : P.obj a ⟶ P.obj b}
    {y : P.obj b ⟶ P.obj c} {m n : ℤ} (hx : x ∈ presentedPart 𝒜 deg P a b m)
    (hy : y ∈ presentedPart 𝒜 deg P b c n) : x ≫ y ∈ presentedPart 𝒜 deg P a c (m + n) := by
  obtain ⟨f, hf, rfl⟩ := mem_presentedPart_iff.mp hx
  obtain ⟨g, hg, rfl⟩ := mem_presentedPart_iff.mp hy
  rw [← P.lin_comp]
  exact lin_mem_presentedPart (comp_mem_part hf hg)

/-- **Graded supercategory over the degree-zero ring.** A parity homogeneous presentation over
a `ℤ`-graded `K`-algebra `R` whose relations are coefficient-graded homogeneous presents a
graded supercategory over `K`. -/
@[instance_reducible]
def gradedSupercategory (hpar : P.IsParityHomogeneous) (hP : IsHomogeneous 𝒜 deg P) :
    letI := Linear.restrictScalars K R P.Presented
    letI := P.supercategory hpar
    letI := Supercategory.restrictScalars K R P.Presented
    GradedSupercategory K P.Presented :=
  letI := Linear.restrictScalars K R P.Presented
  letI := P.supercategory hpar
  letI := Supercategory.restrictScalars K R P.Presented
  { degree := fun X Y n => presentedSubmodule (𝒜 := 𝒜) (deg := deg) P X.as Y.as n
    isInternal_degree := fun X Y => isInternal_presentedSubmodule hP X.as Y.as
    proj_mem_degree := fun {X Y n f} p hf => by
      rw [proj_eq_homogeneousComponent hpar]
      exact presented_homogeneousComponent_mem hpar p hf
    id_mem_degree := fun X => id_mem_presentedPart (𝒜 := 𝒜) (deg := deg) X.as
    comp_mem_degree := fun hf hg => comp_mem_presentedPart hf hg }

end OddMath.Diagrams.CoefficientGrading
