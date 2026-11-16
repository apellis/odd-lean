/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Diagrams.BoxProductCoefficientGraded
import StringDiagrams.Super.GSMod

/-!
# Superalgebras over a graded base ring as graded supercategories

Let `R` be a commutative `K`-algebra and `A` an `R`-superalgebra with parity `𝒬`. A grading
`𝒟 : ℤ → Submodule K A` of `A` as a `K`-algebra whose parts are stable under the parity
projections makes the one-object supercategory `SuperalgebraCat 𝒬`, with scalars restricted to
`K`, a graded supercategory over `K` (`SuperalgebraCatOver.gradedSupercategory`). If moreover
`R` is graded by `𝒜` and `𝒜 e • 𝒟 n ⊆ 𝒟 (e + n)`, the degree parts satisfy the coefficient
compatibility of `BoxProdCoefficient.gradedSupercategory` (membership is `mem_homDegree`).

For `K = R` this is `SuperalgebraCat.instGradedSupercategory`. It grades the coefficient factor of
the ELV coefficient category over a graded base ring (`docs/Nondegeneracy/Phase2Plan.md`, step 2).
-/

noncomputable section

namespace OddMath.Diagrams.SuperalgebraCatOver

open CategoryTheory StringDiagrams Supercategory GradedSupercategory DirectSum

universe u

variable {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  {A : Type u} [Ring A] [Algebra R A] [Algebra K A] [IsScalarTower K R A]
  (𝒬 : ZMod 2 → Submodule R A) [GradedAlgebra 𝒬]

/-- The degree-`n` part of a Hom module of `SuperalgebraCat 𝒬`, for the restricted scalars. -/
def homDegree (𝒟 : ℤ → Submodule K A) (X Y : SuperalgebraCat 𝒬) (n : ℤ) :
    letI := Linear.restrictScalars K R (SuperalgebraCat 𝒬)
    Submodule K (X ⟶ Y) :=
  letI := Linear.restrictScalars K R (SuperalgebraCat 𝒬)
  { carrier := {f | SuperalgebraCat.toElem f ∈ 𝒟 n}
    add_mem' := fun {f g} hf hg => by
      change SuperalgebraCat.toElem (f + g) ∈ 𝒟 n
      rw [SuperalgebraCat.toElem_add]
      exact add_mem hf hg
    zero_mem' := zero_mem (𝒟 n)
    smul_mem' := fun r f hf => by
      change algebraMap K R r • SuperalgebraCat.toElem f ∈ 𝒟 n
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ r hf }

variable {𝒬} {𝒟 : ℤ → Submodule K A}

omit [GradedAlgebra 𝒬] in
theorem mem_homDegree {X Y : SuperalgebraCat 𝒬} {n : ℤ} {f : X ⟶ Y} :
    f ∈ homDegree (K := K) 𝒬 𝒟 X Y n ↔ SuperalgebraCat.toElem f ∈ 𝒟 n :=
  Iff.rfl

omit [Algebra K A] [IsScalarTower K R A] in
theorem mem_parity_restrict {X Y : SuperalgebraCat 𝒬} {p : ZMod 2} {f : X ⟶ Y} :
    letI := Linear.restrictScalars K R (SuperalgebraCat 𝒬)
    letI := Supercategory.restrictScalars K R (SuperalgebraCat 𝒬)
    f ∈ parity (R := K) X Y p ↔ f ∈ parity (R := R) X Y p :=
  Iff.rfl

variable (𝒬 𝒟) [GradedAlgebra 𝒟]
  (hdec : ∀ {n : ℤ} {a : A} (p : ZMod 2), a ∈ 𝒟 n → (decompose 𝒬 a p : A) ∈ 𝒟 n)

/-- **Graded supercategory over `K`.** -/
@[instance_reducible]
def gradedSupercategory :
    letI := Linear.restrictScalars K R (SuperalgebraCat 𝒬)
    letI := Supercategory.restrictScalars K R (SuperalgebraCat 𝒬)
    GradedSupercategory K (SuperalgebraCat 𝒬) :=
  letI := Linear.restrictScalars K R (SuperalgebraCat 𝒬)
  letI := Supercategory.restrictScalars K R (SuperalgebraCat 𝒬)
  { degree := homDegree 𝒬 𝒟
    isInternal_degree := fun _ _ =>
      BoxProdCoefficient.isInternal_of_mem_iff (fun _ _ => mem_homDegree.symm)
        (Decomposition.isInternal 𝒟)
    proj_mem_degree := fun {X Y n f} p hf => by
      rw [BoxProdCoefficient.proj_eq_proj (R := R) (fun _ _ _ _ => mem_parity_restrict) p f,
        SuperalgebraCat.proj_eq_decompose]
      exact hdec p hf
    id_mem_degree := fun _ => mem_homDegree.2 (SetLike.GradedOne.one_mem (A := 𝒟))
    comp_mem_degree := fun hf hg => mem_homDegree.2 (by
      rw [SuperalgebraCat.toElem_comp, add_comm]
      exact SetLike.GradedMul.mul_mem (A := 𝒟) (mem_homDegree.1 hg) (mem_homDegree.1 hf)) }

end OddMath.Diagrams.SuperalgebraCatOver
