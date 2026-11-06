/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.Graded

/-!
# Restriction of scalars for supercategories

An `R`-linear supercategory is `K`-linear for every `K`-algebra structure on `R`: the Hom
modules are restricted along `algebraMap K R`, and the parity submodules are restricted to
`K`-submodules. This lets a category over a graded ring `R = K[h]/(h^N)`, whose grading is
only `K`-linear, carry a `GradedSupercategory K` structure (route step 2 of
`docs/Nondegeneracy/Phase2Plan.md`, item 2). The structures are definitions, not instances,
so they do not create instance diamonds when `K = R`.

## Main definitions

* `Linear.restrictScalars K R C`: the `K`-linear structure.
* `Supercategory.restrictScalars K R C`: the `K`-linear supercategory structure, with the same
  parity decompositions.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

namespace OddMath.Diagrams

open CategoryTheory StringDiagrams

universe w w' w₁ w₂

variable (K : Type w') [CommRing K] (R : Type w) [CommRing R] [Algebra K R]
  (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C]

/-- An `R`-linear category is `K`-linear by restriction of scalars along `algebraMap K R`. -/
@[reducible]
def Linear.restrictScalars : Linear K C where
  homModule X Y := Module.compHom (X ⟶ Y) (algebraMap K R)
  smul_comp X Y Z r f g := Linear.smul_comp (R := R) X Y Z (algebraMap K R r) f g
  comp_smul X Y Z f r g := Linear.comp_smul (R := R) X Y Z f (algebraMap K R r) g

theorem Linear.restrictScalars_smul {X Y : C} (r : K) (f : X ⟶ Y) :
    letI := Linear.restrictScalars K R C
    r • f = algebraMap K R r • f :=
  rfl

/-- The restricted and the original scalar actions on a Hom module form a scalar tower. -/
theorem Linear.isScalarTower_restrictScalars (X Y : C) :
    letI := Linear.restrictScalars K R C
    IsScalarTower K R (X ⟶ Y) :=
  letI := Linear.restrictScalars K R C
  ⟨fun r s f => by
    change (r • s) • f = algebraMap K R r • s • f
    rw [Algebra.smul_def, mul_smul]⟩

/-- A supercategory over `R` is a supercategory over `K` by restriction of scalars, with the
same parity decompositions. -/
@[reducible]
def Supercategory.restrictScalars [Supercategory R C] :
    letI := Linear.restrictScalars K R C
    Supercategory K C :=
  letI := Linear.restrictScalars K R C
  letI : ∀ X Y : C, IsScalarTower K R (X ⟶ Y) := Linear.isScalarTower_restrictScalars K R C
  { parity := fun X Y p => (Supercategory.parity (R := R) X Y p).restrictScalars K
    isInternal := fun X Y => by
      have h := Supercategory.isInternal (R := R) (C := C) X Y
      rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
      refine ⟨?_, ?_⟩
      · intro p
        have := h.1 p
        rw [Submodule.disjoint_def] at this ⊢
        intro f hf hf'
        refine this f hf ?_
        have hle : (⨆ q, ⨆ (_ : q ≠ p),
            (Supercategory.parity (R := R) X Y q).restrictScalars K) ≤
            (⨆ q, ⨆ (_ : q ≠ p), Supercategory.parity (R := R) X Y q).restrictScalars K :=
          iSup₂_le fun q hq => (Submodule.restrictScalars_mono K
            (le_iSup₂_of_le (f := fun q (_ : q ≠ p) => Supercategory.parity (R := R) X Y q)
              q hq le_rfl))
        exact hle hf'
      · rw [eq_top_iff]
        intro f _
        have hf : f ∈ ⨆ q, Supercategory.parity (R := R) X Y q := h.2 ▸ Submodule.mem_top
        refine Submodule.iSup_induction (Supercategory.parity (R := R) X Y)
          (motive := fun f => f ∈ ⨆ q, (Supercategory.parity (R := R) X Y q).restrictScalars K)
          hf (fun q g hg => ?_) (zero_mem _) (fun _ _ => add_mem)
        exact Submodule.mem_iSup_of_mem
          (p := fun q => (Supercategory.parity (R := R) X Y q).restrictScalars K) q hg
    id_mem := fun X => Supercategory.id_mem (R := R) X
    comp_mem := fun hf hg => Supercategory.comp_mem (R := R) hf hg }

/-- The parity projections of the restricted supercategory are those of the original one. -/
theorem Supercategory.proj_restrictScalars [Supercategory R C] (p : ZMod 2) {X Y : C}
    (f : X ⟶ Y) :
    letI := Linear.restrictScalars K R C
    letI := Supercategory.restrictScalars K R C
    Supercategory.proj K p f = Supercategory.proj R p f := by
  letI := Linear.restrictScalars K R C
  letI := Supercategory.restrictScalars K R C
  exact Supercategory.proj_eq_of_add (R := K)
    (Supercategory.proj_add_proj_add_one (R := R) p f).symm
    (Supercategory.proj_mem (R := R) p f) (Supercategory.proj_mem (R := R) (p + 1) f)

end OddMath.Diagrams
