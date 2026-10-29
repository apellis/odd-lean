/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ReservoirCoefficients
import StringDiagrams.Super.GSBim

/-! # Coefficient bounds from the regular reservoir bimodule

The coefficient grading needed in `SwappedHomInversion.md` §4 does not require a grading
on arbitrary superfunctors. Here the reservoir is a graded superalgebra, while the ambient
2-supercategory is that of **ungraded** superbimodules. Only its regular bimodule is graded.
Evaluation at `1` detects its endomorphisms, so an upper support bound on the algebra proves
the required coefficient bound. Arbitrary source algebras and probe bimodules remain ungraded.

The downstream construction `coefficientIdeal` supplies the jointly nilpotent ideal on this
kernel Hom sector. This is not a construction of the full exterior-deformed factor action,
nor a comparison of its kernel realization with the superfunctor action.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly.RegularReservoir

open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open ProbeWindow

universe u
variable {k : Type u} [CommRing k] (A : GSuperAlg k)

/-- Restrict the integer grading to endomorphisms of the regular bimodule; all other
bimodules in the ambient category may be ungraded. -/
def coeffGrading : CoeffGrading k A.toSuperAlg where
  deg n := {f | f ∈ GradedSuperBimodule.degHom (GradedSuperBimodule.regular A.gsa)
    (GradedSuperBimodule.regular A.gsa) n}
  id_mem := (GradedSuperBimodule.family A.gsa A.gsa).id_mem _
  comp_mem := (GradedSuperBimodule.family A.gsa A.gsa).comp_mem
  proj_mem {_} q {_} hc := (GradedSuperBimodule.family A.gsa A.gsa).proj_mem q hc

/-- Right linearity determines a regular bimodule endomorphism by its value at `1`.
The left action is signed, but the right action is ordinary; no parity sign is dropped. -/
theorem regular_apply (f : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) (x : A) :
    f.1 x = (show A from f.1 (1 : A)) * x := by
  have h := congrArg (fun g => g (1 : A)) (f.2.2 x)
  change f.1 ((1 : A) * x) = (show A from f.1 (1 : A)) * x at h
  simpa only [one_mul] using h

/-- Homogeneity of a closed coefficient is detected at `1`, so it can be checked
inside the reservoir algebra rather than on all vectors of all modules. -/
theorem mem_coeffGrading_iff (n : ℤ) (f : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) :
    f ∈ (coeffGrading A).deg n ↔ (show A from f.1 (1 : A)) ∈ A.degree n := by
  change f ∈ GradedSuperBimodule.degHom (GradedSuperBimodule.regular A.gsa)
    (GradedSuperBimodule.regular A.gsa) n ↔ _
  rw [GradedSuperBimodule.mem_degHom_iff]
  constructor
  · intro hf
    have hh := hf 0 (1 : A) (SetLike.GradedOne.one_mem : (1 : A) ∈ A.degree 0)
    change (show A from f.1 (1 : A)) ∈ A.degree (0 + n) at hh
    simpa only [zero_add] using hh
  · intro hf m x hx
    change (show A from f.1 x) ∈ A.degree (m + n)
    rw [regular_apply A f x]
    rw [add_comm]
    exact SetLike.GradedMul.mul_mem hf hx

/-- Evaluation at `1` is faithful on the closed reservoir coefficients. -/
theorem regular_eq_zero (f : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg)
    (hf : f.1 (1 : A) = 0) : f = 0 := by
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro x
  change f.1 x = 0
  rw [regular_apply A f x, hf, zero_mul]

/-- The algebra support bound, not a bound on arbitrary module Hom spaces, kills
high-degree closed coefficients. -/
theorem coefficient_eq_zero (M : ℕ)
    (hM : ∀ n : ℤ, (M : ℤ) ≤ n → A.degree n = ⊥)
    (n : ℤ) (hn : (M : ℤ) ≤ n)
    (f : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) (hf : f ∈ (coeffGrading A).deg n) : f = 0 := by
  apply regular_eq_zero A f
  change f ∈ GradedSuperBimodule.degHom (GradedSuperBimodule.regular A.gsa)
    (GradedSuperBimodule.regular A.gsa) n at hf
  have h := (GradedSuperBimodule.mem_degHom_iff _).mp hf 0 (1 : A)
    (SetLike.GradedOne.one_mem : (1 : A) ∈ A.degree 0)
  change f.1 (1 : A) ∈ A.degree (0 + n) at h
  simpa [hM n hn] using h

/-- The jointly nilpotent coefficient ideal on all ungraded kernel morphisms into `A`.
The bound is proved from the algebra grading rather than assumed for `End(identity)`. -/
def coefficientIdeal (T : SuperAlg k) (M : ℕ)
    (hM : ∀ n : ℤ, (M : ℤ) ≤ n → A.degree n = ⊥) : CoefficientIdeal (T ⟶ A.toSuperAlg) :=
  reservoirCoefficientIdeal T (coeffGrading A) M (coefficient_eq_zero A M hM)

/-- A closed word contraction has the sum of its kernel degrees. The intermediate
kernels retain their chosen integer shifts; no grading of other bimodules is used. -/
theorem contraction_mem {U V : GradedSuperBimodule A.gsa A.gsa}
    (cup : (GradedSuperBimodule.regular A.gsa).toSuperBimodule ⟶ U.toSuperBimodule)
    (middle : U.toSuperBimodule ⟶ V.toSuperBimodule)
    (cap : V.toSuperBimodule ⟶ (GradedSuperBimodule.regular A.gsa).toSuperBimodule)
    {c d e : ℤ}
    (hc : cup ∈ GradedSuperBimodule.degHom _ _ c)
    (hd : middle ∈ GradedSuperBimodule.degHom _ _ d)
    (he : cap ∈ GradedSuperBimodule.degHom _ _ e) :
    cup ≫ middle ≫ cap ∈ (coeffGrading A).deg (c + (d + e)) :=
  (GradedSuperBimodule.family A.gsa A.gsa).comp_mem hc
    ((GradedSuperBimodule.family A.gsa A.gsa).comp_mem hd he)

/-- The right reservoir closure of `SwappedHomInversion.md` (8) belongs to the
coefficient ideal, retaining the cup/cap shifts `d(h+1+2r)` and `d(1-h+2s)`.
The middle map is the degree-zero inverse component, not an inverse to a bare crossing.
Its construction and its kernel-degree proof are explicit remaining inputs. -/
theorem closure_mem_coefficientIdeal (T : SuperAlg k) (M : ℕ)
    (hM : ∀ n : ℤ, (M : ℤ) ≤ n → A.degree n = ⊥)
    {U V : GradedSuperBimodule A.gsa A.gsa}
    (cup : (GradedSuperBimodule.regular A.gsa).toSuperBimodule ⟶ U.toSuperBimodule)
    (middle : U.toSuperBimodule ⟶ V.toSuperBimodule)
    (cap : V.toSuperBimodule ⟶ (GradedSuperBimodule.regular A.gsa).toSuperBimodule)
    (d h : ℤ) (hd : 0 < d) (r s : ℕ)
    (hc : cup ∈ GradedSuperBimodule.degHom _ _ (d * (h + 1 + 2 * r)))
    (hy : middle ∈ GradedSuperBimodule.degHom _ _ 0)
    (he : cap ∈ GradedSuperBimodule.degHom _ _ (d * (1 - h + 2 * s)))
    {X Z Y : T ⟶ A.toSuperAlg} (f : X ⟶ Z) (g : Z ⟶ Y) :
    (coefficientIdeal A T M hM).mem 1 (f ≫ postCoeff Z (cup ≫ middle ≫ cap) ≫ g) := by
  have hc' := contraction_mem A cup middle cap hc hy he
  have hdegree : d * (h + 1 + 2 * r) + (0 + d * (1 - h + 2 * s)) =
      2 * d * (r + s + 1) := by ring
  rw [hdegree] at hc'
  have hpos : 0 < 2 * d * ((r : ℤ) + s + 1) := by positivity
  exact comp_postCoeff_comp_mem (Gr := coeffGrading A) (by omega) hc' f g

/-- Matrix lifting on ungraded kernel windows, with the zeroth-ideal membership of the
comparison inverse discharged. This uses joint ideal nilpotence, not entrywise nilpotence. -/
theorem isIso_of_coefficient_error (T : SuperAlg k) (M : ℕ)
    (hM : ∀ n : ℤ, (M : ℤ) ≤ n → A.degree n = ⊥)
    {X Y : Mat_ (T ⟶ A.toSuperAlg)} (F G : X ⟶ Y) [IsIso G]
    (hFG : ∀ i j, (F - G) i j ∈ coeffIdeal (coeffGrading A) 1 _ _) : IsIso F :=
  (coefficientIdeal A T M hM).isIso_of_sub_mem F G
    (fun _ _ => mem_coeffIdeal_zero _) hFG

end OddMath.QuiverHecke.SwappedAssembly.RegularReservoir
