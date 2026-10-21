/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.FiniteHomMatrix
import StringDiagrams.Super.Graded

/-! # Entrywise gradings of finite-support Hom matrices

This supplies the integer and parity grading for BE2, arXiv:1701.04133v2,
§11's algebra `H_n`, without imposing a finite object set.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams
namespace OddMath.FiniteHomMatrix
universe u v w t z
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] {J : Type t} {obj : J → C}
  {Γ : Type z}

/-- Matrices whose entries lie in the specified homogeneous submodules. -/
def component (G : (p : J × J) → Γ → Submodule k (obj p.2 ⟶ obj p.1))
    (d : Γ) : Submodule k (Mat obj) where
  carrier := {a | ∀ p, a p ∈ G p d}
  zero_mem' := fun p => (G p d).zero_mem
  add_mem' ha hb p := (G p d).add_mem (ha p) (hb p)
  smul_mem' r _ ha p := (G p d).smul_mem r (ha p)

@[simp] theorem mem_component (G : (p : J × J) → Γ → Submodule k (obj p.2 ⟶ obj p.1))
    (d : Γ) (a : Mat obj) : a ∈ component G d ↔ ∀ p, a p ∈ G p d := Iff.rfl

theorem single_mem_component {G : (p : J × J) → Γ → Submodule k (obj p.2 ⟶ obj p.1)}
    {d : Γ} (i j : J) {f : obj j ⟶ obj i} (hf : f ∈ G (i,j) d) :
    single i j f ∈ component G d := by
  intro p
  by_cases h : p = (i,j)
  · subst p; simpa [single] using hf
  · simp [single, DFinsupp.single_eq_of_ne h]

/-- Entrywise direct-sum gradings remain internal on finite-support matrices. -/
theorem isInternal_component [DecidableEq Γ]
    (G : (p : J × J) → Γ → Submodule k (obj p.2 ⟶ obj p.1))
    (hG : ∀ p, DirectSum.IsInternal (G p)) : DirectSum.IsInternal (component G) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s a ha hz d hd
    ext p
    have h := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (G p)).mp
      (hG p).submodule_iSupIndep s (fun d => a d p) (fun d hd => ha d hd p)
    apply h _ d hd
    simpa using congrArg (fun a : Mat obj => a p) hz
  · apply top_le_iff.mp
    intro a ha
    clear ha
    induction a using induction with
    | hz => exact Submodule.zero_mem _
    | ha a b ha hb => exact Submodule.add_mem _ ha hb
    | hs i j f =>
      let := (hG (i,j)).chooseDecomposition
      apply DirectSum.Decomposition.inductionOn (G (i,j)) (motive := fun f =>
        single i j f ∈ ⨆ d, component G d) ?_ ?_ ?_ f
      · simp [single]
      · intro d f
        exact (le_iSup (component G) d) (single_mem_component i j f.property)
      · intro f g hf hg
        simpa [single, DFinsupp.single_add] using (⨆ d, component G d).add_mem hf hg

/-- Expand a matrix as the finite sum of its entries. -/
theorem eq_sum_single (a : Mat obj) :
    a = ∑ p ∈ a.support, single p.1 p.2 (a p) := DFinsupp.sum_single.symm

/-- Entrywise homogeneous multiplication is inherited from composition. -/
theorem mul_mem_component [AddCommMonoid Γ]
    (G : (p : J × J) → Γ → Submodule k (obj p.2 ⟶ obj p.1))
    (hcomp : ∀ i j l d e (f : obj j ⟶ obj i) (g : obj l ⟶ obj j),
      f ∈ G (i,j) d → g ∈ G (j,l) e → g ≫ f ∈ G (i,l) (d + e))
    {d e : Γ} {a b : Mat obj} (ha : a ∈ component G d) (hb : b ∈ component G e) :
    a * b ∈ component G (d + e) := by
  rw [eq_sum_single a, eq_sum_single b, Finset.sum_mul]
  apply Submodule.sum_mem
  intro p _
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  rintro ⟨l,m⟩ _
  obtain ⟨i,j⟩ := p
  by_cases h : j = l
  · subst l
    rw [single_mul_single]
    exact single_mem_component i m (hcomp i j m d e _ _ (ha (i,j)) (hb (j,m)))
  · rw [single_mul_single_of_ne i j l m h]
    exact Submodule.zero_mem _

section Super
variable [Supercategory k C] [GradedSupercategory k C]

/-- The integer homogeneous pieces. -/
abbrev degree (d : ℤ) : Submodule k (Mat obj) :=
  component (fun p => GradedSupercategory.degree (R := k) (obj p.2) (obj p.1)) d

/-- The independent parity pieces. -/
abbrev parity (p : ZMod 2) : Submodule k (Mat obj) :=
  component (fun q => Supercategory.parity (R := k) (obj q.2) (obj q.1)) p

/-- Simultaneous degree and parity, with their internal direct-sum decomposition. -/
abbrev bidegree (d : ℤ × ZMod 2) : Submodule k (Mat obj) :=
  component (fun p => GradedSupercategory.bidegree (R := k) (obj p.2) (obj p.1)) d

theorem isInternal_bidegree : DirectSum.IsInternal (bidegree (k := k) (obj := obj)) :=
  isInternal_component _ fun _ => GradedSupercategory.isInternal_bigrading _ _

theorem mul_mem_bidegree {d e : ℤ × ZMod 2} {a b : Mat obj}
    (ha : a ∈ bidegree (k := k) d) (hb : b ∈ bidegree (k := k) e) :
    a * b ∈ bidegree (k := k) (d + e) := by
  apply mul_mem_component _ _ ha hb
  intro i j l d e f g hf hg
  exact ⟨by simpa [add_comm] using GradedSupercategory.comp_mem_degree hg.1 hf.1,
    by simpa [add_comm] using Supercategory.comp_mem hg.2 hf.2⟩

theorem idem_mem_bidegree (i : J) : idem (obj := obj) i ∈ bidegree (k := k) (0,0) :=
  single_mem_component i i ⟨GradedSupercategory.id_mem_degree _, Supercategory.id_mem _⟩

theorem localUnit_mem_bidegree (s : Finset J) :
    localUnit (obj := obj) s ∈ bidegree (k := k) (0,0) :=
  Submodule.sum_mem _ fun i _ => idem_mem_bidegree i

end Super
end OddMath.FiniteHomMatrix
