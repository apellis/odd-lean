/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Basis
import OddMath.QuiverHecke.Grading
import OddMath.QuiverHecke.Envelope

/-!
# Graded pieces of the Hom spaces of `H`

The normal forms `x^l ψ_w : t → t'` (`OddMath.QuiverHecke.Basis`) are homogeneous for the
integer grading and the parity of the quiver Hecke supercategory `H` (Brundan–Ellis,
arXiv:1701.04133v2, §11): `x^l ψ_w` has degree `NFIdx.deg` and parity `NFIdx.par`, the sums
over its generators (`NFIdx.nf_mem_homDegree`, `NFIdx.nf_mem_parity`). Hence the piece of
`Hom_H(t, t')` of degree `n` and parity `p` is spanned by the normal forms of that degree and
parity (`homPiece_eq_span`).

Each dot has degree `2 d_i ≥ 2`, so a normal form of degree `n` has at most a bounded number of
dots, and there are only finitely many normal forms of each degree (`finite_deg_eq`). Over a
field, the piece of degree `n` and parity `p` is therefore finite dimensional, of dimension the
number of normal forms of that degree and parity (`finrank_homPiece`). These numbers are the
coefficients of the graded dimensions that enter the categorical pairing of BE2 §11 (Hill–Wang,
arXiv:1202.2769v2, Proposition 6.8).
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams Module

universe u v w

section Generic

variable {k M ι Γ : Type*} [Semiring k] [AddCommMonoid M] [Module k M] [DecidableEq Γ]
  (ℳ : Γ → Submodule k M) [DirectSum.Decomposition ℳ] {b : ι → M} (deg : ι → Γ)

/-- The homogeneous components of an element of the span of homogeneous elements lie in the
span of those of the right degree. -/
theorem decompose_mem_span_of_homogeneous (hdeg : ∀ x, b x ∈ ℳ (deg x)) (S : Set ι) {y : M}
    (hy : y ∈ Submodule.span k (b '' S)) (d : Γ) :
    (DirectSum.decompose ℳ y d : M) ∈ Submodule.span k (b '' {x | x ∈ S ∧ deg x = d}) := by
  classical
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    by_cases h : deg x = d
    · rw [DirectSum.decompose_of_mem_same _ (h ▸ hdeg x)]
      exact Submodule.subset_span ⟨x, ⟨hx, h⟩, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne _ (hdeg x) h]
      exact zero_mem _
  | zero => simp
  | add y z _ _ hy hz =>
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [DirectSum.decompose_smul, DFinsupp.smul_apply, Submodule.coe_smul]
    exact Submodule.smul_mem _ c hy

/-- For a grading by any index type: the degree-`d` part of the span of homogeneous elements is
spanned by those of degree `d`. -/
theorem inf_span_eq_of_homogeneous (hdeg : ∀ x, b x ∈ ℳ (deg x)) (S : Set ι) (d : Γ) :
    ℳ d ⊓ Submodule.span k (b '' S) = Submodule.span k (b '' {x | x ∈ S ∧ deg x = d}) := by
  apply le_antisymm
  · rintro y ⟨hyd, hyS⟩
    have := decompose_mem_span_of_homogeneous ℳ deg hdeg S hyS d
    rwa [DirectSum.decompose_of_mem_same _ hyd] at this
  · refine le_inf (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono fun x hx => hx.1))
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact hx ▸ hdeg x

end Generic

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)

/-- The positioned generators of a normal form: its dots, then the crossings of the canonical
reduced word. -/
def NFIdx.gens {t t' : List I} (i : NFIdx t t') : List PG :=
  i.1.1.map PG.dot ++ cw (Categorification.TypeA.canWord t.length i.1.2)

/-- The degree of a normal form. -/
def NFIdx.deg {t t' : List I} (i : NFIdx t t') : ℤ := gsum D sy (pl t i.gens)

/-- The parity of a normal form. -/
def NFIdx.par {t t' : List I} (i : NFIdx t t') : ZMod 2 :=
  ((pl t i.gens).map fun x => x.2.1.parity D).sum

theorem NFIdx.nf_mem_homDegree {t t' : List I} (i : NFIdx t t') :
    i.nf (D := D) (Sc := Sc) ∈ homDegree D sy Sc t t' (i.deg D sy) :=
  Presentation.diag_mem_homDeg' (degree_gdeg_mkD D sy _ _)

theorem NFIdx.nf_mem_parity {t t' : List I} (i : NFIdx t t') :
    i.nf (D := D) (Sc := Sc) ∈
      (pres D Sc).homDeg (Presentation.parityDeg (sig D)) (ob D t) (ob D t') (i.par D) :=
  Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)

/-- A dot on strand `p < |t|` has degree `2 d_{t_p} ≥ 2`. -/
theorem two_mul_length_le_gsum_dots (t : List I) (l : List ℕ) (hl : ∀ x ∈ l, x < t.length) :
    2 * (l.length : ℤ) ≤ gsum D sy (pl t (l.map PG.dot)) := by
  induction l with
  | nil => simp [gsum]
  | cons p l ih =>
    have hp : p < t.length := hl p (by simp)
    rw [List.map_cons, pl_cons, gsum_append]
    have hrest := ih fun x hx => hl x (by simp [hx])
    obtain ⟨x, r, h⟩ : ∃ x r, t.drop p = x :: r := by
      cases h : t.drop p with
      | nil => rw [List.drop_eq_nil_iff] at h; omega
      | cons x r => exact ⟨x, r, rfl⟩
    have hld : (PG.dot p).ld t = [(t.take p, Shape.dot x, r)] := by simp [PG.ld, h]
    have hact : (PG.dot p).act t = t := rfl
    rw [hld, hact]
    have hx := sy.pos x
    simp only [gsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, gdeg,
      List.length_cons] at hrest ⊢
    push_cast
    linarith

/-- The degree of a normal form splits into its dots and its crossings. -/
theorem NFIdx.deg_eq {t t' : List I} (i : NFIdx t t') :
    i.deg D sy = gsum D sy (pl t (i.1.1.map PG.dot)) +
      gsum D sy (pl t (cw (Categorification.TypeA.canWord t.length i.1.2))) := by
  rw [NFIdx.deg, NFIdx.gens, pl_append, gsum_append, tgt_map_dot]

/-- **Finitely many normal forms in each degree.** -/
theorem finite_deg_eq (t t' : List I) (n : ℤ) : {i : NFIdx t t' | i.deg D sy = n}.Finite := by
  classical
  let c : Equiv.Perm (Fin t.length) → ℤ := fun w =>
    gsum D sy (pl t (cw (Categorification.TypeA.canWord t.length w)))
  let B : ℕ := Finset.univ.sup fun w => (n - c w).toNat
  let S : Set (List ℕ × Equiv.Perm (Fin t.length)) :=
    ((fun l : List (Fin t.length) => l.map Fin.val) '' {l | l.length ≤ B}) ×ˢ Set.univ
  have hS : S.Finite := ((List.finite_length_le _ B).image _).prod Set.finite_univ
  refine (hS.preimage (Subtype.val_injective.injOn)).subset ?_
  intro i hi
  change NFIdx.deg D sy i = n at hi
  have hlt := i.2.2.1
  have hdots := two_mul_length_le_gsum_dots D sy t i.1.1 hlt
  rw [NFIdx.deg_eq] at hi
  have hB : (n - c i.1.2).toNat ≤ B :=
    Finset.le_sup (f := fun w => (n - c w).toNat) (Finset.mem_univ _)
  refine ⟨⟨i.1.1.pmap (fun x hx => (⟨x, hx⟩ : Fin t.length)) hlt, ?_, ?_⟩, Set.mem_univ _⟩
  · change (List.pmap _ _ _).length ≤ B
    rw [List.length_pmap]
    have : (i.1.1.length : ℤ) ≤ (n - c i.1.2).toNat := by
      have := Int.self_le_toNat (n - c i.1.2)
      have hc : c i.1.2 =
          gsum D sy (pl t (cw (Categorification.TypeA.canWord t.length i.1.2))) := rfl
      omega
    omega
  · simp [List.map_pmap]

variable (hc : Sc.Homogeneous)

/-- The piece of `Hom_H(t, t')` of degree `n` and parity `p`. -/
abbrev homPiece (t t' : List I) (n : ℤ) (p : ZMod 2) :
    Submodule k (hObj D Sc sy hc t ⟶ hObj D Sc sy hc t') :=
  GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc) _ _ n ⊓
    Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _ p

/-- **The graded pieces of `Hom_H(t, t')`** are spanned by the normal forms of that degree and
parity. -/
theorem homPiece_eq_span (t t' : List I) (n : ℤ) (p : ZMod 2) :
    homPiece D Sc sy hc t t' n p = Submodule.span k
      ((fun i : NFIdx t t' => (i.nf (D := D) (Sc := Sc) : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'))
        '' {i | i.par D = p ∧ i.deg D sy = n}) := by
  classical
  let _ : DirectSum.Decomposition
      (Supercategory.parity (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t)
        (hObj D Sc sy hc t')) :=
    (Supercategory.isInternal (R := k) (C := HGr D Sc sy hc) _ _).chooseDecomposition
  let _ : DirectSum.Decomposition
      (GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t)
        (hObj D Sc sy hc t')) :=
    (GradedSupercategory.isInternal_degree (R := k) (C := HGr D Sc sy hc) _ _).chooseDecomposition
  have hspan : Submodule.span k
      (Set.range fun i : NFIdx t t' => (i.nf (D := D) (Sc := Sc) :
        hObj D Sc sy hc t ⟶ hObj D Sc sy hc t')) = ⊤ := span_nf D Sc t t'
  have hpar := inf_span_eq_of_homogeneous
    (Supercategory.parity (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t) (hObj D Sc sy hc t'))
    (b := fun i : NFIdx t t' => (i.nf (D := D) (Sc := Sc) :
        hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'))
    (fun i => i.par D) (fun i => i.nf_mem_parity D Sc) Set.univ p
  rw [Set.image_univ, hspan, inf_top_eq] at hpar
  have hdeg := inf_span_eq_of_homogeneous
    (GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t)
      (hObj D Sc sy hc t'))
    (b := fun i : NFIdx t t' => (i.nf (D := D) (Sc := Sc) :
        hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'))
    (fun i => i.deg D sy) (fun i => i.nf_mem_homDegree D Sc sy)
    {x | x ∈ Set.univ ∧ x.par D = p} n
  rw [homPiece, hpar, hdeg]
  congr 2
  ext i
  simp

section Field

variable {K : Type w} [Field K] (Sc : SKM.Scalars D K) (hc : Sc.Homogeneous)

theorem finite_par_deg (t t' : List I) (n : ℤ) (p : ZMod 2) :
    {i : NFIdx t t' | i.par D = p ∧ i.deg D sy = n}.Finite :=
  (finite_deg_eq D sy t t' n).subset fun _ hi => hi.2

/-- The graded pieces of `Hom_H(t, t')` are finite dimensional. -/
instance finiteDimensional_homPiece (t t' : List I) (n : ℤ) (p : ZMod 2) :
    FiniteDimensional K (homPiece D Sc sy hc t t' n p) := by
  rw [homPiece_eq_span]
  exact FiniteDimensional.span_of_finite K ((finite_par_deg D sy t t' n p).image _)

/-- **The dimension of a graded piece of `Hom_H(t, t')`** is the number of normal forms of that
degree and parity. -/
theorem finrank_homPiece (t t' : List I) (n : ℤ) (p : ZMod 2) :
    finrank K (homPiece D Sc sy hc t t' n p) =
      Nat.card {i : NFIdx t t' | i.par D = p ∧ i.deg D sy = n} := by
  rw [homPiece_eq_span]
  have := (finite_par_deg D sy t t' n p).fintype
  rw [Set.image_eq_range]
  exact (finrank_span_eq_card ((linearIndependent_nf D Sc t t').comp _
    Subtype.val_injective)).trans Nat.card_eq_fintype_card.symm

end Field

end OddMath.QuiverHecke
