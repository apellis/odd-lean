/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Calculus
import StringDiagrams.Biadjunction.Zigzag

/-!
# The defining relations of `𝔘(𝔤)` in normal form

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5,
(1.7)–(1.14): each relation of `pres D Sc` as an equation between classes `cl` of normal-form
diagrams, ready for rewriting in context with `cl_step`, `cl_stepL` (`OddMath.SKM.Calculus`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

theorem lin_idg (μ : X) (t : List (Letter I)) :
    (pres D Sc).lin (idg (k := k) D μ t) = cl D Sc μ t t [] := by
  rw [cl_nil]; exact (pres D Sc).diag_id _

theorem lin_sum {a b : Obj (sig D)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    (pres D Sc).lin (∑ i ∈ s, f i) = ∑ i ∈ s, (pres D Sc).lin (f i) :=
  (pres D Sc).linFunctor.map_sum _ _


/-- Unfold a relation of `pres D Sc` into classes of normal-form diagrams. -/
macro "skm_rel_simp " h:ident : tactic =>
  `(tactic| simp only [relation, lin_sub, lin_add, lin_neg, lin_smul, lin_dg, lin_idg, lin_sum,
    Rel.ν, Rel.dom, Rel.cod, List.nil_append, List.append_nil, List.cons_append,
    List.singleton_append] at $h:ident)

variable (Sc)

/-- The relation `r` holds in `𝔘(𝔤)`. -/
theorem lin_relation (r : Rel D) : (pres D Sc).lin (relation D Sc r) = 0 :=
  (pres D Sc).lin_rel_self r

/-! ## Right adjunction (1.10) -/

/-- (1.10), first relation: `(ε ⊗ 1) ∘ (1 ⊗ η) = 1` on `Eᵢ`. -/
theorem cl_zigE (i : I) (ν : X) :
    cl D Sc ν [up i] [up i] [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])] =
      cl D Sc ν [up i] [up i] [] := by
  have := lin_relation Sc (.zigE i ν)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

/-- (1.10), second relation: `(1 ⊗ ε) ∘ (η ⊗ 1) = 1` on `Fᵢ`. -/
theorem cl_zigF (i : I) (ν : X) :
    cl D Sc ν [dn i] [dn i] [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])] =
      cl D Sc ν [dn i] [dn i] [] := by
  have := lin_relation Sc (.zigF i ν)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

/-! ## Quiver Hecke superalgebra relations (1.7)–(1.9) -/

theorem cl_quadEq (i : I) (ν : X) :
    cl D Sc ν [up i, up i] [up i, up i] (crossL [] i i [] ++ crossL [] i i []) = 0 := by
  have := lin_relation Sc (.quadEq i ν)
  skm_rel_simp this
  exact this

theorem cl_quadZero (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j = 0) :
    cl D Sc ν [up i, up j] [up i, up j] (crossL [] i j [] ++ crossL [] j i []) =
      (Sc.t i j : k) • cl D Sc ν [up i, up j] [up i, up j] [] := by
  have := lin_relation Sc (.quadZero i j ν hij hd)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

theorem cl_quadNe (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    cl D Sc ν [up i, up j] [up i, up j] (crossL [] i j [] ++ crossL [] j i []) =
      (Sc.t i j : k) • cl D Sc ν [up i, up j] [up i, up j] (dotsL [] i [up j] (D.dn i j)) +
      (Sc.t j i : k) • cl D Sc ν [up i, up j] [up i, up j] (dotsL [up i] j [] (D.dn j i)) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • cl D Sc ν [up i, up j] [up i, up j]
          (dotsL [up i] j [] q ++ dotsL [] i [up j] p) := by
  have := lin_relation Sc (.quadNe i j ν hij hd)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]; abel

theorem cl_slideL (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν [up i, up j] [up j, up i] (dotsL [] i [up j] 1 ++ crossL [] i j []) =
      zsign k (D.parity i * D.parity j) •
        cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [] ++ dotsL [up j] i [] 1) := by
  have := lin_relation Sc (.slideL i j ν hij)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

theorem cl_slideLEq (i : I) (ν : X) :
    cl D Sc ν [up i, up i] [up i, up i] (dotsL [] i [up i] 1 ++ crossL [] i i []) =
      zsign k (D.parity i * D.parity i) •
        cl D Sc ν [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [up i] i [] 1) +
      cl D Sc ν [up i, up i] [up i, up i] [] := by
  have := lin_relation Sc (.slideLEq i ν)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]; abel

theorem cl_slideR (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [] ++ dotsL [] j [up i] 1) =
      zsign k (D.parity i * D.parity j) •
        cl D Sc ν [up i, up j] [up j, up i] (dotsL [up i] j [] 1 ++ crossL [] i j []) := by
  have := lin_relation Sc (.slideR i j ν hij)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

theorem cl_slideREq (i : I) (ν : X) :
    cl D Sc ν [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [] i [up i] 1) =
      zsign k (D.parity i * D.parity i) •
        cl D Sc ν [up i, up i] [up i, up i] (dotsL [up i] i [] 1 ++ crossL [] i i []) +
      cl D Sc ν [up i, up i] [up i, up i] [] := by
  have := lin_relation Sc (.slideREq i ν)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]; abel

theorem cl_braid (i j k' : I) (ν : X) (h : ¬(i = k' ∧ i ≠ j)) :
    cl D Sc ν [up i, up j, up k'] [up k', up j, up i]
        (crossL [] i j [up k'] ++ crossL [up j] i k' [] ++ crossL [] j k' [up i]) =
      cl D Sc ν [up i, up j, up k'] [up k', up j, up i]
        (crossL [up i] j k' [] ++ crossL [] i k' [up j] ++ crossL [up k'] i j []) := by
  have := lin_relation Sc (.braid i j k' ν h)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

/-! ## Inversion relations (1.12)–(1.14) -/

theorem cl_invNe₁ (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν [up j, dn i] [up j, dn i] (sigmaL i j ++ lcrossL i j) =
      cl D Sc ν [up j, dn i] [up j, dn i] [] := by
  have := lin_relation Sc (.invNe₁ i j ν hij)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

theorem cl_invNe₂ (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν [dn i, up j] [dn i, up j] (lcrossL i j ++ sigmaL i j) =
      cl D Sc ν [dn i, up j] [dn i, up j] [] := by
  have := lin_relation Sc (.invNe₂ i j ν hij)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

theorem cl_invP₂ (i : I) (ν : X) (hh : 0 ≤ D.h i ν) :
    cl D Sc ν [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) =
      -cl D Sc ν [dn i, up i] [dn i, up i] [] := by
  have := lin_relation Sc (.invP₂ i ν hh)
  skm_rel_simp this
  exact eq_neg_of_add_eq_zero_left this

theorem cl_invM₂ (i : I) (ν : X) (hh : D.h i ν ≤ 0) :
    cl D Sc ν [up i, dn i] [up i, dn i] (sigmaL i i ++ lcrossL i i) =
      -cl D Sc ν [up i, dn i] [up i, dn i] [] := by
  have := lin_relation Sc (.invM₂ i ν hh)
  skm_rel_simp this
  exact eq_neg_of_add_eq_zero_left this

theorem cl_invP₁ (i : I) (ν : X) (hh : 0 ≤ D.h i ν) :
    -cl D Sc ν [up i, dn i] [up i, dn i] (sigmaL i i ++ lcrossL i i) +
      ∑ n ∈ Finset.range (D.h i ν).toNat,
        cl D Sc ν [up i, dn i] [up i, dn i] (epsL i n ++ dcupL i n) =
      cl D Sc ν [up i, dn i] [up i, dn i] [] := by
  have := lin_relation Sc (.invP₁ i ν hh)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

theorem cl_invM₁ (i : I) (ν : X) (hh : D.h i ν ≤ 0) :
    -cl D Sc ν [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) +
      ∑ n ∈ Finset.range (-D.h i ν).toNat,
        cl D Sc ν [dn i, up i] [dn i, up i] (dcapL i n ++ etaL i n) =
      cl D Sc ν [dn i, up i] [dn i, up i] [] := by
  have := lin_relation Sc (.invM₁ i ν hh)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]

theorem cl_invP₃ (i : I) (ν : X) (m : ℕ) (hm : (m : ℤ) < D.h i ν) :
    cl D Sc ν [dn i, up i] [] (lcrossL i i ++ epsL i m) = 0 := by
  have := lin_relation Sc (.invP₃ i ν m hm)
  skm_rel_simp this
  exact this

theorem cl_invP₄ (i : I) (ν : X) (n : ℕ) (hn : (n : ℤ) < D.h i ν) :
    cl D Sc ν [] [dn i, up i] (dcupL i n ++ sigmaL i i) = 0 := by
  have := lin_relation Sc (.invP₄ i ν n hn)
  skm_rel_simp this
  exact this

theorem cl_invP₅ (i : I) (ν : X) (m n : ℕ) (hm : (m : ℤ) < D.h i ν) (hn : (n : ℤ) < D.h i ν) :
    cl D Sc ν [] [] (dcupL i n ++ epsL i m) = if m = n then cl D Sc ν [] [] [] else 0 := by
  have := lin_relation Sc (.invP₅ i ν m n hm hn)
  skm_rel_simp this
  split_ifs at this ⊢ with hmn
  · simp only [lin_idg] at this
    exact sub_eq_zero.mp this
  · simpa only [lin_zero, sub_zero] using this

theorem cl_invM₃ (i : I) (ν : X) (m : ℕ) (hm : (m : ℤ) < -D.h i ν) :
    cl D Sc ν [] [up i, dn i] (etaL i m ++ lcrossL i i) = 0 := by
  have := lin_relation Sc (.invM₃ i ν m hm)
  skm_rel_simp this
  exact this

theorem cl_invM₄ (i : I) (ν : X) (n : ℕ) (hn : (n : ℤ) < -D.h i ν) :
    cl D Sc ν [up i, dn i] [] (sigmaL i i ++ dcapL i n) = 0 := by
  have := lin_relation Sc (.invM₄ i ν n hn)
  skm_rel_simp this
  exact this

theorem cl_invM₅ (i : I) (ν : X) (m n : ℕ) (hm : (m : ℤ) < -D.h i ν)
    (hn : (n : ℤ) < -D.h i ν) :
    cl D Sc ν [] [] (etaL i m ++ dcapL i n) = if m = n then cl D Sc ν [] [] [] else 0 := by
  have := lin_relation Sc (.invM₅ i ν m n hm hn)
  skm_rel_simp this
  split_ifs at this ⊢ with hmn
  · simp only [lin_idg] at this
    exact sub_eq_zero.mp this
  · simpa only [lin_zero, sub_zero] using this

theorem cl_dcupZero (i : I) (ν : X) (n : ℕ) (hn : D.h i ν ≤ n) :
    cl D Sc ν [] [up i, dn i] (dcupL i n) = 0 := by
  have := lin_relation Sc (.dcupZero i ν n hn)
  skm_rel_simp this
  exact this

theorem cl_dcapZero (i : I) (ν : X) (n : ℕ) (hn : -D.h i ν ≤ n) :
    cl D Sc ν [dn i, up i] [] (dcapL i n) = 0 := by
  have := lin_relation Sc (.dcapZero i ν n hn)
  skm_rel_simp this
  exact this

end OddMath.SKM
