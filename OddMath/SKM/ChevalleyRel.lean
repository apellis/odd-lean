/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Chevalley

/-!
# The Chevalley involution (Brundan–Ellis, Proposition 3.5): the relations

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 3.5.
The image under `ω` of every defining relation of `𝔘(𝔤)` (Definition 1.5) vanishes: each one is
the mirror image of a relation, using (1.10), (1.12)–(1.14), (2.3), (2.5), (3.5)–(3.7) and (3.9).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Supercategory

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

attribute [local simp] zsign_zero omegaL_dotsL omegaC_dotsL omegaC_append parsum_dotsL

theorem omega_zigE (i : I) (ν : X) :
    omegaLin Sc ν [up i] [up i] (relation D Sc (.zigE i ν)) = 0 := by
  simp only [relation]
  rw [map_sub, omegaLin_dg]
  erw [omegaLin_idg]
  simp [chevL, chevC, Shape.parity, whL, cl_zigF]

theorem omega_zigF (i : I) (ν : X) :
    omegaLin Sc ν [dn i] [dn i] (relation D Sc (.zigF i ν)) = 0 := by
  simp only [relation]
  rw [map_sub, omegaLin_dg]
  erw [omegaLin_idg]
  simp [chevL, chevC, Shape.parity, whL, cl_zigE]

theorem omega_quadEq (i : I) (ν : X) :
    omegaLin Sc ν [up i, up i] [up i, up i] (relation D Sc (.quadEq i ν)) = 0 := by
  simp only [relation]
  rw [omegaLin_dg]
  simp [crossL, chevL, chevC, Shape.parity, lemma32_eq]

theorem omega_quadZero (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j = 0) :
    omegaLin Sc ν [up i, up j] [up i, up j] (relation D Sc (.quadZero i j ν hij hd)) = 0 := by
  simp only [relation]
  rw [map_sub, map_smul, omegaLin_dg]
  erw [omegaLin_idg]
  simp [crossL, chevL, chevC, Shape.parity]
  have key := lemma32_zero Sc i j (-ν) hij hd
  have hc : zsign k (D.parity i * D.parity j * (D.parity j * D.parity i)) *
      zsign k (D.parity i * D.parity j) * zsign k (D.parity j * D.parity i) =
      zsign k (D.parity i * D.parity j) := by
    simp only [← zsign_add]; congr 1
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  linear_combination (norm := module) key +
    hc • cl D Sc (-ν) [dn i, dn j] [dn i, dn j] (dcrossL i j ++ dcrossL j i)

theorem omega_quadNe (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    omegaLin Sc ν [up i, up j] [up i, up j] (relation D Sc (.quadNe i j ν hij hd)) = 0 := by
  simp only [relation]
  simp only [map_sub, map_smul, map_sum, omegaLin_dg]
  simp [crossL, chevL, chevC, Shape.parity]
  have hsum : ∀ p q : ℕ, cl D Sc (-ν) [dn i, dn j] [dn i, dn j]
      ((ddotsL i p).map (whL [] [dn j]) ++ (ddotsL j q).map (whL [dn i] [])) =
      zsign k ((p : ZMod 2) * D.parity i * ((q : ZMod 2) * D.parity j)) •
        cl D Sc (-ν) [dn i, dn j] [dn i, dn j]
          ((ddotsL j q).map (whL [dn i] []) ++ (ddotsL i p).map (whL [] [dn j])) := by
    intro p q
    have := cl_ixc (D := D) (Sc := Sc) (μ := -ν) (S := [dn i, dn j]) (T := [dn i, dn j]) [] []
      [] [] [] (sChain_ddotsL i p) (sChain_ddotsL j q)
    simpa only [List.nil_append, List.append_nil, parsum_ddotsL] using this
  have hcoef : ∀ p q : ℕ, Sc.s i j p q * (zsign k ((q : ZMod 2) * D.parity j * ((p : ZMod 2) *
      D.parity i)) * zsign k (D.parity j * ((q / 2 : ℕ) : ZMod 2)) *
      zsign k (D.parity i * ((p / 2 : ℕ) : ZMod 2)) *
      zsign k ((p : ZMod 2) * D.parity i * ((q : ZMod 2) * D.parity j))) =
      zsign k (D.parity i * ((p / 2 : ℕ) : ZMod 2) + D.parity j * ((q / 2 : ℕ) : ZMod 2)) *
        Sc.s i j p q := by
    intro p q
    rw [mul_comm (Sc.s i j p q)]; congr 1
    simp only [← zsign_add]; congr 1
    generalize ((p / 2 : ℕ) : ZMod 2) = a; generalize ((q / 2 : ℕ) : ZMod 2) = b
    generalize (p : ZMod 2) = c; generalize (q : ZMod 2) = d
    generalize D.parity i = e; generalize D.parity j = f
    revert a b c d e f; decide
  simp only [hsum, smul_smul, hcoef]
  have key := lemma32_ne Sc i j (-ν) hij hd
  have hc : zsign k (D.parity i * D.parity j * (D.parity j * D.parity i)) *
      zsign k (D.parity i * D.parity j) * zsign k (D.parity j * D.parity i) =
      zsign k (D.parity i * D.parity j) := by
    simp only [← zsign_add]; congr 1
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  linear_combination (norm := module) key +
    hc • cl D Sc (-ν) [dn i, dn j] [dn i, dn j] (dcrossL i j ++ dcrossL j i)

theorem omega_dcupZero (i : I) (ν : X) (n : ℕ) (hn : D.h i ν ≤ n) :
    omegaLin Sc ν [] [up i, dn i] (relation D Sc (.dcupZero i ν n hn)) = 0 := by
  simp only [relation]
  rw [omegaLin_dg]
  simp [dcupL, chevL, chevC, Shape.parity, cl_dcapZero Sc i (-ν) n (by simpa using hn)]

theorem omega_dcapZero (i : I) (ν : X) (n : ℕ) (hn : -D.h i ν ≤ n) :
    omegaLin Sc ν [dn i, up i] [] (relation D Sc (.dcapZero i ν n hn)) = 0 := by
  simp only [relation]
  rw [omegaLin_dg]
  simp [dcapL, chevL, chevC, Shape.parity, cl_dcupZero Sc i (-ν) n (by simpa using hn)]

end OddMath.SKM
