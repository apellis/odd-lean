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

theorem braidEq_aux1 (a b X Y fx fy fd : ZMod 2) (h1 : fd + X + Y * X + fx + fy + Y = 0)
    (h2 : a * (Y + X + 1) = 0) :
    a * (b + X) + X * a * (Y * a) + a * fx + a * fy + Y * a * (X * a) =
      a * (1 + b) + a * (fd + Y + 1) := by
  revert a b X Y fx fy fd; decide

theorem braidEq_aux2 (a b X Y Q fx fy fp fq : ZMod 2) (h1 : fp + X + Y * X + fx + fy + Y = 0)
    (h2 : a * (Y + X + 1) = 0) :
    a * (b + X) + X * a * (Q * b + Y * a) + a * fx + (Q * b * (Y * a) + b * fq + a * fy) +
        (Y * a * (Q * b) + Y * a * (X * a) + Q * b * (X * a)) =
      a * (1 + b) + (a * (fp + Y + 1) + b * fq) := by
  revert a b X Y Q fx fy fp fq; decide

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

theorem omega_slideL (i j : I) (ν : X) (hij : i ≠ j) :
    omegaLin Sc ν [up i, up j] [up j, up i] (relation D Sc (.slideL i j ν hij)) = 0 := by
  simp only [relation]
  simp only [map_sub, map_smul, omegaLin_dg]
  simp [crossL, chevL, chevC, Shape.parity]
  rw [← lemma31_eq6_ne Sc i j (-ν) hij 1]
  generalize D.parity i = a; generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp (config := {decide := true}) [zsign]

theorem omega_slideLEq (i : I) (ν : X) :
    omegaLin Sc ν [up i, up i] [up i, up i] (relation D Sc (.slideLEq i ν)) = 0 := by
  simp only [relation]
  simp only [map_sub, map_smul, omegaLin_dg]
  erw [omegaLin_idg]
  simp [crossL, chevL, chevC, Shape.parity]
  have key := lemma31_eq6_eq Sc i (-ν) 1
  simp only [Finset.sum_range_one, Nat.sub_self, Nat.zero_sub, Nat.cast_zero, mul_zero, zsign_zero,
    one_smul, show ddotsL i 0 = [] from rfl, List.map_nil, List.append_nil] at key
  rw [eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp key).symm]
  generalize D.parity i = a
  fin_cases a <;> simp (config := {decide := true}) [zsign]

theorem omega_slideR (i j : I) (ν : X) (hij : i ≠ j) :
    omegaLin Sc ν [up i, up j] [up j, up i] (relation D Sc (.slideR i j ν hij)) = 0 := by
  simp only [relation]
  simp only [map_sub, map_smul, omegaLin_dg]
  simp [crossL, chevL, chevC, Shape.parity]
  rw [← lemma31_eq5_ne Sc i j (-ν) hij 1]
  generalize D.parity i = a; generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp (config := {decide := true}) [zsign]

theorem omega_slideREq (i : I) (ν : X) :
    omegaLin Sc ν [up i, up i] [up i, up i] (relation D Sc (.slideREq i ν)) = 0 := by
  simp only [relation]
  simp only [map_sub, map_smul, omegaLin_dg]
  erw [omegaLin_idg]
  simp [crossL, chevL, chevC, Shape.parity]
  have key := lemma31_eq5_eq Sc i (-ν) 1
  simp only [Finset.sum_range_one, Nat.sub_self, Nat.zero_sub, Nat.cast_zero, mul_zero, zsign_zero,
    one_smul, show ddotsL i 0 = [] from rfl, List.map_nil, List.append_nil] at key
  rw [eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp key).symm]
  generalize D.parity i = a
  fin_cases a <;> simp (config := {decide := true}) [zsign]

theorem omega_braid (i j k' : I) (ν : X) (h : ¬(i = k' ∧ i ≠ j)) :
    omegaLin Sc ν [up i, up j, up k'] [up k', up j, up i] (relation D Sc (.braid i j k' ν h)) = 0 := by
  simp only [relation]
  simp only [map_sub, omegaLin_dg]
  simp [crossL, chevL, chevC, Shape.parity]
  have key := lemma33_eq9 Sc i j k' (-ν) h
  simp only [lemma33_eq9_lhs, lemma33_eq9_rhs, List.append_assoc] at key
  rw [key]
  generalize D.parity i = a; generalize D.parity j = b; generalize D.parity k' = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp (config := {decide := true}) [zsign]

theorem omega_braidEq (i j : I) (ν : X) (hij : i ≠ j) :
    omegaLin Sc ν [up i, up j, up i] [up i, up j, up i] (relation D Sc (.braidEq i j ν hij)) = 0 := by
  simp only [relation]
  simp only [map_sub, map_smul, map_sum, omegaLin_dg]
  simp [crossL, chevL, chevC, Shape.parity]
  simp only [parsum_append, parsum_dotsL]
  have E1 : ∀ a b : ℕ, cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i]
      ((ddotsL i a).map (whL [] [dn j, dn i]) ++ (ddotsL i b).map (whL [dn i, dn j] [])) =
      zsign k ((a : ZMod 2) * D.parity i * ((b : ZMod 2) * D.parity i)) •
        cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i]
          ((ddotsL i b).map (whL [dn i, dn j] []) ++ (ddotsL i a).map (whL [] [dn j, dn i])) := by
    intro a b
    have := cl_ixc (D := D) (Sc := Sc) (μ := -ν) (S := [dn i, dn j, dn i])
      (T := [dn i, dn j, dn i]) [] [] [] [dn j] [] (sChain_ddotsL i a) (sChain_ddotsL i b)
    simpa [parsum_ddotsL] using this
  have E2 : ∀ a q b : ℕ, cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i]
      ((ddotsL i a).map (whL [] [dn j, dn i]) ++ ((ddotsL j q).map (whL [dn i] [dn i]) ++
        (ddotsL i b).map (whL [dn i, dn j] []))) =
      zsign k ((a : ZMod 2) * D.parity i * ((q : ZMod 2) * D.parity j) +
          (a : ZMod 2) * D.parity i * ((b : ZMod 2) * D.parity i) +
          (q : ZMod 2) * D.parity j * ((b : ZMod 2) * D.parity i)) •
        cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i]
          ((ddotsL i b).map (whL [dn i, dn j] []) ++ ((ddotsL j q).map (whL [dn i] [dn i]) ++
            (ddotsL i a).map (whL [] [dn j, dn i]))) := by
    intro a q b
    have h1 := cl_ixc (D := D) (Sc := Sc) (μ := -ν) (S := [dn i, dn j, dn i])
      (T := [dn i, dn j, dn i]) [] ((ddotsL i b).map (whL [dn i, dn j] [])) [] [] [dn i]
      (sChain_ddotsL i a) (sChain_ddotsL j q)
    have h2 := cl_ixc (D := D) (Sc := Sc) (μ := -ν) (S := [dn i, dn j, dn i])
      (T := [dn i, dn j, dn i]) ((ddotsL j q).map (whL [dn i] [dn i])) [] [] [dn j] []
      (sChain_ddotsL i a) (sChain_ddotsL i b)
    have h3 := cl_ixc (D := D) (Sc := Sc) (μ := -ν) (S := [dn i, dn j, dn i])
      (T := [dn i, dn j, dn i]) [] ((ddotsL i a).map (whL [] [dn j, dn i])) [dn i] [] []
      (sChain_ddotsL j q) (sChain_ddotsL i b)
    simp only [List.nil_append, List.append_nil, List.cons_append, List.append_assoc,
      parsum_ddotsL] at h1 h2 h3
    rw [h1, h2, h3, smul_smul, smul_smul, zsign_add, zsign_add]
  have hS1 : ∑ x ∈ Finset.range (D.dn i j),
      (zsign k (D.parity i * (D.parity j + (x : ZMod 2))) * (Sc.t i j : k)) •
        (zsign k ((x : ZMod 2) * D.parity i * (((D.dn i j - 1 - x : ℕ) : ZMod 2) * D.parity i)) *
          zsign k (D.parity i * ((x / 2 : ℕ) : ZMod 2)) *
          zsign k (D.parity i * (((D.dn i j - 1 - x) / 2 : ℕ) : ZMod 2))) •
        cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i]
          ((ddotsL i (D.dn i j - 1 - x)).map (whL [] [dn j, dn i]) ++
            (ddotsL i x).map (whL [dn i, dn j] [])) =
      zsign k (D.parity i * (1 + D.parity j)) •
        ∑ r ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (((D.dn i j / 2 : ℕ) : ZMod 2) + r + 1)) * (Sc.t i j : k)) •
            cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i] (dots3 i j r 0 (D.dn i j - 1 - r)) := by
    rw [Finset.smul_sum]
    conv_rhs => rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [show D.dn i j - 1 - (D.dn i j - 1 - x) = x by omega, E1, dots3]
    simp only [show ddotsL j 0 = [] from rfl, List.map_nil, List.append_nil, smul_smul]
    congr 1
    have hfl := zmod2_floor_identity (D.dn i j - 1 - x) x
    rw [show D.dn i j - 1 - x + x + 1 = D.dn i j by omega] at hfl
    have hd := parity_mul_dn D i j
    rw [show D.dn i j = (D.dn i j - 1 - x) + x + 1 by omega] at hd
    push_cast at hd
    have e := congrArg (zsign k) (braidEq_aux1 (D.parity i) (D.parity j) (x : ZMod 2)
      ((D.dn i j - 1 - x : ℕ) : ZMod 2) ((x / 2 : ℕ) : ZMod 2) (((D.dn i j - 1 - x) / 2 : ℕ) : ZMod 2)
      ((D.dn i j / 2 : ℕ) : ZMod 2) hfl hd)
    simp only [zsign_add] at e
    linear_combination (Sc.t i j : k) * e
  have hS2 : ∑ x ∈ Finset.Ioo 0 (D.dn i j), ∑ x_1 ∈ Finset.Ioo 0 (D.dn j i), ∑ x_2 ∈ Finset.range x,
      (zsign k (D.parity i * (D.parity j + (x_2 : ZMod 2))) * Sc.s i j x x_1) •
        (zsign k ((x_2 : ZMod 2) * D.parity i * ((x_1 : ZMod 2) * D.parity j +
            ((x - 1 - x_2 : ℕ) : ZMod 2) * D.parity i)) *
          zsign k (D.parity i * ((x_2 / 2 : ℕ) : ZMod 2)) *
          (zsign k ((x_1 : ZMod 2) * D.parity j * (((x - 1 - x_2 : ℕ) : ZMod 2) * D.parity i)) *
            zsign k (D.parity j * ((x_1 / 2 : ℕ) : ZMod 2)) *
            zsign k (D.parity i * (((x - 1 - x_2) / 2 : ℕ) : ZMod 2)))) •
        cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i]
          ((ddotsL i (x - 1 - x_2)).map (whL [] [dn j, dn i]) ++
            ((ddotsL j x_1).map (whL [dn i] [dn i]) ++ (ddotsL i x_2).map (whL [dn i, dn j] []))) =
      zsign k (D.parity i * (1 + D.parity j)) •
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ r ∈ Finset.range p,
          (zsign k (D.parity i * (((p / 2 : ℕ) : ZMod 2) + r + 1) +
              D.parity j * ((q / 2 : ℕ) : ZMod 2)) * Sc.s i j p q) •
            cl D Sc (-ν) [dn i, dn j, dn i] [dn i, dn j, dn i] (dots3 i j r q (p - 1 - r)) := by
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    conv_rhs => rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [show p - 1 - (p - 1 - x) = x by omega, E2, dots3]
    simp only [List.append_assoc, smul_smul]
    by_cases hs : (p : ZMod 2) * D.parity i = 1
    · simp [Sc.s_eq_zero i j p q hs]
    congr 1
    have hfl := zmod2_floor_identity (p - 1 - x) x
    rw [show p - 1 - x + x + 1 = p by omega] at hfl
    have hd : D.parity i * (p : ZMod 2) = 0 := by
      rw [mul_comm]; exact zmod2_eq_zero_of_ne_one hs
    rw [show p = (p - 1 - x) + x + 1 by omega] at hd
    push_cast at hd
    have e := congrArg (zsign k) (braidEq_aux2 (D.parity i) (D.parity j) (x : ZMod 2)
      ((p - 1 - x : ℕ) : ZMod 2) (q : ZMod 2) ((x / 2 : ℕ) : ZMod 2) (((p - 1 - x) / 2 : ℕ) : ZMod 2)
      ((p / 2 : ℕ) : ZMod 2) ((q / 2 : ℕ) : ZMod 2) hfl hd)
    simp only [zsign_add] at e ⊢
    linear_combination (Sc.s i j p q) * e
  rw [hS1, hS2]
  have key := lemma33_eq9_eq Sc i j (-ν) hij
  simp only [lemma33_eq9_lhs, lemma33_eq9_rhs, List.append_assoc] at key
  have hc1 : zsign k (D.parity i * D.parity j * (D.parity i * D.parity i + D.parity j * D.parity i)) *
      zsign k (D.parity i * D.parity j) * (zsign k (D.parity i * D.parity i * (D.parity j * D.parity i)) *
        zsign k (D.parity i * D.parity i) * zsign k (D.parity j * D.parity i)) =
      zsign k (D.parity i * (1 + D.parity j)) := by
    simp only [← zsign_add]; congr 1
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  have hc2 : zsign k (D.parity j * D.parity i * (D.parity i * D.parity i + D.parity i * D.parity j)) *
      zsign k (D.parity j * D.parity i) * (zsign k (D.parity i * D.parity i * (D.parity i * D.parity j)) *
        zsign k (D.parity i * D.parity i) * zsign k (D.parity i * D.parity j)) =
      zsign k (D.parity i * (1 + D.parity j)) := by
    simp only [← zsign_add]; congr 1
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  rw [hc1, hc2]
  linear_combination (norm := module) zsign k (D.parity i * (1 + D.parity j)) • key

end OddMath.SKM
