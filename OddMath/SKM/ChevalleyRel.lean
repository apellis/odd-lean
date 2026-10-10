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

/-! ## Images of the sideways crossing and of the components of (1.13), (1.14) -/

/-- The layers of the image under `ω` of `σ : Eⱼ Fᵢ → Fᵢ Eⱼ`. -/
def omegaSigma (i j : I) : List (LayerData I) :=
  whL [up i, dn j] [] ([], Shape.cup i, []) ::
    ((dcrossL j i).map (whL [up i] [up i]) ++ [whL [] [dn j, up i] ([], Shape.cap i, [])])

theorem sChain_omegaSigma (i j : I) : SChain [up i, dn j] (omegaSigma i j) [dn j, up i] := by
  have h := (sChain_dcrossL j i).whisk [up i] [up i]
  refine ⟨rfl, ?_⟩
  refine SChain.append (t' := [up i] ++ [dn i, dn j] ++ [up i]) (by simpa [whL, Shape.cod] using h) ?_
  exact ⟨rfl, rfl⟩

variable (Sc) in
/-- `ω(σᵢⱼ)` is `σⱼᵢ` up to the scalar `-(-1)^{|i||j|}` (here the layers, without scalars):
(2.5) moves the downward crossing through the cup, then the zigzag (1.10) straightens. -/
theorem cl_omegaSigma (μ : X) (i j : I) :
    cl D Sc μ [up i, dn j] [dn j, up i] (omegaSigma i j) =
      cl D Sc μ [up i, dn j] [dn j, up i] (sigmaL j i) := by
  have E := (eq_2_5_a Sc i j (wt D μ [])).symm
  have h1 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i, dn j]) (t₀ := [dn j, up i]) []
    [([], Shape.cap i, [dn j, up i])] [up i] [] E (by simp) ⟨by simp [Shape.dom], rfl⟩
    (L := omegaSigma i j)
    (L' := [] ++ ([([], Shape.cup i, [dn j])] ++ (sigmaL j i).map (whL [dn i] [])).map
      (whL [up i] []) ++ [([], Shape.cap i, [dn j, up i])])
    (by simp [omegaSigma, whL]) rfl
  rw [h1]
  have h2 := (cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := [up i, dn j]) (T := [dn j, up i])
    [([up i], Shape.cup i, [dn j])] [] [] [] [] (A := [([], Shape.cap i, [])])
    (s := [up i, dn i]) (s' := []) ⟨rfl, rfl⟩ (sChain_sigmaL j i)
    (Or.inl (by simp [parsum, Shape.parity]))).symm
  simp [whL] at h2 ⊢
  rw [h2]
  exact cl_step (D := D) (Sc := Sc) μ [] (sigmaL j i) [] [dn j] (cl_zigE Sc i (wt D μ [dn j]))
    (by simp) (by simpa using sChain_sigmaL j i) (by simp [whL]) rfl

theorem cl_cons_congr {μ : X} {s m t : List (Letter I)} (x : LayerData I) {B B' : List (LayerData I)}
    (hx : SChain s [x] m) (hB : SChain m B t) (hB' : SChain m B' t) (c : k)
    (h : cl D Sc μ m t B = c • cl D Sc μ m t B') :
    cl D Sc μ s t (x :: B) = c • cl D Sc μ s t (x :: B') := by
  rw [show x :: B = [x] ++ B from rfl, ← cl_comp hx hB, h, Linear.comp_smul, cl_comp hx hB']; rfl

theorem cl_append_congr {μ : X} {s m t : List (Letter I)} {A A' : List (LayerData I)}
    (C : List (LayerData I)) (hA : SChain s A m) (hA' : SChain s A' m) (hC : SChain m C t) (c : k)
    (h : cl D Sc μ s m A = c • cl D Sc μ s m A') :
    cl D Sc μ s t (A ++ C) = c • cl D Sc μ s t (A' ++ C) := by
  rw [← cl_comp hA hC, h, Linear.smul_comp, cl_comp hA' hC]

theorem cl_prefix_congr {μ : X} {s m t : List (Letter I)} (A : List (LayerData I))
    {B B' : List (LayerData I)} (hA : SChain s A m) (hB : SChain m B t) (hB' : SChain m B' t)
    (c : k) (h : cl D Sc μ m t B = c • cl D Sc μ m t B') :
    cl D Sc μ s t (A ++ B) = c • cl D Sc μ s t (A ++ B') := by
  rw [← cl_comp hA hB, h, Linear.comp_smul, cl_comp hA hB']

theorem omegaL_sigmaL (i j : I) : omegaL (sigmaL i j) = omegaSigma i j := by
  simp [sigmaL, omegaSigma, chevL]

theorem omegaC_sigmaL (i j : I) : omegaC D k (sigmaL i j) = -zsign k (D.parity i * D.parity j) := by
  simp [sigmaL, chevC, Shape.parity, zsign_zero]

theorem omegaL_lcrossL (i j : I) : omegaL (lcrossL i j) = lcrossL j i := by
  simp [lcrossL, chevL]

theorem omegaC_lcrossL (i j : I) : omegaC D k (lcrossL i j) = -1 := by
  simp [lcrossL, chevC, zsign_zero]

theorem omegaL_epsL (i : I) (n : ℕ) :
    omegaL (epsL i n) = ([], Shape.cup i, []) :: (ddotsL i n).map (whL [] [up i]) := by
  simp [epsL, chevL, omegaL_dotsL]

theorem omegaC_epsL (i : I) (n : ℕ) :
    omegaC D k (epsL i n) = zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) := by
  simp [epsL, omegaC_append, omegaC_dotsL, chevC, Shape.parity, parsum, zsign_zero]

theorem omegaL_etaL (i : I) (n : ℕ) :
    omegaL (etaL i n) = (ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])] := by
  simp [etaL, chevL, omegaL_dotsL]

theorem omegaC_etaL (i : I) (n : ℕ) :
    omegaC D k (etaL i n) = zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) := by
  simp [etaL, omegaC_dotsL, chevC, Shape.parity, parsum, zsign_zero]

theorem omegaL_dcupL (i : I) (n : ℕ) : omegaL (dcupL i n) = dcapL i n := by
  simp [dcupL, dcapL, chevL]

theorem omegaC_dcupL (i : I) (n : ℕ) :
    omegaC D k (dcupL i n) = zsign k (D.parity i * n) := by
  simp [dcupL, chevC]

theorem omegaL_dcapL (i : I) (n : ℕ) : omegaL (dcapL i n) = dcupL i n := by
  simp [dcupL, dcapL, chevL]

theorem omegaC_dcapL (i : I) (n : ℕ) :
    omegaC D k (dcapL i n) = zsign k (D.parity i * n) := by
  simp [dcapL, chevC]

theorem parsum_lcrossL (i j : I) : parsum D (lcrossL i j) = D.parity i * D.parity j := by
  simp [parsum, lcrossL, Shape.parity]

theorem parsum_epsL (i : I) (n : ℕ) : parsum D (epsL i n) = (n : ZMod 2) * D.parity i := by
  rw [epsL, parsum_append, parsum_dotsL]; simp [parsum, Shape.parity]

theorem parsum_etaL (i : I) (n : ℕ) : parsum D (etaL i n) = (n : ZMod 2) * D.parity i := by
  rw [etaL, parsum_append, parsum_dotsL]; simp [parsum, Shape.parity]

theorem parsum_dcupL (i : I) (n : ℕ) : parsum D (dcupL i n) = D.parity i * n := by
  simp [parsum, dcupL, Shape.parity]

theorem parsum_dcapL (i : I) (n : ℕ) : parsum D (dcapL i n) = D.parity i * n := by
  simp [parsum, dcapL, Shape.parity]

theorem sChain_cupDots (i : I) (n : ℕ) :
    SChain [] (([], Shape.cup i, []) :: (ddotsL i n).map (whL [] [up i])) [dn i, up i] :=
  ⟨rfl, by simpa [Shape.cod] using (sChain_ddotsL i n).whisk [] [up i]⟩

theorem sChain_dotsCap (i : I) (n : ℕ) :
    SChain [up i, dn i] ((ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])]) [] :=
  SChain.append (t' := [up i] ++ [dn i] ++ []) (by simpa using (sChain_ddotsL i n).whisk [up i] [])
    ⟨rfl, rfl⟩

variable (Sc) in
/-- (2.3) for the image of `ε ∘ (xⁿ ⊗ 1)`. -/
theorem cl_cupDots (μ : X) (i : I) (n : ℕ) :
    cl D Sc μ [] [dn i, up i] (([], Shape.cup i, []) :: (ddotsL i n).map (whL [] [up i])) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) • cl D Sc μ [] [dn i, up i] (etaL i n) := by
  have h := eq_2_3_a' (Sc := Sc) i μ n
  rw [show (dotsL [] i [] n).map (whL [dn i] []) = dotsL [dn i] i [] n by
    simp [dotsL, List.map_replicate, whL]] at h
  exact h

variable (Sc) in
/-- (2.3) for the image of `(1 ⊗ xⁿ) ∘ η`. -/
theorem cl_dotsCap (μ : X) (i : I) (n : ℕ) :
    cl D Sc μ [up i, dn i] [] ((ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])]) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) • cl D Sc μ [up i, dn i] [] (epsL i n) := by
  have h := eq_2_3_b' (Sc := Sc) i μ n
  rw [show (dotsL [] i [] n).map (whL [] [dn i]) = dotsL [] i [dn i] n by
    simp [dotsL, List.map_replicate, whL]] at h
  exact h

attribute [local simp] omegaL_sigmaL omegaC_sigmaL omegaL_lcrossL omegaC_lcrossL omegaL_epsL
  omegaC_epsL omegaL_etaL omegaC_etaL omegaL_dcupL omegaC_dcupL omegaL_dcapL omegaC_dcapL
  parsum_sigmaL parsum_lcrossL parsum_epsL parsum_etaL parsum_dcupL parsum_dcapL

theorem coroot_neg (i : I) (ν : X) : D.h i (-ν) = -D.h i ν := map_neg _ _

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

theorem omega_invNe₁ (i j : I) (ν : X) (hij : i ≠ j) :
    omegaLin Sc ν [up j, dn i] [up j, dn i] (relation D Sc (.invNe₁ i j ν hij)) = 0 := by
  simp only [relation, map_sub, omegaLin_dg]
  erw [omegaLin_idg]
  simp only [omegaL_append, omegaC_append, omegaL_sigmaL, omegaL_lcrossL, omegaC_sigmaL,
    omegaC_lcrossL, parsum_sigmaL, parsum_lcrossL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_prefix_congr (lcrossL j i) (sChain_lcrossL j i) (sChain_omegaSigma i j)
    (sChain_sigmaL j i) 1 (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i j), one_smul,
    cl_invNe₂ Sc j i (-ν) (Ne.symm hij)]
  generalize D.parity i = a; generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp (config := {decide := true}) [zsign]

theorem omega_invNe₂ (i j : I) (ν : X) (hij : i ≠ j) :
    omegaLin Sc ν [dn i, up j] [dn i, up j] (relation D Sc (.invNe₂ i j ν hij)) = 0 := by
  simp only [relation, map_sub, omegaLin_dg]
  erw [omegaLin_idg]
  simp only [omegaL_append, omegaC_append, omegaL_sigmaL, omegaL_lcrossL, omegaC_sigmaL,
    omegaC_lcrossL, parsum_sigmaL, parsum_lcrossL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_append_congr (lcrossL j i) (sChain_omegaSigma i j) (sChain_sigmaL j i)
    (sChain_lcrossL j i) 1 (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i j), one_smul,
    cl_invNe₁ Sc j i (-ν) (Ne.symm hij)]
  generalize D.parity i = a; generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp (config := {decide := true}) [zsign]

theorem omega_invP₂ (i : I) (ν : X) (hh : 0 ≤ D.h i ν) :
    omegaLin Sc ν [dn i, up i] [dn i, up i] (relation D Sc (.invP₂ i ν hh)) = 0 := by
  simp only [relation, map_add, omegaLin_dg]
  erw [omegaLin_idg]
  simp only [omegaL_append, omegaC_append, omegaL_sigmaL, omegaL_lcrossL, omegaC_sigmaL,
    omegaC_lcrossL, parsum_sigmaL, parsum_lcrossL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_append_congr (lcrossL i i) (sChain_omegaSigma i i) (sChain_sigmaL i i)
    (sChain_lcrossL i i) 1 (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i i), one_smul,
    cl_invM₂ Sc i (-ν) (by rw [coroot_neg]; omega)]
  generalize D.parity i = a
  fin_cases a <;> simp (config := {decide := true}) [zsign]

theorem omega_invM₂ (i : I) (ν : X) (hh : D.h i ν ≤ 0) :
    omegaLin Sc ν [up i, dn i] [up i, dn i] (relation D Sc (.invM₂ i ν hh)) = 0 := by
  simp only [relation, map_add, omegaLin_dg]
  erw [omegaLin_idg]
  simp only [omegaL_append, omegaC_append, omegaL_sigmaL, omegaL_lcrossL, omegaC_sigmaL,
    omegaC_lcrossL, parsum_sigmaL, parsum_lcrossL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_prefix_congr (lcrossL i i) (sChain_lcrossL i i) (sChain_omegaSigma i i)
    (sChain_sigmaL i i) 1 (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i i), one_smul,
    cl_invP₂ Sc i (-ν) (by rw [coroot_neg]; omega)]
  generalize D.parity i = a
  fin_cases a <;> simp (config := {decide := true}) [zsign]

theorem omega_invP₃ (i : I) (ν : X) (m : ℕ) (hm : (m : ℤ) < D.h i ν) :
    omegaLin Sc ν [dn i, up i] [] (relation D Sc (.invP₃ i ν m hm)) = 0 := by
  simp only [relation, omegaLin_dg]
  simp only [omegaL_append, omegaC_append, omegaL_epsL, omegaL_lcrossL, omegaC_epsL,
    omegaC_lcrossL, parsum_epsL, parsum_lcrossL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_append_congr (lcrossL i i) (sChain_cupDots i m) (sChain_etaL i m) (sChain_lcrossL i i) _
    (cl_cupDots Sc (-ν) i m), cl_invM₃ Sc i (-ν) m (by rw [coroot_neg]; omega), smul_zero,
    smul_zero]

theorem omega_invM₃ (i : I) (ν : X) (m : ℕ) (hm : (m : ℤ) < -D.h i ν) :
    omegaLin Sc ν [] [up i, dn i] (relation D Sc (.invM₃ i ν m hm)) = 0 := by
  simp only [relation, omegaLin_dg]
  simp only [omegaL_append, omegaC_append, omegaL_etaL, omegaL_lcrossL, omegaC_etaL,
    omegaC_lcrossL, parsum_etaL, parsum_lcrossL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_prefix_congr (lcrossL i i) (sChain_lcrossL i i) (sChain_dotsCap i m) (sChain_epsL i m) _
    (cl_dotsCap Sc (-ν) i m), cl_invP₃ Sc i (-ν) m (by rw [coroot_neg]; omega), smul_zero,
    smul_zero]

theorem omega_invP₄ (i : I) (ν : X) (n : ℕ) (hn : (n : ℤ) < D.h i ν) :
    omegaLin Sc ν [] [dn i, up i] (relation D Sc (.invP₄ i ν n hn)) = 0 := by
  simp only [relation, omegaLin_dg]
  simp only [omegaL_append, omegaC_append, omegaL_sigmaL, omegaL_dcupL, omegaC_sigmaL,
    omegaC_dcupL, parsum_sigmaL, parsum_dcupL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_append_congr (dcapL i n) (sChain_omegaSigma i i) (sChain_sigmaL i i) (sChain_dcapL i n) 1
    (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i i), one_smul,
    cl_invM₄ Sc i (-ν) n (by rw [coroot_neg]; omega), smul_zero]

theorem omega_invM₄ (i : I) (ν : X) (n : ℕ) (hn : (n : ℤ) < -D.h i ν) :
    omegaLin Sc ν [up i, dn i] [] (relation D Sc (.invM₄ i ν n hn)) = 0 := by
  simp only [relation, omegaLin_dg]
  simp only [omegaL_append, omegaC_append, omegaL_sigmaL, omegaL_dcapL, omegaC_sigmaL,
    omegaC_dcapL, parsum_sigmaL, parsum_dcapL, flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_prefix_congr (dcupL i n) (sChain_dcupL i n) (sChain_omegaSigma i i) (sChain_sigmaL i i) 1
    (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i i), one_smul,
    cl_invP₄ Sc i (-ν) n (by rw [coroot_neg]; omega), smul_zero]

theorem omega_invP₅ (i : I) (ν : X) (m n : ℕ) (hm : (m : ℤ) < D.h i ν) (hn : (n : ℤ) < D.h i ν) :
    omegaLin Sc ν [] [] (relation D Sc (.invP₅ i ν m n hm hn)) = 0 := by
  have hm' : (m : ℤ) < -D.h i (-ν) := by rw [coroot_neg, neg_neg]; exact hm
  have hn' : (n : ℤ) < -D.h i (-ν) := by rw [coroot_neg, neg_neg]; exact hn
  simp only [relation]
  split_ifs with hmn
  · subst hmn
    rw [map_sub, omegaLin_dg]
    erw [omegaLin_idg]
    simp only [omegaL_append, omegaC_append, omegaL_epsL, omegaL_dcupL, omegaC_epsL,
      omegaC_dcupL, parsum_epsL, parsum_dcupL, flipW_nil]
    rw [cl_append_congr (dcapL i m) (sChain_cupDots i m) (sChain_etaL i m) (sChain_dcapL i m) _
      (cl_cupDots Sc (-ν) i m), cl_invM₅ Sc i (-ν) m m hm' hm', ite_eq_left rfl, smul_smul]
    generalize D.parity i = a; generalize ((m / 2 : ℕ) : ZMod 2) = b; generalize (m : ZMod 2) = c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp (config := {decide := true}) [zsign]
  · rw [map_sub, map_zero, sub_zero, omegaLin_dg]
    simp only [omegaL_append, omegaL_epsL, omegaL_dcupL, flipW_nil]
    rw [cl_append_congr (dcapL i n) (sChain_cupDots i m) (sChain_etaL i m) (sChain_dcapL i n) _
      (cl_cupDots Sc (-ν) i m), cl_invM₅ Sc i (-ν) m n hm' hn', ite_eq_right hmn, smul_zero, smul_zero]

theorem omega_invM₅ (i : I) (ν : X) (m n : ℕ) (hm : (m : ℤ) < -D.h i ν)
    (hn : (n : ℤ) < -D.h i ν) :
    omegaLin Sc ν [] [] (relation D Sc (.invM₅ i ν m n hm hn)) = 0 := by
  have hm' : (m : ℤ) < D.h i (-ν) := by rw [coroot_neg]; exact hm
  have hn' : (n : ℤ) < D.h i (-ν) := by rw [coroot_neg]; exact hn
  simp only [relation]
  split_ifs with hmn
  · subst hmn
    rw [map_sub, omegaLin_dg]
    erw [omegaLin_idg]
    simp only [omegaL_append, omegaC_append, omegaL_etaL, omegaL_dcapL, omegaC_etaL,
      omegaC_dcapL, parsum_etaL, parsum_dcapL, flipW_nil]
    rw [cl_prefix_congr (dcupL i m) (sChain_dcupL i m) (sChain_dotsCap i m) (sChain_epsL i m) _
      (cl_dotsCap Sc (-ν) i m), cl_invP₅ Sc i (-ν) m m hm' hm', ite_eq_left rfl, smul_smul]
    generalize D.parity i = a; generalize ((m / 2 : ℕ) : ZMod 2) = b; generalize (m : ZMod 2) = c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp (config := {decide := true}) [zsign]
  · rw [map_sub, map_zero, sub_zero, omegaLin_dg]
    simp only [omegaL_append, omegaL_etaL, omegaL_dcapL, flipW_nil]
    rw [cl_prefix_congr (dcupL i n) (sChain_dcupL i n) (sChain_dotsCap i m) (sChain_epsL i m) _
      (cl_dotsCap Sc (-ν) i m), cl_invP₅ Sc i (-ν) m n hm' hn', ite_eq_right hmn, smul_zero, smul_zero]

theorem omega_invP₁ (i : I) (ν : X) (hh : 0 ≤ D.h i ν) :
    omegaLin Sc ν [up i, dn i] [up i, dn i] (relation D Sc (.invP₁ i ν hh)) = 0 := by
  simp only [relation, map_sub, map_add, map_neg, map_sum, omegaLin_dg]
  erw [omegaLin_idg]
  simp only [omegaL_append, omegaL_sigmaL, omegaL_lcrossL, omegaL_epsL, omegaL_dcupL, flipW_cons,
    flipW_nil, flipL_up, flipL_dn]
  have hc1 : omegaC D k (sigmaL i i ++ lcrossL i i) = 1 := by
    simp only [omegaC_append, omegaC_sigmaL, omegaC_lcrossL, parsum_sigmaL, parsum_lcrossL]
    generalize D.parity i = a
    fin_cases a <;> simp (config := {decide := true}) [zsign]
  have hterm : ∀ x : ℕ, omegaC D k (epsL i x ++ dcupL i x) •
      cl D Sc (-ν) [dn i, up i] [dn i, up i]
        (dcapL i x ++ (([], Shape.cup i, []) :: (ddotsL i x).map (whL [] [up i]))) =
      cl D Sc (-ν) [dn i, up i] [dn i, up i] (dcapL i x ++ etaL i x) := by
    intro x
    rw [cl_prefix_congr (dcapL i x) (sChain_dcapL i x) (sChain_cupDots i x) (sChain_etaL i x) _
      (cl_cupDots Sc (-ν) i x), smul_smul]
    convert one_smul k _
    simp only [omegaC_append, omegaC_epsL, omegaC_dcupL, parsum_epsL, parsum_dcupL]
    generalize D.parity i = a; generalize ((x / 2 : ℕ) : ZMod 2) = b; generalize (x : ZMod 2) = c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp (config := {decide := true}) [zsign]
  simp only [hterm, hc1, one_smul]
  rw [cl_prefix_congr (lcrossL i i) (sChain_lcrossL i i) (sChain_omegaSigma i i)
    (sChain_sigmaL i i) 1 (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i i), one_smul]
  have key := cl_invM₁ Sc i (-ν) (by rw [coroot_neg]; omega)
  rw [coroot_neg, neg_neg] at key
  rw [← key, sub_self]

theorem omega_invM₁ (i : I) (ν : X) (hh : D.h i ν ≤ 0) :
    omegaLin Sc ν [dn i, up i] [dn i, up i] (relation D Sc (.invM₁ i ν hh)) = 0 := by
  simp only [relation, map_sub, map_add, map_neg, map_sum, omegaLin_dg]
  erw [omegaLin_idg]
  simp only [omegaL_append, omegaL_sigmaL, omegaL_lcrossL, omegaL_etaL, omegaL_dcapL, flipW_cons,
    flipW_nil, flipL_up, flipL_dn]
  have hc1 : omegaC D k (lcrossL i i ++ sigmaL i i) = 1 := by
    simp only [omegaC_append, omegaC_sigmaL, omegaC_lcrossL, parsum_sigmaL, parsum_lcrossL]
    generalize D.parity i = a
    fin_cases a <;> simp (config := {decide := true}) [zsign]
  have hterm : ∀ x : ℕ, omegaC D k (dcapL i x ++ etaL i x) •
      cl D Sc (-ν) [up i, dn i] [up i, dn i]
        (((ddotsL i x).map (whL [up i] []) ++ [([], Shape.cap i, [])]) ++ dcupL i x) =
      cl D Sc (-ν) [up i, dn i] [up i, dn i] (epsL i x ++ dcupL i x) := by
    intro x
    rw [cl_append_congr (dcupL i x) (sChain_dotsCap i x) (sChain_epsL i x) (sChain_dcupL i x) _
      (cl_dotsCap Sc (-ν) i x), smul_smul]
    convert one_smul k _
    simp only [omegaC_append, omegaC_etaL, omegaC_dcapL, parsum_etaL, parsum_dcapL]
    generalize D.parity i = a; generalize ((x / 2 : ℕ) : ZMod 2) = b; generalize (x : ZMod 2) = c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp (config := {decide := true}) [zsign]
  simp only [hterm, hc1, one_smul]
  rw [cl_append_congr (lcrossL i i) (sChain_omegaSigma i i) (sChain_sigmaL i i)
    (sChain_lcrossL i i) 1 (by rw [one_smul]; exact cl_omegaSigma Sc (-ν) i i), one_smul]
  have key := cl_invP₁ Sc i (-ν) (by rw [coroot_neg]; omega)
  rw [coroot_neg] at key
  rw [← key, sub_self]

/-! ## The Chevalley involution -/

/-- The image of every defining relation of `𝔘(𝔤)` vanishes. -/
theorem omega_relation (r : Rel D) :
    (freeLift k (SOpMap.functor (chevMap D) (chevImg D Sc))).map ((pres D Sc).rel r) = 0 := by
  apply eq_zero_of_omegaLin
  cases r with
  | quadEq i ν => exact omega_quadEq i ν
  | quadZero i j ν hij hd => exact omega_quadZero i j ν hij hd
  | quadNe i j ν hij hd => exact omega_quadNe i j ν hij hd
  | slideL i j ν hij => exact omega_slideL i j ν hij
  | slideLEq i ν => exact omega_slideLEq i ν
  | slideR i j ν hij => exact omega_slideR i j ν hij
  | slideREq i ν => exact omega_slideREq i ν
  | braid i j k' ν h => exact omega_braid i j k' ν h
  | braidEq i j ν hij => exact omega_braidEq i j ν hij
  | zigE i ν => exact omega_zigE i ν
  | zigF i ν => exact omega_zigF i ν
  | invNe₁ i j ν hij => exact omega_invNe₁ i j ν hij
  | invNe₂ i j ν hij => exact omega_invNe₂ i j ν hij
  | invP₁ i ν hh => exact omega_invP₁ i ν hh
  | invP₂ i ν hh => exact omega_invP₂ i ν hh
  | invP₃ i ν m hm => exact omega_invP₃ i ν m hm
  | invP₄ i ν n hn => exact omega_invP₄ i ν n hn
  | invP₅ i ν m n hm hn => exact omega_invP₅ i ν m n hm hn
  | invM₁ i ν hh => exact omega_invM₁ i ν hh
  | invM₂ i ν hh => exact omega_invM₂ i ν hh
  | invM₃ i ν m hm => exact omega_invM₃ i ν m hm
  | invM₄ i ν n hn => exact omega_invM₄ i ν n hn
  | invM₅ i ν m n hm hn => exact omega_invM₅ i ν m n hm hn
  | dcupZero i ν n hn => exact omega_dcupZero i ν n hn
  | dcapZero i ν n hn => exact omega_dcapZero i ν n hn

variable (Sc) in
/-- **Brundan–Ellis, Proposition 3.5: the Chevalley involution** `ω : 𝔘(𝔤) → 𝔘(𝔤)^{sop}`, the
contravariant superfunctor given on objects by `λ ↦ -λ`, `Eᵢ ↦ Fᵢ`, `Fᵢ ↦ Eᵢ` and on the generating
2-morphisms by the images `chevImg` (see `OddMath.SKM.Chevalley`). -/
def omega : (pres D Sc).Presented ⥤ SOp k (pres D Sc).Presented :=
  SOpMap.liftGen chevPar (chevMap D) (chevImg D Sc) (pres D Sc) chevImg_mem omega_relation

instance : (omega Sc).Additive := by unfold omega; infer_instance

instance : (omega Sc).Linear k := by unfold omega; infer_instance

theorem omega_obj (μ : X) (t : List (Letter I)) :
    (omega Sc).obj ((pres D Sc).obj (ob D μ t)) = ⟨(pres D Sc).obj (ob D (-μ) (flipW t))⟩ := by
  unfold omega; rw [SOpMap.liftGen_obj, chevMap_obj]

set_option backward.isDefEq.respectTransparency false in
/-- `ω` on normal-form diagrams: the images of the layers in reverse order, at the weight `-μ`. -/
theorem omega_cl (μ : X) {s t : List (Letter I)} {L : List (LayerData I)} (h : SChain s L t) :
    SOp.unsop ((omega Sc).map (cl D Sc μ s t L)) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ t)) ≫
        (omegaC D k L • cl D Sc (-μ) (flipW t) (flipW s) (omegaL L)) ≫
          eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ s)).symm := by
  unfold omega; rw [cl_of h, SOpMap.liftGen_diag, unsop_functor_mkD]

set_option backward.isDefEq.respectTransparency false in
/-- `ω` on the generating 2-morphisms (Proposition 3.5 and the table that follows it). -/
theorem omega_gen (μ : X) (g : Shape I) :
    SOp.unsop ((omega Sc).map (cl D Sc μ g.dom g.cod [([], g, [])])) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ g.cod)) ≫
        (chevC D k g • cl D Sc (-μ) (flipW g.cod) (flipW g.dom) (chevL g)) ≫
          eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ g.dom)).symm := by
  rw [omega_cl μ (show SChain g.dom [([], g, [])] g.cod from ⟨by simp, by simp⟩)]
  simp [zsign_zero]

set_option backward.isDefEq.respectTransparency false in
/-- `ω` is a strict 2-superfunctor: it commutes with horizontal composition (whiskering). -/
theorem omega_whisk {a b : Obj (sig D)} (f : (pres D Sc).obj a ⟶ (pres D Sc).obj b) {u : Obj (sig D)}
    {v : List (sig D).Colour} (hw : a.WhiskerOK u v) :
    SOp.unsop ((omega Sc).map ((pres D Sc).whisk f u v)) =
      eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_whisker b u v)) ≫
        (pres D Sc).whisk (SOp.unsop ((omega Sc).map f)) ((chevMap D).obj u) ((chevMap D).word v) ≫
          eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_whisker a u v)).symm :=
  SOpMap.liftGen_whisk chevPar chevImg_mem omega_relation f hw

/-- `ω` preserves parities. -/
theorem omega_mem {a b : Obj (sig D)} {x : (pres D Sc).obj a ⟶ (pres D Sc).obj b} {p : ZMod 2}
    (hx : x ∈ parity (R := k) ((pres D Sc).obj a) ((pres D Sc).obj b) p) :
    (omega Sc).map x ∈ parity (R := k) ((omega Sc).obj ((pres D Sc).obj a))
      ((omega Sc).obj ((pres D Sc).obj b)) p :=
  SOpMap.liftGen_mem chevPar chevImg_mem omega_relation hx

set_option backward.isDefEq.respectTransparency false in
/-- **(3.10)**: `ω(xⁿ) = (-1)^{|i|⌊n/2⌋}` times `n` downward dots, at the weight `-μ`. -/
theorem omega_dots (μ : X) (i : I) (n : ℕ) :
    SOp.unsop ((omega Sc).map (cl D Sc μ [up i] [up i] (dotsL [] i [] n))) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ [up i])) ≫
        (zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
          cl D Sc (-μ) [dn i] [dn i] (ddotsL i n)) ≫
          eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ [up i])).symm := by
  rw [omega_cl μ (show SChain [up i] (dotsL [] i [] n) [up i] from sChain_dotsL [] i [] n),
    omegaL_dotsL, omegaC_dotsL]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- `ω(σᵢⱼ) = -(-1)^{|i||j|} σⱼᵢ` (the value on the rightward crossing listed after
Proposition 3.5). -/
theorem omega_sigma (μ : X) (i j : I) :
    SOp.unsop ((omega Sc).map (cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j))) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ [dn i, up j])) ≫
        (-zsign k (D.parity i * D.parity j) •
          cl D Sc (-μ) [up i, dn j] [dn j, up i] (sigmaL j i)) ≫
          eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ [up j, dn i])).symm := by
  rw [omega_cl μ (sChain_sigmaL i j), omegaL_sigmaL, omegaC_sigmaL]
  simp only [flipW_cons, flipW_nil, flipL_up, flipL_dn]
  rw [cl_omegaSigma]

end OddMath.SKM
