/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Mates

/-!
# Dots through sideways and downward crossings (Brundan–Ellis, Lemma 3.1 (3.3)–(3.6))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 3.1 (TeX label
`firstlemma`), relations (3.3) (`rtcross1`), (3.4) (`rtcross2`), (3.5) (`downcross1`) and (3.6)
(`downcross2`):

* (3.3): upward dots on `Eᵢ` through `σ : Eᵢ Fⱼ → Fⱼ Eᵢ` (1.11), correction term
  `δᵢⱼ ∑_{r+s=n-1} (-1)^{|i|r}` (cap with `r` dots, then cup with `s` dots);
* (3.4): downward dots on `Fⱼ` through `σ`;
* (3.5), (3.6): downward dots through the downward crossing `Fⱼ Fᵢ → Fᵢ Fⱼ` (2.1), on either strand.

The paper derives (3.3)–(3.6) by rotating (3.1), (3.2). Here (3.3) and (3.4) are derived from
(3.2) and (3.1) inside `σ = (1 ⊗ ε) ∘ (1 ⊗ τ ⊗ 1) ∘ (η ⊗ 1)`, converting downward dots with (2.3);
(3.5) and (3.6) are (3.4) and (3.3) inside the downward crossing, the correction terms being
straightened with the zigzag relations. The signs of the correction terms come out exactly as
printed (the identity `zmod2_floor_identity` matches the various `(-1)^{|i|⌊n/2⌋}`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.3), `i ≠ j`.** -/
theorem lemma31_eq3_ne (i j : I) (ν : X) (hij : i ≠ j) (n : ℕ) :
    cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i ++ dotsL [dn j] i [] n) =
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, dn j] [dn j, up i] (dotsL [] i [dn j] n ++ sigmaL j i) := by
  have hd := fun (u v : List (Letter I)) (m : ℕ) => sChain_dotsL u i v m
  -- the dots move below the cap of `σ`
  have s1 : cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i ++ dotsL [dn j] i [] n) =
      cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
          dotsL [dn j] i [up j, dn j] n ++ [([dn j, up i], Shape.cap j, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn j]) (T := [dn j, up i])
      [([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] []
      (s := [dn j, up i]) (s' := [dn j, up i]) (t := [up j, dn j]) (t' := [])
      (A := dotsL [dn j] i [] n) (B := [([], Shape.cap j, [])]) (hd [dn j] [] n) ⟨rfl, rfl⟩
    simp only [parsum_cons, parsum_nil, show (Shape.cap j).parity D = 0 from rfl, add_zero,
      mul_zero, zsign_zero, one_smul] at E
    simp only [sigmaL, dotsL, List.map_replicate, whL, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append, List.cons_append] at E ⊢
    exact E.symm
  -- (3.2) inside `σ`
  have s2 : cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
          dotsL [dn j] i [up j, dn j] n ++ [([dn j, up i], Shape.cap j, [])]) =
      zsign k (D.parity j * D.parity i * n) •
      cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j])] ++ dotsL [dn j, up j] i [dn j] n ++
          [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) := by
    have E := lemma31_eq2_ne Sc j i (wt D ν [dn j]) (Ne.symm hij) n
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i])
      [([], Shape.cup j, [up i, dn j])] [([dn j, up i], Shape.cap j, [])] [dn j] [dn j] E
      (L := [([], Shape.cup j, [up i, dn j])] ++
        (crossL [] j i [] ++ dotsL [] i [up j] n).map (whL [dn j] [dn j]) ++
        [([dn j, up i], Shape.cap j, [])]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i])
      (pre := [([], Shape.cup j, [up i, dn j])]) (u := [dn j]) (v := [dn j])
      (post := [([dn j, up i], Shape.cap j, [])]) (s := [up j, up i]) (t := [up i, up j])
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (dotsL [up j] i [] n ++ crossL [] j i [])
    rw [map_smul, h2] at h1
    simp only [crossL, dotsL, List.map_append, List.map_replicate, whL, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h1 ⊢
    exact h1
  -- the dots move below the cup of `σ`
  have s3 : cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j])] ++ dotsL [dn j, up j] i [dn j] n ++
          [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) =
      cl D Sc ν [up i, dn j] [dn j, up i] (dotsL [] i [dn j] n ++ sigmaL j i) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn j]) (T := [dn j, up i])
      [] [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])] [] [] (Shape.cup j)
      (t₀ := [up i, dn j]) (t₁ := [up i, dn j]) (B := dotsL [] i [dn j] n) (hd [] [dn j] n)
    simp only [show (Shape.cup j).parity D = 0 from rfl, zero_mul, zsign_zero, one_smul] at E
    simp only [sigmaL, dotsL, List.map_replicate, whL, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append, List.append_assoc] at E ⊢
    exact E
  rw [s1, s2, s3, mul_comm (D.parity j)]

variable (Sc) in
/-- The bubble-free term of (3.3): the cap `ε` with `r` dots on its upward leg, then the cup `η`
with `s` dots on its upward leg. -/
theorem lemma31_eq3_term (i : I) (ν : X) (r s : ℕ) :
    cl D Sc ν [up i, dn i] [dn i, up i]
        ([([], Shape.cup i, [up i, dn i])] ++ dotsL [dn i, up i] i [dn i] r ++
          dotsL [dn i] i [up i, dn i] s ++ [([dn i, up i], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          dotsL [dn i] i [] s) := by
  have hd := fun (u v : List (Letter I)) (m : ℕ) => sChain_dotsL u i v m
  have hc0 : (Shape.cup i).parity D = 0 := rfl
  have hk0 : (Shape.cap i).parity D = 0 := rfl
  -- the `r` dots move below the cup
  have s1 : cl D Sc ν [up i, dn i] [dn i, up i]
        ([([], Shape.cup i, [up i, dn i])] ++ dotsL [dn i, up i] i [dn i] r ++
          dotsL [dn i] i [up i, dn i] s ++ [([dn i, up i], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] r ++ [([], Shape.cup i, [up i, dn i])] ++
          dotsL [dn i] i [up i, dn i] s ++ [([dn i, up i], Shape.cap i, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn i]) (T := [dn i, up i])
      [] (dotsL [dn i] i [up i, dn i] s ++ [([dn i, up i], Shape.cap i, [])]) [] [] (Shape.cup i)
      (t₀ := [up i, dn i]) (t₁ := [up i, dn i]) (B := dotsL [] i [dn i] r) (hd [] [dn i] r)
    simp only [hc0, zero_mul, zsign_zero, one_smul] at E
    simp only [dotsL, List.map_replicate, whL, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append, List.append_assoc] at E ⊢
    exact E
  -- the cap moves below the `s` dots
  have s2 : cl D Sc ν [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] r ++ [([], Shape.cup i, [up i, dn i])] ++
          dotsL [dn i] i [up i, dn i] s ++ [([dn i, up i], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] r ++ [([], Shape.cup i, [up i, dn i]), ([dn i, up i], Shape.cap i, [])] ++
          dotsL [dn i] i [] s) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn i]) (T := [dn i, up i])
      (dotsL [] i [dn i] r ++ [([], Shape.cup i, [up i, dn i])]) []
      (s := [dn i, up i]) (s' := [dn i, up i]) (t := [up i, dn i]) (t' := [])
      (A := dotsL [dn i] i [] s) (B := [([], Shape.cap i, [])]) (hd [dn i] [] s) ⟨rfl, rfl⟩
    simp only [parsum_cons, parsum_nil, hk0, add_zero, mul_zero, zsign_zero, one_smul] at E
    simp only [dotsL, List.map_replicate, whL, List.map_cons, List.map_nil, List.append_nil,
      List.nil_append, List.cons_append, List.append_assoc] at E ⊢
    exact E
  -- the cap moves below the cup
  have s3 : cl D Sc ν [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] r ++ [([], Shape.cup i, [up i, dn i]), ([dn i, up i], Shape.cap i, [])] ++
          dotsL [dn i] i [] s) =
      cl D Sc ν [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          dotsL [dn i] i [] s) := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [up i, dn i] [dn i, up i] (dotsL [] i [dn i] r)
      (dotsL [dn i] i [] s) [] [] [] (Shape.cup i) (Shape.cap i)
    simp only [hc0, zero_mul, zsign_zero, one_smul, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append] at E
    exact E.symm
  rw [s1, s2, s3]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.3), `i = j`.** The correction term is
`∑_{r+s=n-1} (-1)^{|i|r}` times the cap `ε` with `r` dots on its upward leg followed by the cup
`η` with `s` dots on its upward leg. -/
theorem lemma31_eq3_eq (i : I) (ν : X) (n : ℕ) :
    cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] n) -
      zsign k (D.parity i * D.parity i * n) •
        cl D Sc ν [up i, dn i] [dn i, up i] (dotsL [] i [dn i] n ++ sigmaL i i) =
      ∑ r ∈ Finset.range n, zsign k (D.parity i * r) •
        cl D Sc ν [up i, dn i] [dn i, up i]
          (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            dotsL [dn i] i [] (n - 1 - r)) := by
  have hd := fun (u v : List (Letter I)) (m : ℕ) => sChain_dotsL u i v m
  have s1 : cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] n) =
      cl D Sc ν [up i, dn i] [dn i, up i]
        ([([], Shape.cup i, [up i, dn i]), ([dn i], Shape.cross i i, [dn i])] ++
          dotsL [dn i] i [up i, dn i] n ++ [([dn i, up i], Shape.cap i, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn i]) (T := [dn i, up i])
      [([], Shape.cup i, [up i, dn i]), ([dn i], Shape.cross i i, [dn i])] []
      (s := [dn i, up i]) (s' := [dn i, up i]) (t := [up i, dn i]) (t' := [])
      (A := dotsL [dn i] i [] n) (B := [([], Shape.cap i, [])]) (hd [dn i] [] n) ⟨rfl, rfl⟩
    simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl, add_zero,
      mul_zero, zsign_zero, one_smul] at E
    simp only [sigmaL, dotsL, List.map_replicate, whL, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append, List.cons_append] at E ⊢
    exact E.symm
  have E := lemma31_eq2_eq Sc i (wt D ν [dn i]) n
  rw [sub_eq_iff_eq_add] at E
  have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [dn i, up i])
    [([], Shape.cup i, [up i, dn i])] [([dn i, up i], Shape.cap i, [])] [dn i] [dn i] E
    (L := [([], Shape.cup i, [up i, dn i])] ++
      (crossL [] i i [] ++ dotsL [] i [up i] n).map (whL [dn i] [dn i]) ++
      [([dn i, up i], Shape.cap i, [])]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  have hc : ∀ L : List (LayerData I),
      ctxL D Sc ν [up i, dn i] [dn i, up i] [([], Shape.cup i, [up i, dn i])] [dn i] [dn i]
        [([dn i, up i], Shape.cap i, [])] [up i, up i] [up i, up i]
        (cl D Sc (wt D ν [dn i]) [up i, up i] [up i, up i] L) =
      cl D Sc ν [up i, dn i] [dn i, up i] ([([], Shape.cup i, [up i, dn i])] ++
        L.map (whL [dn i] [dn i]) ++ [([dn i, up i], Shape.cap i, [])]) := fun L =>
    ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [dn i, up i])
      (pre := [([], Shape.cup i, [up i, dn i])]) (u := [dn i]) (v := [dn i])
      (post := [([dn i, up i], Shape.cap i, [])]) (s := [up i, up i]) (t := [up i, up i])
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ L
  simp only [map_add, map_sum, map_smul, hc] at h1
  -- the `n` dots of the second term move below the cup
  have s3 : cl D Sc ν [up i, dn i] [dn i, up i] ([([], Shape.cup i, [up i, dn i])] ++
        (dotsL [up i] i [] n ++ crossL [] i i []).map (whL [dn i] [dn i]) ++
        [([dn i, up i], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] [dn i, up i] (dotsL [] i [dn i] n ++ sigmaL i i) := by
    have E3 := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn i])
      (T := [dn i, up i]) [] [([dn i], Shape.cross i i, [dn i]), ([dn i, up i], Shape.cap i, [])]
      [] [] (Shape.cup i) (t₀ := [up i, dn i]) (t₁ := [up i, dn i]) (B := dotsL [] i [dn i] n)
      (hd [] [dn i] n)
    simp only [show (Shape.cup i).parity D = 0 from rfl, zero_mul, zsign_zero, one_smul] at E3
    simp only [sigmaL, crossL, dotsL, List.map_append, List.map_replicate, whL, Shape.dom,
      Shape.cod, List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E3 ⊢
    exact E3
  rw [s1, show [([], Shape.cup i, [up i, dn i]), ([dn i], Shape.cross i i, [dn i])] ++
      dotsL [dn i] i [up i, dn i] n ++ [([dn i, up i], Shape.cap i, [])] =
      [([], Shape.cup i, [up i, dn i])] ++
      (crossL [] i i [] ++ dotsL [] i [up i] n).map (whL [dn i] [dn i]) ++
      [([dn i, up i], Shape.cap i, [])] by
        simp [crossL, dotsL, whL, List.map_replicate], h1, s3, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← lemma31_eq3_term Sc i ν r (n - 1 - r)]
  congr 2
  simp [dotsL, whL, List.map_replicate, List.append_assoc]

/-! ## (3.4): downward dots through `σ` -/

theorem parsum_ddotsL (i : I) (n : ℕ) : parsum D (ddotsL i n) = (n : ZMod 2) * D.parity i := by
  induction n with
  | zero => simp [ddotsL]
  | succ n ih =>
    rw [ddotsL, List.replicate_succ', List.flatten_append, List.flatten_singleton, parsum_append,
      ← ddotsL, ih, ddotL, mateL, parsum_append, parsum_append, parsum_map_whL, parsum_dotsL]
    simp [Shape.parity]
    ring

variable (Sc) in
/-- The left-hand side of (3.4), first term: `n` downward dots on the outgoing `Fⱼ` of `σ`,
rewritten as `n` upward dots on the incoming upward strand of the inner crossing. -/
theorem lemma31_eq4_top (i j : I) (ν : X) (n : ℕ) :
    cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i ++ (ddotsL j n).map (whL [] [up i])) =
      (zsign k (D.parity i * D.parity j * n) * zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2))) •
        cl D Sc ν [up i, dn j] [dn j, up i]
          ([([], Shape.cup j, [up i, dn j])] ++ dotsL [dn j] j [up i, dn j] n ++
            [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) := by
  have hdd := sChain_ddotsL j n
  -- a1: the downward dots move below the cap
  have a1 : cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i ++ (ddotsL j n).map (whL [] [up i])) =
      cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
          (ddotsL j n).map (whL [] [up i, up j, dn j]) ++ [([dn j, up i], Shape.cap j, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn j]) (T := [dn j, up i])
      [([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] []
      (s := [dn j]) (s' := [dn j]) (t := [up i, up j, dn j]) (t' := [up i])
      (A := ddotsL j n) (B := [([up i], Shape.cap j, [])]) hdd ⟨rfl, rfl⟩
    simp only [parsum_cons, parsum_nil, show (Shape.cap j).parity D = 0 from rfl, add_zero,
      mul_zero, zsign_zero, one_smul] at E
    simp only [sigmaL, whL, List.map_cons, List.map_nil, List.append_nil, List.nil_append,
      List.cons_append] at E ⊢
    exact E.symm
  -- a2: the downward dots move below the crossing
  have a2 : cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
          (ddotsL j n).map (whL [] [up i, up j, dn j]) ++ [([dn j, up i], Shape.cap j, [])]) =
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, dn j] [dn j, up i]
          ([([], Shape.cup j, [up i, dn j])] ++ (ddotsL j n).map (whL [] [up j, up i, dn j]) ++
            [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn j]) (T := [dn j, up i])
      [([], Shape.cup j, [up i, dn j])] [([dn j, up i], Shape.cap j, [])]
      (s := [dn j]) (s' := [dn j]) (t := [up j, up i, dn j]) (t' := [up i, up j, dn j])
      (A := ddotsL j n) (B := [([], Shape.cross j i, [dn j])]) hdd (by simp [Shape.dom, Shape.cod])
    simp only [parsum_cons, parsum_nil, add_zero, parsum_ddotsL] at E
    simp only [whL, List.map_cons, List.map_nil, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] at E ⊢
    have h : D.parity i * D.parity j * n + (n : ZMod 2) * D.parity j * (Shape.cross j i).parity D = 0 := by
      simp only [Shape.parity]
      have hz : ∀ a b c : ZMod 2, a * b * c + c * b * (b * a) = 0 := by decide
      exact hz _ _ _
    rw [E, smul_smul, ← zsign_add, h, zsign_zero, one_smul]
  -- a3: (2.3) on the cup
  have a3 : cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j])] ++ (ddotsL j n).map (whL [] [up j, up i, dn j]) ++
          [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) =
      zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [up i, dn j] [dn j, up i]
          ([([], Shape.cup j, [up i, dn j])] ++ dotsL [dn j] j [up i, dn j] n ++
            [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) := by
    have E := eq_2_3_a Sc j (wt D ν [up i, dn j]) n
    have hsq : zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) *
        zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) = 1 := by
      rw [← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero]
    have E' : cl D Sc (wt D ν [up i, dn j]) [] [dn j, up j]
        ([([], Shape.cup j, [])] ++ (ddotsL j n).map (whL [] [up j])) =
        zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) •
          cl D Sc (wt D ν [up i, dn j]) [] [dn j, up j]
            ([([], Shape.cup j, [])] ++ (dotsL [] j [] n).map (whL [dn j] [])) := by
      rw [E, smul_smul, hsq, one_smul]
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i])
      [] [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])] [] [up i, dn j] E'
      (L := [] ++ ([([], Shape.cup j, [])] ++ (ddotsL j n).map (whL [] [up j])).map
        (whL [] [up i, dn j]) ++ [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])])
      rfl ⟨rfl, rfl, rfl⟩ rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i]) (pre := [])
      (u := []) (v := [up i, dn j]) (post := [([dn j], Shape.cross j i, [dn j]),
        ([dn j, up i], Shape.cap j, [])]) (s := []) (t := [dn j, up j]) rfl ⟨rfl, rfl, rfl⟩
      ([([], Shape.cup j, [])] ++ (dotsL [] j [] n).map (whL [dn j] []))
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_replicate, map_whL_map_whL, whL, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append] at h1 ⊢
    exact h1
  rw [a1, a2, a3, smul_smul]

variable (Sc) in
/-- The left-hand side of (3.4), second term: `n` downward dots on the incoming `Fⱼ` of `σ`,
rewritten as `n` upward dots on the outgoing upward strand of the inner crossing. -/
theorem lemma31_eq4_bot (i j : I) (ν : X) (n : ℕ) :
    cl D Sc ν [up i, dn j] [dn j, up i] ((ddotsL j n).map (whL [up i] []) ++ sigmaL j i) =
      (zsign k (D.parity i * D.parity j * n) * zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2))) •
        cl D Sc ν [up i, dn j] [dn j, up i]
          ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
            dotsL [dn j, up i] j [dn j] n ++ [([dn j, up i], Shape.cap j, [])]) := by
  have hdd := sChain_ddotsL j n
  -- b1: the downward dots move above the cup
  have b1 : cl D Sc ν [up i, dn j] [dn j, up i] ((ddotsL j n).map (whL [up i] []) ++ sigmaL j i) =
      cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j])] ++ (ddotsL j n).map (whL [dn j, up j, up i] []) ++
          [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn j]) (T := [dn j, up i])
      [] [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])] [] [up i] (Shape.cup j)
      (t₀ := [dn j]) (t₁ := [dn j]) (B := ddotsL j n) hdd
    simp only [show (Shape.cup j).parity D = 0 from rfl, zero_mul, zsign_zero, one_smul] at E
    simp only [sigmaL, Shape.dom, Shape.cod, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E ⊢
    exact E.symm
  -- b2: the downward dots move above the crossing
  have b2 : cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j])] ++ (ddotsL j n).map (whL [dn j, up j, up i] []) ++
          [([dn j], Shape.cross j i, [dn j]), ([dn j, up i], Shape.cap j, [])]) =
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, dn j] [dn j, up i]
          ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
            (ddotsL j n).map (whL [dn j, up i, up j] []) ++ [([dn j, up i], Shape.cap j, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn j]) (T := [dn j, up i])
      [([], Shape.cup j, [up i, dn j])] [([dn j, up i], Shape.cap j, [])] [dn j] [] (Shape.cross j i)
      (t₀ := [dn j]) (t₁ := [dn j]) (B := ddotsL j n) hdd
    simp only [parsum_ddotsL, Shape.dom, Shape.cod, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] at E ⊢
    have h : D.parity i * D.parity j * n + (Shape.cross j i).parity D * ((n : ZMod 2) * D.parity j) = 0 := by
      simp only [Shape.parity]
      have hz : ∀ a b c : ZMod 2, a * b * c + b * a * (c * b) = 0 := by decide
      exact hz _ _ _
    rw [E, smul_smul, ← zsign_add, h, zsign_zero, one_smul]
  -- b3: (2.3) on the cap
  have b3 : cl D Sc ν [up i, dn j] [dn j, up i]
        ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
          (ddotsL j n).map (whL [dn j, up i, up j] []) ++ [([dn j, up i], Shape.cap j, [])]) =
      zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [up i, dn j] [dn j, up i]
          ([([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
            dotsL [dn j, up i] j [dn j] n ++ [([dn j, up i], Shape.cap j, [])]) := by
    have E := eq_2_3_b Sc j (wt D ν []) n
    have hsq : zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) *
        zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) = 1 := by
      rw [← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero]
    have E' : cl D Sc (wt D ν []) [up j, dn j] []
        ((ddotsL j n).map (whL [up j] []) ++ [([], Shape.cap j, [])]) =
        zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) •
          cl D Sc (wt D ν []) [up j, dn j] []
            ((dotsL [] j [] n).map (whL [] [dn j]) ++ [([], Shape.cap j, [])]) := by
      rw [E, smul_smul, hsq, one_smul]
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i])
      [([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] [] [dn j, up i] [] E'
      (L := [([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])] ++
        ((ddotsL j n).map (whL [up j] []) ++ [([], Shape.cap j, [])]).map (whL [dn j, up i] []) ++ [])
      ⟨rfl, rfl, rfl⟩ rfl rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i])
      (pre := [([], Shape.cup j, [up i, dn j]), ([dn j], Shape.cross j i, [dn j])])
      (u := [dn j, up i]) (v := []) (post := []) (s := [up j, dn j]) (t := []) ⟨rfl, rfl, rfl⟩ rfl
      ((dotsL [] j [] n).map (whL [] [dn j]) ++ [([], Shape.cap j, [])])
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_append, List.map_replicate, map_whL_map_whL, whL, List.map_cons,
      List.map_nil, List.append_nil, List.nil_append, List.cons_append] at h1 ⊢
    exact h1
  rw [b1, b2, b3, smul_smul]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.4), `i ≠ j`**: downward dots on `Fⱼ` slide through
`σ : Eᵢ Fⱼ → Fⱼ Eᵢ`: `(-1)^{|i||j|n} σ ≫ (xⁿ ⊗ 1) = (1 ⊗ xⁿ) ≫ σ` (the dots on `Fⱼ`). -/
theorem lemma31_eq4_ne (i j : I) (ν : X) (hij : i ≠ j) (n : ℕ) :
    zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i ++ (ddotsL j n).map (whL [] [up i])) =
      cl D Sc ν [up i, dn j] [dn j, up i] ((ddotsL j n).map (whL [up i] []) ++ sigmaL j i) := by
  rw [lemma31_eq4_top, lemma31_eq4_bot, smul_smul, ← mul_assoc, ← zsign_add, ← two_mul,
    show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero, one_mul]
  have E := lemma31_eq1_ne Sc j i (wt D ν [dn j]) (Ne.symm hij) n
  have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i])
    [([], Shape.cup j, [up i, dn j])] [([dn j, up i], Shape.cap j, [])] [dn j] [dn j] E
    (L := [([], Shape.cup j, [up i, dn j])] ++
      (dotsL [] j [up i] n ++ crossL [] j i []).map (whL [dn j] [dn j]) ++
      [([dn j, up i], Shape.cap j, [])]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn j]) (t₀ := [dn j, up i])
    (pre := [([], Shape.cup j, [up i, dn j])]) (u := [dn j]) (v := [dn j])
    (post := [([dn j, up i], Shape.cap j, [])]) (s := [up j, up i]) (t := [up i, up j])
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (crossL [] j i [] ++ dotsL [up i] j [] n)
  rw [map_smul, h2] at h1
  simp only [crossL, dotsL, List.map_append, List.map_replicate, whL, List.map_cons, List.map_nil,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h1 ⊢
  rw [h1, smul_smul]
  congr 1
  rw [mul_comm]
  congr 2
  ring

theorem zmod2_floor_identity (r s : ℕ) :
    (((r + s + 1) / 2 : ℕ) : ZMod 2) + s + r * s + ((s / 2 : ℕ) : ZMod 2) + ((r / 2 : ℕ) : ZMod 2) + r
      = 0 := by
  rcases Nat.even_or_odd' r with ⟨a, rfl | rfl⟩ <;> rcases Nat.even_or_odd' s with ⟨b, rfl | rfl⟩
  · rw [show (2 * a + 2 * b + 1) / 2 = a + b by omega, show 2 * b / 2 = b by omega,
      show 2 * a / 2 = a by omega]
    push_cast; generalize (a : ZMod 2) = x; generalize (b : ZMod 2) = y; revert x y; decide
  · rw [show (2 * a + (2 * b + 1) + 1) / 2 = a + b + 1 by omega, show (2 * b + 1) / 2 = b by omega,
      show 2 * a / 2 = a by omega]
    push_cast; generalize (a : ZMod 2) = x; generalize (b : ZMod 2) = y; revert x y; decide
  · rw [show (2 * a + 1 + 2 * b + 1) / 2 = a + b + 1 by omega, show 2 * b / 2 = b by omega,
      show (2 * a + 1) / 2 = a by omega]
    push_cast; generalize (a : ZMod 2) = x; generalize (b : ZMod 2) = y; revert x y; decide
  · rw [show (2 * a + 1 + (2 * b + 1) + 1) / 2 = a + b + 1 by omega,
      show (2 * b + 1) / 2 = b by omega, show (2 * a + 1) / 2 = a by omega]
    push_cast; generalize (a : ZMod 2) = x; generalize (b : ZMod 2) = y; revert x y; decide

variable (Sc) in
/-- The correction terms of (3.4): a cap and a cup with upward dots, rewritten with downward
dots on their downward legs. -/
theorem lemma31_eq4_term (i : I) (ν : X) (m s : ℕ) :
    cl D Sc ν [up i, dn i] [dn i, up i]
        ([([], Shape.cup i, [up i, dn i])] ++ dotsL [dn i] i [up i, dn i] m ++
          dotsL [dn i, up i] i [dn i] s ++ [([dn i, up i], Shape.cap i, [])]) =
      (zsign k (D.parity i * m * s) * zsign k (D.parity i * ((s / 2 : ℕ) : ZMod 2)) *
          zsign k (D.parity i * ((m / 2 : ℕ) : ZMod 2))) •
        cl D Sc ν [up i, dn i] [dn i, up i]
          ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            (ddotsL i m).map (whL [] [up i])) := by
  have hd := fun (u v : List (Letter I)) (q : ℕ) => sChain_dotsL u i v q
  -- the two blocks of dots are exchanged
  have t1 : cl D Sc ν [up i, dn i] [dn i, up i]
        ([([], Shape.cup i, [up i, dn i])] ++ dotsL [dn i] i [up i, dn i] m ++
          dotsL [dn i, up i] i [dn i] s ++ [([dn i, up i], Shape.cap i, [])]) =
      zsign k (D.parity i * m * s) •
        cl D Sc ν [up i, dn i] [dn i, up i]
          ([([], Shape.cup i, [up i, dn i])] ++ dotsL [dn i, up i] i [dn i] s ++
            dotsL [dn i] i [up i, dn i] m ++ [([dn i, up i], Shape.cap i, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn i]) (T := [dn i, up i])
      [([], Shape.cup i, [up i, dn i])] [([dn i, up i], Shape.cap i, [])]
      (s := [dn i, up i]) (s' := [dn i, up i]) (t := [up i, dn i]) (t' := [up i, dn i])
      (A := dotsL [dn i] i [] m) (B := dotsL [] i [dn i] s) (hd [dn i] [] m) (hd [] [dn i] s)
    rw [parsum_dotsL, parsum_dotsL] at E
    simp only [dotsL, List.map_replicate, whL, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E ⊢
    rw [E]
    congr 2
    have hz : ∀ a b c : ZMod 2, b * a * (c * a) = a * b * c := by decide
    exact hz _ _ _
  -- the cap moves below the cup (lemma31_eq3_term)
  rw [t1, lemma31_eq3_term Sc i ν s m]
  -- (2.3) on the cap
  have t2 : cl D Sc ν [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] s ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++ dotsL [dn i] i [] m) =
      zsign k (D.parity i * ((s / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [up i, dn i] [dn i, up i]
          ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            dotsL [dn i] i [] m) := by
    have E := eq_2_3_b Sc i (wt D ν []) s
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [dn i, up i])
      [] ([([], Shape.cup i, [])] ++ dotsL [dn i] i [] m) [] [] E
      (L := [] ++ ((dotsL [] i [] s).map (whL [] [dn i]) ++ [([], Shape.cap i, [])]).map (whL [] []) ++
        ([([], Shape.cup i, [])] ++ dotsL [dn i] i [] m)) rfl
      (SChain.append (t' := [dn i, up i]) ⟨rfl, rfl⟩ (hd [dn i] [] m)) rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [dn i, up i]) (pre := [])
      (u := []) (v := []) (post := [([], Shape.cup i, [])] ++ dotsL [dn i] i [] m) (s := [up i, dn i])
      (t := []) rfl (SChain.append (t' := [dn i, up i]) ⟨rfl, rfl⟩ (hd [dn i] [] m))
      ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, [])])
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_append, List.map_replicate, map_whL_map_whL, whL,
      List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at h1 ⊢
    exact h1
  -- (2.3) on the cup
  have t3 : cl D Sc ν [up i, dn i] [dn i, up i]
        ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          dotsL [dn i] i [] m) =
      zsign k (D.parity i * ((m / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [up i, dn i] [dn i, up i]
          ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            (ddotsL i m).map (whL [] [up i])) := by
    have E := eq_2_3_a Sc i (wt D ν []) m
    have hpre : SChain [up i, dn i] ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, [])]) [] :=
      SChain.append (t' := [up i, dn i]) (by simpa using (sChain_ddotsL i s).whisk [up i] []) ⟨rfl, rfl⟩
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [dn i, up i])
      ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, [])]) [] [] [] E
      (L := ((ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, [])]) ++
        ([([], Shape.cup i, [])] ++ (dotsL [] i [] m).map (whL [dn i] [])).map (whL [] []) ++ [])
      hpre rfl rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [dn i, up i])
      (pre := (ddotsL i s).map (whL [up i] []) ++ [([], Shape.cap i, [])]) (u := []) (v := [])
      (post := []) (s := []) (t := [dn i, up i]) hpre rfl
      ([([], Shape.cup i, [])] ++ (ddotsL i m).map (whL [] [up i]))
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_replicate, map_whL_map_whL, whL,
      List.map_cons, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at h1 ⊢
    exact h1
  rw [t2, t3, smul_smul, smul_smul, mul_assoc]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.4), `i = j`**: the correction term is
`∑_{r+s=n-1} (-1)^{|i|r}` times the cap `ε` with `s` downward dots on its downward leg followed by
the cup `η` with `r` downward dots on its downward leg. -/
theorem lemma31_eq4_eq (i : I) (ν : X) (n : ℕ) :
    zsign k (D.parity i * D.parity i * n) •
        cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i ++ (ddotsL i n).map (whL [] [up i])) -
      cl D Sc ν [up i, dn i] [dn i, up i] ((ddotsL i n).map (whL [up i] []) ++ sigmaL i i) =
      ∑ r ∈ Finset.range n, zsign k (D.parity i * r) •
        cl D Sc ν [up i, dn i] [dn i, up i]
          ((ddotsL i (n - 1 - r)).map (whL [up i] []) ++
            [([], Shape.cap i, []), ([], Shape.cup i, [])] ++ (ddotsL i r).map (whL [] [up i])) := by
  rw [lemma31_eq4_top, lemma31_eq4_bot, smul_smul, ← mul_assoc, ← zsign_add, ← two_mul,
    show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero, one_mul]
  have E := lemma31_eq1_eq Sc i (wt D ν [dn i]) n
  have hc : ∀ L : List (LayerData I),
      ctxL D Sc ν [up i, dn i] [dn i, up i] [([], Shape.cup i, [up i, dn i])] [dn i] [dn i]
        [([dn i, up i], Shape.cap i, [])] [up i, up i] [up i, up i]
        (cl D Sc (wt D ν [dn i]) [up i, up i] [up i, up i] L) =
      cl D Sc ν [up i, dn i] [dn i, up i] ([([], Shape.cup i, [up i, dn i])] ++
        L.map (whL [dn i] [dn i]) ++ [([dn i, up i], Shape.cap i, [])]) := fun L =>
    ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [dn i, up i])
      (pre := [([], Shape.cup i, [up i, dn i])]) (u := [dn i]) (v := [dn i])
      (post := [([dn i, up i], Shape.cap i, [])]) (s := [up i, up i]) (t := [up i, up i])
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ L
  have E' := congrArg (ctxL D Sc ν [up i, dn i] [dn i, up i] [([], Shape.cup i, [up i, dn i])]
    [dn i] [dn i] [([dn i, up i], Shape.cap i, [])] [up i, up i] [up i, up i]) E
  simp only [map_sub, map_sum, map_smul, hc] at E'
  simp only [crossL, dotsL, List.map_append, List.map_replicate, whL, List.map_cons, List.map_nil,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at E' ⊢
  rw [mul_comm (zsign k (D.parity i * D.parity i * n)), ← smul_smul, ← smul_sub, E',
    Finset.smul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  have e := lemma31_eq4_term Sc i ν (n - 1 - (n - 1 - r)) (n - 1 - r)
  simp only [dotsL, List.nil_append, List.cons_append, List.append_assoc] at e
  rw [show n - 1 - (n - 1 - r) = r by omega] at e ⊢
  rw [e, smul_smul, smul_smul]
  congr 1
  -- the sign identity
  rw [← zsign_add, ← zsign_add, ← zsign_add, ← zsign_add]
  congr 1
  have key := zmod2_floor_identity r (n - 1 - r)
  rw [show r + (n - 1 - r) + 1 = n by omega] at key
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (D.parity i) * key - (D.parity i * r) * h2

/-! ## (3.5): downward dots through downward crossings -/

variable (Sc) in
/-- (3.5), outgoing side: `n` downward dots on the outgoing `Fⱼ` of the downward crossing
`Fⱼ Fᵢ → Fᵢ Fⱼ` are `n` downward dots on the outgoing `Fⱼ` of the inner `σ`. -/
theorem lemma31_eq5_top (i j : I) (ν : X) (n : ℕ) :
    cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i ++ (ddotsL j n).map (whL [dn i] [])) =
      cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        (sigmaL j i ++ (ddotsL j n).map (whL [] [up i])).map (whL [dn i] [dn i]) ++
        [([dn i, dn j], Shape.cap i, [])]) := by
  have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn j, dn i]) (T := [dn i, dn j])
    ([([], Shape.cup i, [dn j, dn i])] ++ (sigmaL j i).map (whL [dn i] [dn i])) []
    (s := [dn i, dn j]) (s' := [dn i, dn j]) (t := [up i, dn i]) (t' := [])
    (A := (ddotsL j n).map (whL [dn i] [])) (B := [([], Shape.cap i, [])])
    (by simpa using (sChain_ddotsL j n).whisk [dn i] []) ⟨rfl, rfl⟩
  simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl, add_zero,
    mul_zero, zsign_zero, one_smul, map_whL_map_whL] at E
  simp only [dcrossL, List.map_append, map_whL_map_whL, whL, List.map_cons, List.map_nil,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at E ⊢
  exact E.symm

variable (Sc) in
/-- (3.5), incoming side. -/
theorem lemma31_eq5_bot (i j : I) (ν : X) (n : ℕ) :
    cl D Sc ν [dn j, dn i] [dn i, dn j] ((ddotsL j n).map (whL [] [dn i]) ++ dcrossL j i) =
      cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        ((ddotsL j n).map (whL [up i] []) ++ sigmaL j i).map (whL [dn i] [dn i]) ++
        [([dn i, dn j], Shape.cap i, [])]) := by
  have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [dn j, dn i]) (T := [dn i, dn j])
    [] ((sigmaL j i).map (whL [dn i] [dn i]) ++ [([dn i, dn j], Shape.cap i, [])]) [] []
    (Shape.cup i) (t₀ := [dn j, dn i]) (t₁ := [dn j, dn i]) (B := (ddotsL j n).map (whL [] [dn i]))
    (by simpa using (sChain_ddotsL j n).whisk [] [dn i])
  simp only [show (Shape.cup i).parity D = 0 from rfl, zero_mul, zsign_zero, one_smul,
    map_whL_map_whL] at E
  simp only [dcrossL, List.map_append, map_whL_map_whL, Shape.dom, Shape.cod,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at E ⊢
  exact E.symm

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.5), `i ≠ j`**: downward dots slide through the downward
crossing `Fⱼ Fᵢ → Fᵢ Fⱼ`: `(-1)^{|i||j|n} (crossing ≫ dots on the outgoing Fⱼ) =
dots on the incoming Fⱼ ≫ crossing`. -/
theorem lemma31_eq5_ne (i j : I) (ν : X) (hij : i ≠ j) (n : ℕ) :
    zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i ++ (ddotsL j n).map (whL [dn i] [])) =
      cl D Sc ν [dn j, dn i] [dn i, dn j] ((ddotsL j n).map (whL [] [dn i]) ++ dcrossL j i) := by
  rw [lemma31_eq5_top, lemma31_eq5_bot]
  have E := lemma31_eq4_ne Sc i j (wt D ν [dn i]) hij n
  have hc : ∀ L : List (LayerData I),
      ctxL D Sc ν [dn j, dn i] [dn i, dn j] [([], Shape.cup i, [dn j, dn i])] [dn i] [dn i]
        [([dn i, dn j], Shape.cap i, [])] [up i, dn j] [dn j, up i]
        (cl D Sc (wt D ν [dn i]) [up i, dn j] [dn j, up i] L) =
      cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        L.map (whL [dn i] [dn i]) ++ [([dn i, dn j], Shape.cap i, [])]) := fun L =>
    ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn j, dn i]) (t₀ := [dn i, dn j])
      (pre := [([], Shape.cup i, [dn j, dn i])]) (u := [dn i]) (v := [dn i])
      (post := [([dn i, dn j], Shape.cap i, [])]) (s := [up i, dn j]) (t := [dn j, up i])
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ L
  have E' := congrArg (ctxL D Sc ν [dn j, dn i] [dn i, dn j] [([], Shape.cup i, [dn j, dn i])]
    [dn i] [dn i] [([dn i, dn j], Shape.cap i, [])] [up i, dn j] [dn j, up i]) E
  rw [map_smul, hc, hc] at E'
  exact E'

variable (Sc) in
/-- The correction terms of (3.5): straightening the zigzags. -/
theorem lemma31_eq5_term (i : I) (ν : X) (a b : ℕ) :
    cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        ((ddotsL i a).map (whL [up i] []) ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          (ddotsL i b).map (whL [] [up i])).map (whL [dn i] [dn i]) ++
        [([dn i, dn i], Shape.cap i, [])]) =
      cl D Sc ν [dn i, dn i] [dn i, dn i]
        ((ddotsL i a).map (whL [] [dn i]) ++ (ddotsL i b).map (whL [dn i] [])) := by
  have ha := sChain_ddotsL i a
  have hb := sChain_ddotsL i b
  -- the `a` dots move below the outer cup
  have t1 : cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        ((ddotsL i a).map (whL [up i] []) ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          (ddotsL i b).map (whL [] [up i])).map (whL [dn i] [dn i]) ++
        [([dn i, dn i], Shape.cap i, [])]) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i a).map (whL [] [dn i]) ++
        [([], Shape.cup i, [dn i, dn i]), ([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
        (ddotsL i b).map (whL [dn i] [up i, dn i]) ++ [([dn i, dn i], Shape.cap i, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [dn i, dn i])
      (T := [dn i, dn i]) [] ([([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
        (ddotsL i b).map (whL [dn i] [up i, dn i]) ++ [([dn i, dn i], Shape.cap i, [])]) [] []
      (Shape.cup i) (t₀ := [dn i, dn i]) (t₁ := [dn i, dn i]) (B := (ddotsL i a).map (whL [] [dn i]))
      (by simpa using ha.whisk [] [dn i])
    simp only [show (Shape.cup i).parity D = 0 from rfl, zero_mul, zsign_zero, one_smul,
      map_whL_map_whL] at E
    simp only [List.map_append, map_whL_map_whL, whL, Shape.dom, Shape.cod, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at E ⊢
    exact E
  -- the first zigzag
  have t2 : cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i a).map (whL [] [dn i]) ++
        [([], Shape.cup i, [dn i, dn i]), ([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
        (ddotsL i b).map (whL [dn i] [up i, dn i]) ++ [([dn i, dn i], Shape.cap i, [])]) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i a).map (whL [] [dn i]) ++ [] ++
        ([([dn i], Shape.cup i, [dn i])] ++
        (ddotsL i b).map (whL [dn i] [up i, dn i]) ++ [([dn i, dn i], Shape.cap i, [])])) := by
    have E := cl_zigF Sc i (wt D ν [dn i])
    refine cl_step ν ((ddotsL i a).map (whL [] [dn i])) _ [] [dn i] E
      (by simpa using ha.whisk [] [dn i]) ?_ (by simp [whL, List.append_assoc]) rfl
    exact SChain.append (t' := [dn i, dn i, up i, dn i])
      (SChain.append (t' := [dn i, dn i, up i, dn i]) ⟨rfl, rfl⟩
        (by simpa using hb.whisk [dn i] [up i, dn i])) ⟨rfl, rfl⟩
  -- the outer cap moves below the `b` dots
  have t3 : cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i a).map (whL [] [dn i]) ++ [] ++
        ([([dn i], Shape.cup i, [dn i])] ++
        (ddotsL i b).map (whL [dn i] [up i, dn i]) ++ [([dn i, dn i], Shape.cap i, [])])) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i a).map (whL [] [dn i]) ++
        [([dn i], Shape.cup i, [dn i]), ([dn i, dn i], Shape.cap i, [])] ++
        (ddotsL i b).map (whL [dn i] [])) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn i, dn i]) (T := [dn i, dn i])
      ((ddotsL i a).map (whL [] [dn i]) ++ [([dn i], Shape.cup i, [dn i])]) []
      (s := [dn i, dn i]) (s' := [dn i, dn i]) (t := [up i, dn i]) (t' := [])
      (A := (ddotsL i b).map (whL [dn i] [])) (B := [([], Shape.cap i, [])])
      (by simpa using hb.whisk [dn i] []) ⟨rfl, rfl⟩
    simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl, add_zero,
      mul_zero, zsign_zero, one_smul, map_whL_map_whL] at E
    simp only [whL, List.map_cons, List.map_nil, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] at E ⊢
    exact E
  -- the second zigzag
  have t4 : cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i a).map (whL [] [dn i]) ++
        [([dn i], Shape.cup i, [dn i]), ([dn i, dn i], Shape.cap i, [])] ++
        (ddotsL i b).map (whL [dn i] [])) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i a).map (whL [] [dn i]) ++ [] ++
        (ddotsL i b).map (whL [dn i] [])) := by
    have E := cl_zigF Sc i (wt D ν [])
    exact cl_step ν ((ddotsL i a).map (whL [] [dn i])) _ [dn i] [] E
      (by simpa using ha.whisk [] [dn i]) (by simpa using hb.whisk [dn i] []) (by simp [whL]) rfl
  rw [t1, t2, t3, t4, List.append_nil]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.5), `i = j`**: the correction term is `∑_{r+s=n-1} (-1)^{|i|s}`
times `r` downward dots on the left strand followed by `s` downward dots on the right strand. -/
theorem lemma31_eq5_eq (i : I) (ν : X) (n : ℕ) :
    zsign k (D.parity i * D.parity i * n) •
        cl D Sc ν [dn i, dn i] [dn i, dn i] (dcrossL i i ++ (ddotsL i n).map (whL [dn i] [])) -
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i n).map (whL [] [dn i]) ++ dcrossL i i) =
      ∑ s ∈ Finset.range n, zsign k (D.parity i * s) •
        cl D Sc ν [dn i, dn i] [dn i, dn i]
          ((ddotsL i (n - 1 - s)).map (whL [] [dn i]) ++ (ddotsL i s).map (whL [dn i] [])) := by
  rw [lemma31_eq5_top, lemma31_eq5_bot]
  have E := lemma31_eq4_eq Sc i (wt D ν [dn i]) n
  have hc : ∀ L : List (LayerData I),
      ctxL D Sc ν [dn i, dn i] [dn i, dn i] [([], Shape.cup i, [dn i, dn i])] [dn i] [dn i]
        [([dn i, dn i], Shape.cap i, [])] [up i, dn i] [dn i, up i]
        (cl D Sc (wt D ν [dn i]) [up i, dn i] [dn i, up i] L) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        L.map (whL [dn i] [dn i]) ++ [([dn i, dn i], Shape.cap i, [])]) := fun L =>
    ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn i, dn i]) (t₀ := [dn i, dn i])
      (pre := [([], Shape.cup i, [dn i, dn i])]) (u := [dn i]) (v := [dn i])
      (post := [([dn i, dn i], Shape.cap i, [])]) (s := [up i, dn i]) (t := [dn i, up i])
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ L
  have E' := congrArg (ctxL D Sc ν [dn i, dn i] [dn i, dn i] [([], Shape.cup i, [dn i, dn i])]
    [dn i] [dn i] [([dn i, dn i], Shape.cap i, [])] [up i, dn i] [dn i, up i]) E
  simp only [map_sub, map_sum, map_smul, hc, lemma31_eq5_term] at E'
  exact E'

/-! ## (3.6): downward dots on the other strand of the downward crossing -/

/-- `(2.3)` in the inverse direction, as a two-sided identity for the cup. -/
theorem eq_2_3_a' (i : I) (ν : X) (n : ℕ) :
    cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ (ddotsL i n).map (whL [] [up i])) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ (dotsL [] i [] n).map (whL [dn i] [])) := by
  rw [eq_2_3_a Sc i ν n, smul_smul, ← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl,
    zero_mul, zsign_zero, one_smul]

/-- `(2.3)` in the inverse direction, for the cap. -/
theorem eq_2_3_b' (i : I) (ν : X) (n : ℕ) :
    cl D Sc ν [up i, dn i] [] ((ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])]) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [up i, dn i] [] ((dotsL [] i [] n).map (whL [] [dn i]) ++ [([], Shape.cap i, [])]) := by
  rw [eq_2_3_b Sc i ν n, smul_smul, ← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl,
    zero_mul, zsign_zero, one_smul]

variable (Sc) in
/-- (3.6), outgoing side: downward dots on the outgoing `Fᵢ` of the downward crossing
`Fⱼ Fᵢ → Fᵢ Fⱼ` are upward dots on the incoming upward strand of the inner `σ`. -/
theorem lemma31_eq6_top (i j : I) (ν : X) (n : ℕ) :
    cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i ++ (ddotsL i n).map (whL [] [dn j])) =
      (zsign k (D.parity i * D.parity j * n) * zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2))) •
        cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
          dotsL [dn i] i [dn j, dn i] n ++ (sigmaL j i).map (whL [dn i] [dn i]) ++
          [([dn i, dn j], Shape.cap i, [])]) := by
  have hdd := sChain_ddotsL i n
  have hσ := sChain_sigmaL j i
  -- the dots move below the cap and `σ`
  have a1 : cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i ++ (ddotsL i n).map (whL [] [dn j])) =
      zsign k (D.parity i * D.parity j * n) •
      cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        (ddotsL i n).map (whL [] [up i, dn j, dn i]) ++ (sigmaL j i).map (whL [dn i] [dn i]) ++
        [([dn i, dn j], Shape.cap i, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn j, dn i]) (T := [dn i, dn j])
      [([], Shape.cup i, [dn j, dn i])] [] (s := [dn i]) (s' := [dn i]) (t := [up i, dn j, dn i])
      (t' := [dn j]) (A := ddotsL i n)
      (B := (sigmaL j i).map (whL [] [dn i]) ++ [([dn j], Shape.cap i, [])]) hdd
      (SChain.append (t' := [dn j, up i, dn i]) (by simpa using hσ.whisk [] [dn i]) ⟨rfl, rfl⟩)
    rw [parsum_ddotsL, parsum_append, parsum_map_whL, parsum_sigmaL] at E
    simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl, add_zero] at E
    simp only [dcrossL, List.map_append, map_whL_map_whL, whL, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at E ⊢
    rw [E, smul_smul, ← zsign_add]
    have h : D.parity i * D.parity j * n + (n : ZMod 2) * D.parity i * (D.parity j * D.parity i) = 0 := by
      have hz : ∀ a b c : ZMod 2, a * b * c + c * a * (b * a) = 0 := by decide
      exact hz _ _ _
    rw [h, zsign_zero, one_smul]
  -- (2.3) on the cup
  have a2 : cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        (ddotsL i n).map (whL [] [up i, dn j, dn i]) ++ (sigmaL j i).map (whL [dn i] [dn i]) ++
        [([dn i, dn j], Shape.cap i, [])]) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
      cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
          dotsL [dn i] i [dn j, dn i] n ++ (sigmaL j i).map (whL [dn i] [dn i]) ++
          [([dn i, dn j], Shape.cap i, [])]) := by
    have E := eq_2_3_a' (Sc := Sc) i (wt D ν [dn j, dn i]) n
    have hpost : SChain ([] ++ [dn i, up i] ++ [dn j, dn i])
        ((sigmaL j i).map (whL [dn i] [dn i]) ++ [([dn i, dn j], Shape.cap i, [])]) [dn i, dn j] :=
      SChain.append (t' := [dn i, dn j, up i, dn i]) (by simpa using hσ.whisk [dn i] [dn i]) ⟨rfl, rfl⟩
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [dn j, dn i]) (t₀ := [dn i, dn j]) []
      ((sigmaL j i).map (whL [dn i] [dn i]) ++ [([dn i, dn j], Shape.cap i, [])]) [] [dn j, dn i] E
      (L := [] ++ ([([], Shape.cup i, [])] ++ (ddotsL i n).map (whL [] [up i])).map
        (whL [] [dn j, dn i]) ++ ((sigmaL j i).map (whL [dn i] [dn i]) ++ [([dn i, dn j], Shape.cap i, [])]))
      rfl hpost rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn j, dn i]) (t₀ := [dn i, dn j]) (pre := [])
      (u := []) (v := [dn j, dn i])
      (post := (sigmaL j i).map (whL [dn i] [dn i]) ++ [([dn i, dn j], Shape.cap i, [])])
      (s := []) (t := [dn i, up i]) rfl hpost
      ([([], Shape.cup i, [])] ++ (dotsL [] i [] n).map (whL [dn i] []))
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_replicate, map_whL_map_whL, whL, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h1 ⊢
    exact h1
  rw [a1, a2, smul_smul]

variable (Sc) in
/-- (3.6), incoming side. -/
theorem lemma31_eq6_bot (i j : I) (ν : X) (n : ℕ) :
    cl D Sc ν [dn j, dn i] [dn i, dn j] ((ddotsL i n).map (whL [dn j] []) ++ dcrossL j i) =
      (zsign k (D.parity i * D.parity j * n) * zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2))) •
        cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
          (sigmaL j i).map (whL [dn i] [dn i]) ++ dotsL [dn i, dn j] i [dn i] n ++
          [([dn i, dn j], Shape.cap i, [])]) := by
  have hdd := sChain_ddotsL i n
  have hσ := sChain_sigmaL j i
  -- the dots move above the cup and `σ`
  have b1 : cl D Sc ν [dn j, dn i] [dn i, dn j] ((ddotsL i n).map (whL [dn j] []) ++ dcrossL j i) =
      zsign k (D.parity i * D.parity j * n) •
      cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        (sigmaL j i).map (whL [dn i] [dn i]) ++ (ddotsL i n).map (whL [dn i, dn j, up i] []) ++
        [([dn i, dn j], Shape.cap i, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn j, dn i]) (T := [dn i, dn j])
      [] [([dn i, dn j], Shape.cap i, [])] (s := [dn j]) (s' := [dn i, dn j, up i])
      (t := [dn i]) (t' := [dn i])
      (A := [([], Shape.cup i, [dn j])] ++ (sigmaL j i).map (whL [dn i] []))
      (B := ddotsL i n) (SChain.append (t' := [dn i, up i, dn j]) ⟨rfl, rfl⟩
        (by simpa using hσ.whisk [dn i] [])) hdd
    rw [parsum_ddotsL, parsum_append, parsum_map_whL, parsum_sigmaL] at E
    simp only [parsum_cons, parsum_nil, show (Shape.cup i).parity D = 0 from rfl, zero_add] at E
    simp only [dcrossL, map_whL_map_whL, whL, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at E ⊢
    have h : D.parity i * D.parity j * n + D.parity j * D.parity i * ((n : ZMod 2) * D.parity i) = 0 := by
      have hz : ∀ a b c : ZMod 2, a * b * c + b * a * (c * a) = 0 := by decide
      exact hz _ _ _
    rw [E, smul_smul, ← zsign_add, h, zsign_zero, one_smul]
  -- (2.3) on the cap
  have b2 : cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        (sigmaL j i).map (whL [dn i] [dn i]) ++ (ddotsL i n).map (whL [dn i, dn j, up i] []) ++
        [([dn i, dn j], Shape.cap i, [])]) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
          (sigmaL j i).map (whL [dn i] [dn i]) ++ dotsL [dn i, dn j] i [dn i] n ++
          [([dn i, dn j], Shape.cap i, [])]) := by
    have E := eq_2_3_b' (Sc := Sc) i (wt D ν []) n
    have hpre : SChain [dn j, dn i] ([([], Shape.cup i, [dn j, dn i])] ++
        (sigmaL j i).map (whL [dn i] [dn i])) ([dn i, dn j] ++ [up i, dn i] ++ []) :=
      SChain.append (t' := [dn i, up i, dn j, dn i]) ⟨rfl, rfl⟩ (by simpa using hσ.whisk [dn i] [dn i])
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [dn j, dn i]) (t₀ := [dn i, dn j])
      ([([], Shape.cup i, [dn j, dn i])] ++ (sigmaL j i).map (whL [dn i] [dn i])) [] [dn i, dn j] [] E
      (L := ([([], Shape.cup i, [dn j, dn i])] ++ (sigmaL j i).map (whL [dn i] [dn i])) ++
        ((ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])]).map (whL [dn i, dn j] []) ++ [])
      hpre rfl rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn j, dn i]) (t₀ := [dn i, dn j])
      (pre := [([], Shape.cup i, [dn j, dn i])] ++ (sigmaL j i).map (whL [dn i] [dn i]))
      (u := [dn i, dn j]) (v := []) (post := []) (s := [up i, dn i]) (t := []) hpre rfl
      ((dotsL [] i [] n).map (whL [] [dn i]) ++ [([], Shape.cap i, [])])
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_append, List.map_replicate, map_whL_map_whL, whL, List.map_cons,
      List.map_nil, List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h1 ⊢
    exact h1
  rw [b1, b2, smul_smul]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.6), `i ≠ j`**: downward dots on `Fᵢ` slide through the downward
crossing `Fⱼ Fᵢ → Fᵢ Fⱼ`. -/
theorem lemma31_eq6_ne (i j : I) (ν : X) (hij : i ≠ j) (n : ℕ) :
    zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [dn j, dn i] [dn i, dn j] ((ddotsL i n).map (whL [dn j] []) ++ dcrossL j i) =
      cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i ++ (ddotsL i n).map (whL [] [dn j])) := by
  rw [lemma31_eq6_top, lemma31_eq6_bot, smul_smul, ← mul_assoc, ← zsign_add, ← two_mul,
    show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero, one_mul]
  have E := lemma31_eq3_ne Sc i j (wt D ν [dn i]) hij n
  have hc : ∀ L : List (LayerData I),
      ctxL D Sc ν [dn j, dn i] [dn i, dn j] [([], Shape.cup i, [dn j, dn i])] [dn i] [dn i]
        [([dn i, dn j], Shape.cap i, [])] [up i, dn j] [dn j, up i]
        (cl D Sc (wt D ν [dn i]) [up i, dn j] [dn j, up i] L) =
      cl D Sc ν [dn j, dn i] [dn i, dn j] ([([], Shape.cup i, [dn j, dn i])] ++
        L.map (whL [dn i] [dn i]) ++ [([dn i, dn j], Shape.cap i, [])]) := fun L =>
    ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn j, dn i]) (t₀ := [dn i, dn j])
      (pre := [([], Shape.cup i, [dn j, dn i])]) (u := [dn i]) (v := [dn i])
      (post := [([dn i, dn j], Shape.cap i, [])]) (s := [up i, dn j]) (t := [dn j, up i])
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ L
  have E' := congrArg (ctxL D Sc ν [dn j, dn i] [dn i, dn j] [([], Shape.cup i, [dn j, dn i])]
    [dn i] [dn i] [([dn i, dn j], Shape.cap i, [])] [up i, dn j] [dn j, up i]) E
  rw [map_smul, hc, hc] at E'
  simp only [dotsL, List.map_append, List.map_replicate, whL, List.append_nil, List.nil_append,
    List.cons_append, List.append_assoc] at E' ⊢
  rw [E', smul_smul, mul_comm]

variable (Sc) in
/-- The correction terms of (3.6): straightening the zigzags. -/
theorem lemma31_eq6_term (i : I) (ν : X) (r m : ℕ) :
    cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          dotsL [dn i] i [] m).map (whL [dn i] [dn i]) ++ [([dn i, dn i], Shape.cap i, [])]) =
      (zsign k (D.parity i * ((r / 2 : ℕ) : ZMod 2)) * zsign k (D.parity i * ((m / 2 : ℕ) : ZMod 2)) *
          zsign k (D.parity i * r * m)) •
        cl D Sc ν [dn i, dn i] [dn i, dn i]
          ((ddotsL i m).map (whL [dn i] []) ++ (ddotsL i r).map (whL [] [dn i])) := by
  have hr := sChain_ddotsL i r
  have hm := sChain_ddotsL i m
  have hd := fun (u v : List (Letter I)) (q : ℕ) => sChain_dotsL u i v q
  -- (1) (2.3) on the outer cup
  have t1 : cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          dotsL [dn i] i [] m).map (whL [dn i] [dn i]) ++ [([dn i, dn i], Shape.cap i, [])]) =
      zsign k (D.parity i * ((r / 2 : ℕ) : ZMod 2)) •
      cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        (ddotsL i r).map (whL [] [up i, dn i, dn i]) ++
        [([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
        dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])]) := by
    have E := eq_2_3_a Sc i (wt D ν [dn i, dn i]) r
    have hpost : SChain ([] ++ [dn i, up i] ++ [dn i, dn i])
        ([([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
          dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])]) [dn i, dn i] :=
      SChain.append (t' := [dn i, dn i, up i, dn i])
        (SChain.append (t' := [dn i, dn i, up i, dn i]) ⟨rfl, rfl, rfl⟩ (hd [dn i, dn i] [dn i] m))
        ⟨rfl, rfl⟩
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [dn i, dn i]) (t₀ := [dn i, dn i]) []
      ([([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
        dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])]) [] [dn i, dn i] E
      (L := [] ++ ([([], Shape.cup i, [])] ++ (dotsL [] i [] r).map (whL [dn i] [])).map
        (whL [] [dn i, dn i]) ++ ([([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
          dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])])) rfl hpost rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn i, dn i]) (t₀ := [dn i, dn i]) (pre := [])
      (u := []) (v := [dn i, dn i])
      (post := [([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
        dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])])
      (s := []) (t := [dn i, up i]) rfl hpost
      ([([], Shape.cup i, [])] ++ (ddotsL i r).map (whL [] [up i]))
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_append, List.map_replicate, map_whL_map_whL, whL, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h1 ⊢
    exact h1
  -- (2) the `r` downward dots move above the inner cap
  have t2 : cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        (ddotsL i r).map (whL [] [up i, dn i, dn i]) ++
        [([dn i], Shape.cap i, [dn i]), ([dn i], Shape.cup i, [dn i])] ++
        dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])]) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i]), ([dn i], Shape.cap i, [dn i])] ++
        (ddotsL i r).map (whL [] [dn i]) ++ [([dn i], Shape.cup i, [dn i])] ++
        dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn i, dn i]) (T := [dn i, dn i])
      [([], Shape.cup i, [dn i, dn i])]
      ([([dn i], Shape.cup i, [dn i])] ++ dotsL [dn i, dn i] i [dn i] m ++
        [([dn i, dn i], Shape.cap i, [])]) (s := [dn i]) (s' := [dn i]) (t := [up i, dn i, dn i])
      (t' := [dn i]) (A := ddotsL i r) (B := [([], Shape.cap i, [dn i])]) hr ⟨rfl, rfl⟩
    simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl, add_zero,
      mul_zero, zsign_zero, one_smul] at E
    simp only [whL, List.map_cons, List.map_nil, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] at E ⊢
    exact E
  -- (3) the first zigzag
  have t3 : cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i]), ([dn i], Shape.cap i, [dn i])] ++
        (ddotsL i r).map (whL [] [dn i]) ++ [([dn i], Shape.cup i, [dn i])] ++
        dotsL [dn i, dn i] i [dn i] m ++ [([dn i, dn i], Shape.cap i, [])]) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ([] ++ [] ++ ((ddotsL i r).map (whL [] [dn i]) ++
        [([dn i], Shape.cup i, [dn i])] ++ dotsL [dn i, dn i] i [dn i] m ++
        [([dn i, dn i], Shape.cap i, [])])) := by
    have E := cl_zigF Sc i (wt D ν [dn i])
    refine cl_step ν [] _ [] [dn i] E rfl ?_ (by simp [whL, List.append_assoc]) rfl
    exact SChain.append (t' := [dn i, dn i, up i, dn i])
      (SChain.append (t' := [dn i, dn i, up i, dn i])
        (SChain.append (t' := [dn i, dn i]) (by simpa using hr.whisk [] [dn i]) ⟨rfl, rfl⟩)
        (hd [dn i, dn i] [dn i] m)) ⟨rfl, rfl⟩
  -- (4) (2.3) on the outer cap
  have t4 : cl D Sc ν [dn i, dn i] [dn i, dn i] ([] ++ [] ++ ((ddotsL i r).map (whL [] [dn i]) ++
        [([dn i], Shape.cup i, [dn i])] ++ dotsL [dn i, dn i] i [dn i] m ++
        [([dn i, dn i], Shape.cap i, [])])) =
      zsign k (D.parity i * ((m / 2 : ℕ) : ZMod 2)) •
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i r).map (whL [] [dn i]) ++
        [([dn i], Shape.cup i, [dn i])] ++ (ddotsL i m).map (whL [dn i, dn i, up i] []) ++
        [([dn i, dn i], Shape.cap i, [])]) := by
    have E := eq_2_3_b Sc i (wt D ν []) m
    have hpre : SChain [dn i, dn i] ((ddotsL i r).map (whL [] [dn i]) ++
        [([dn i], Shape.cup i, [dn i])]) ([dn i, dn i] ++ [up i, dn i] ++ []) :=
      SChain.append (t' := [dn i, dn i]) (by simpa using hr.whisk [] [dn i]) ⟨rfl, rfl⟩
    have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [dn i, dn i]) (t₀ := [dn i, dn i])
      ((ddotsL i r).map (whL [] [dn i]) ++ [([dn i], Shape.cup i, [dn i])]) [] [dn i, dn i] [] E
      (L := ((ddotsL i r).map (whL [] [dn i]) ++ [([dn i], Shape.cup i, [dn i])]) ++
        ((dotsL [] i [] m).map (whL [] [dn i]) ++ [([], Shape.cap i, [])]).map (whL [dn i, dn i] []) ++ [])
      hpre rfl rfl
    have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn i, dn i]) (t₀ := [dn i, dn i])
      (pre := (ddotsL i r).map (whL [] [dn i]) ++ [([dn i], Shape.cup i, [dn i])])
      (u := [dn i, dn i]) (v := []) (post := []) (s := [up i, dn i]) (t := []) hpre rfl
      ((ddotsL i m).map (whL [up i] []) ++ [([], Shape.cap i, [])])
    rw [map_smul, h2] at h1
    simp only [dotsL, List.map_append, List.map_replicate, map_whL_map_whL, whL, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append, List.append_assoc] at h1 ⊢
    exact h1
  -- (5) the `m` downward dots move below the inner cup
  have t5 : cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i r).map (whL [] [dn i]) ++
        [([dn i], Shape.cup i, [dn i])] ++ (ddotsL i m).map (whL [dn i, dn i, up i] []) ++
        [([dn i, dn i], Shape.cap i, [])]) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i r).map (whL [] [dn i]) ++
        (ddotsL i m).map (whL [dn i] []) ++
        [([dn i], Shape.cup i, [dn i]), ([dn i, dn i], Shape.cap i, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [dn i, dn i]) (T := [dn i, dn i])
      ((ddotsL i r).map (whL [] [dn i])) [([dn i, dn i], Shape.cap i, [])] [dn i] [] (Shape.cup i)
      (t₀ := [dn i]) (t₁ := [dn i]) (B := ddotsL i m) hm
    simp only [show (Shape.cup i).parity D = 0 from rfl, zero_mul, zsign_zero, one_smul] at E
    simp only [Shape.dom, Shape.cod, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E ⊢
    exact E
  -- (6) the second zigzag
  have t6 : cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i r).map (whL [] [dn i]) ++
        (ddotsL i m).map (whL [dn i] []) ++
        [([dn i], Shape.cup i, [dn i]), ([dn i, dn i], Shape.cap i, [])]) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i r).map (whL [] [dn i]) ++
        (ddotsL i m).map (whL [dn i] []) ++ []) := by
    have E := cl_zigF Sc i (wt D ν [])
    exact cl_step ν ((ddotsL i r).map (whL [] [dn i]) ++ (ddotsL i m).map (whL [dn i] [])) [] [dn i] []
      E (SChain.append (t' := [dn i, dn i]) (by simpa using hr.whisk [] [dn i])
        (by simpa using hm.whisk [dn i] [])) rfl (by simp [whL]) (by simp)
  -- (7) the two blocks of downward dots are exchanged
  have t7 : cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i r).map (whL [] [dn i]) ++
        (ddotsL i m).map (whL [dn i] []) ++ []) =
      zsign k (D.parity i * r * m) • cl D Sc ν [dn i, dn i] [dn i, dn i]
        ((ddotsL i m).map (whL [dn i] []) ++ (ddotsL i r).map (whL [] [dn i])) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn i, dn i]) (T := [dn i, dn i])
      [] [] (s := [dn i]) (s' := [dn i]) (t := [dn i]) (t' := [dn i]) (A := ddotsL i r)
      (B := ddotsL i m) hr hm
    rw [parsum_ddotsL, parsum_ddotsL] at E
    simp only [List.nil_append, List.append_nil] at E ⊢
    rw [E]
    congr 2
    have hz : ∀ a b c : ZMod 2, b * a * (c * a) = a * b * c := by decide
    exact hz _ _ _
  rw [t1, t2, t3, t4, t5, t6, t7, smul_smul, smul_smul, mul_assoc]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.1 (3.6), `i = j`**: the correction term is `∑_{r+s=n-1} (-1)^{|i|s}`
times `s` downward dots on the right strand followed by `r` downward dots on the left strand. -/
theorem lemma31_eq6_eq (i : I) (ν : X) (n : ℕ) :
    zsign k (D.parity i * D.parity i * n) •
        cl D Sc ν [dn i, dn i] [dn i, dn i] ((ddotsL i n).map (whL [dn i] []) ++ dcrossL i i) -
      cl D Sc ν [dn i, dn i] [dn i, dn i] (dcrossL i i ++ (ddotsL i n).map (whL [] [dn i])) =
      ∑ r ∈ Finset.range n, zsign k (D.parity i * ((n - 1 - r : ℕ) : ZMod 2)) •
        cl D Sc ν [dn i, dn i] [dn i, dn i]
          ((ddotsL i (n - 1 - r)).map (whL [dn i] []) ++ (ddotsL i r).map (whL [] [dn i])) := by
  rw [lemma31_eq6_top, lemma31_eq6_bot, smul_smul, ← mul_assoc, ← zsign_add, ← two_mul,
    show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero, one_mul]
  have E := lemma31_eq3_eq Sc i (wt D ν [dn i]) n
  have hc : ∀ L : List (LayerData I),
      ctxL D Sc ν [dn i, dn i] [dn i, dn i] [([], Shape.cup i, [dn i, dn i])] [dn i] [dn i]
        [([dn i, dn i], Shape.cap i, [])] [up i, dn i] [dn i, up i]
        (cl D Sc (wt D ν [dn i]) [up i, dn i] [dn i, up i] L) =
      cl D Sc ν [dn i, dn i] [dn i, dn i] ([([], Shape.cup i, [dn i, dn i])] ++
        L.map (whL [dn i] [dn i]) ++ [([dn i, dn i], Shape.cap i, [])]) := fun L =>
    ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [dn i, dn i]) (t₀ := [dn i, dn i])
      (pre := [([], Shape.cup i, [dn i, dn i])]) (u := [dn i]) (v := [dn i])
      (post := [([dn i, dn i], Shape.cap i, [])]) (s := [up i, dn i]) (t := [dn i, up i])
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ L
  have E' := congrArg (ctxL D Sc ν [dn i, dn i] [dn i, dn i] [([], Shape.cup i, [dn i, dn i])]
    [dn i] [dn i] [([dn i, dn i], Shape.cap i, [])] [up i, dn i] [dn i, up i]) E
  simp only [map_sub, map_sum, map_smul, hc, lemma31_eq6_term] at E'
  simp only [dotsL, List.map_append, List.map_replicate, whL, List.append_nil, List.nil_append,
    List.cons_append, List.append_assoc] at E' ⊢
  rw [mul_comm (zsign k (D.parity i * D.parity i * n)), ← smul_smul, ← smul_sub, E',
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [smul_smul, smul_smul]
  congr 1
  rw [← zsign_add, ← zsign_add, ← zsign_add, ← zsign_add]
  congr 1
  have key := zmod2_floor_identity r (n - 1 - r)
  rw [show r + (n - 1 - r) + 1 = n by omega] at key
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (D.parity i) * key - (D.parity i * (n - 1 - r : ℕ)) * h2

end OddMath.SKM
