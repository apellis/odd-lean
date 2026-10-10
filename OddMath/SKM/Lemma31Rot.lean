/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Mates

/-!
# Dot slides through rightward crossings (Brundan–Ellis, Lemma 3.1 (3.3))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 3.1 (TeX label
`firstlemma`), relation (3.3) (`rtcross1`), for the crossing `σ : Eᵢ Fⱼ → Fⱼ Eᵢ` (1.11):

`σ ≫ (1 ⊗ xⁿ) - (-1)^{|i||j|n} (xⁿ ⊗ 1) ≫ σ = δᵢⱼ ∑_{r+s=n-1} (-1)^{|i|r} (xʳ ⊗ 1) ≫ ε ≫ η ≫ (1 ⊗ xˢ)`

(the dots on the upward strand `Eᵢ`). The paper derives (3.3)–(3.6) by rotating (3.1), (3.2);
here (3.3) is derived from (3.2) inside `σ = (1 ⊗ ε) ∘ (1 ⊗ τ ⊗ 1) ∘ (η ⊗ 1)`.
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

end OddMath.SKM
