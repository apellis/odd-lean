/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Rewriting
import OddMath.SKM.RelationsNF
import OddMath.SKM.DotSlides

/-!
# Right mates of upward 2-morphisms (Brundan–Ellis, Definition 2.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 2.1,
(2.1)–(2.5): the downward dot is the right mate of the upward dot,
`(1 ⊗ ε) ∘ (1 ⊗ x ⊗ 1) ∘ (η ⊗ 1)` on `Fᵢ` (the rightward cup on the left, the dot on the middle
upward strand, the rightward cap on the right), and the downward crossing is the right mate of the
upward crossing, i.e. the rotation of `σ` (1.11).

* `mateL i a`: the right mate of a 2-morphism `a : Eᵢ → Eᵢ` given by a list of layers;
* `cl_cup_slide`, `cl_cap_slide`: a 2-morphism on the upward leg of the rightward cup `η` (cap `ε`)
  equals its right mate on the downward leg;
* `cl_mate_comp`: `mate(a) ≫ mate(b) = (-1)^{|a||b|} mate(b ≫ a)`;
* `ddotL`, `cl_ddot_pow`: the downward dot and (2.2);
* `eq_2_3_a`, `eq_2_3_b`: (2.3);
* `dcrossL`: the downward crossing (2.1); `eq_2_4_a`, `eq_2_4_b`, `eq_2_5_a`, `eq_2_5_b`: the
  pitchfork relations (2.4), (2.5).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-- The right mate on `Fᵢ` of the 2-morphism on `Eᵢ` with layers `a`: the cup `η` on the left,
`a` on the middle (upward) strand, the cap `ε` on the right. -/
def mateL (i : I) (a : List (LayerData I)) : List (LayerData I) :=
  [([], Shape.cup i, [dn i])] ++ a.map (whL [dn i] [dn i]) ++ [([dn i], Shape.cap i, [])]

theorem sChain_mateL (i : I) {a : List (LayerData I)} (ha : SChain [up i] a [up i]) :
    SChain [dn i] (mateL i a) [dn i] := by
  refine SChain.append (t' := [dn i, up i, dn i])
    (SChain.append (t' := [dn i, up i, dn i]) ⟨rfl, rfl⟩ ?_) ⟨rfl, rfl⟩
  simpa using ha.whisk [dn i] [dn i]

variable (Sc) in
/-- **Cup slide** (the mate form of Brundan–Ellis (2.3), first identity): a 2-morphism `a` on
the upward leg of the rightward cup `η : 1 → Fᵢ Eᵢ` equals its right mate on the downward leg. -/
theorem cl_cup_slide (i : I) (ν : X) {a : List (LayerData I)} (ha : SChain [up i] a [up i]) :
    cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ a.map (whL [dn i] [])) =
      cl D Sc ν [] [dn i, up i]
        ([([], Shape.cup i, [])] ++ (mateL i a).map (whL [] [up i])) := by
  -- Step 1: the second cup moves below the first (interchange of the two cups).
  have e0 : [([], Shape.cup i, [])] ++ (mateL i a).map (whL [] [up i]) =
      ([], Shape.cup i, []) :: ([], Shape.cup i, [dn i, up i]) ::
        (a.map (whL [dn i] [dn i, up i]) ++ [([dn i], Shape.cap i, [up i])]) := by
    simp [mateL, whL]
  have s1 : cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ (mateL i a).map (whL [] [up i])) =
      cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, []), ([dn i, up i], Shape.cup i, [])] ++
        a.map (whL [dn i] [dn i, up i]) ++ [([dn i], Shape.cap i, [up i])]) := by
    rw [e0, cl_swapRL_at _ 0 _ _ _ rfl (by simp [Shape.dom]) (by simp [Shape.dom, Shape.cod])]
    simp [Shape.parity, zsign_zero, swapRL, Shape.dom, Shape.cod]
  -- Step 2: `a` moves below the first cup (super interchange; the cup is even).
  have s2 : cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, []), ([dn i, up i], Shape.cup i, [])] ++
        a.map (whL [dn i] [dn i, up i]) ++ [([dn i], Shape.cap i, [up i])]) =
      cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ a.map (whL [dn i] []) ++
        [([dn i, up i], Shape.cup i, []), ([dn i], Shape.cap i, [up i])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := wt D ν []) (S := [up i])
      (T := [up i, dn i, up i]) [] [] (s := [up i]) (s' := [up i]) (t := []) (t' := [dn i, up i]) ha
      (B := [([], Shape.cup i, [])]) (by simp [Shape.dom, Shape.cod])
    have hz : parsum D [(([] : List (Letter I)), Shape.cup i, ([] : List (Letter I)))] = 0 := by
      simp [Shape.parity]
    rw [hz, mul_zero, zsign_zero, one_smul] at E
    have E' := congrArg (ctxL D Sc ν [] [dn i, up i] [([], Shape.cup i, [])] [dn i] []
      [([dn i], Shape.cap i, [up i])] [up i] [up i, dn i, up i]) E
    rw [ctxL_cl ν (by simp [Shape.dom, Shape.cod]) (by simp [Shape.dom, Shape.cod]),
      ctxL_cl ν (by simp [Shape.dom, Shape.cod]) (by simp [Shape.dom, Shape.cod])] at E'
    convert E'.symm using 2 <;> simp [whL, List.append_assoc]
  -- Step 3: the zigzag `(ε ⊗ 1) ∘ (1 ⊗ η) = 1` on the upward strand.
  have s3 : cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ a.map (whL [dn i] []) ++
        [([dn i, up i], Shape.cup i, []), ([dn i], Shape.cap i, [up i])]) =
      cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ a.map (whL [dn i] []) ++ []) := by
    have E := cl_zigE Sc i (wt D ν [])
    refine cl_step ν ([([], Shape.cup i, [])] ++ a.map (whL [dn i] [])) [] [dn i] [] E ?_
      rfl (by simp [whL]) (by simp)
    refine SChain.append (t' := [dn i, up i]) ⟨rfl, rfl⟩ ?_
    simpa using ha.whisk [dn i] []
  rw [s1, s2, s3, List.append_nil]

variable (Sc) in
/-- **Cap slide** (the mate form of Brundan–Ellis (2.3), second identity): a 2-morphism `a` on
the upward leg of the rightward cap `ε : Eᵢ Fᵢ → 1` equals its right mate on the downward leg. -/
theorem cl_cap_slide (i : I) (ν : X) {a : List (LayerData I)} (ha : SChain [up i] a [up i]) :
    cl D Sc ν [up i, dn i] [] (a.map (whL [] [dn i]) ++ [([], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] []
        ((mateL i a).map (whL [up i] []) ++ [([], Shape.cap i, [])]) := by
  -- Step 1: the outer cap moves below the cap of the mate.
  have e0 : (mateL i a).map (whL [up i] []) ++ [([], Shape.cap i, [])] =
      ([([up i], Shape.cup i, [dn i])] ++ a.map (whL [up i, dn i] [dn i])) ++
        ([up i, dn i], Shape.cap i, []) :: ([], Shape.cap i, []) :: [] := by
    simp [mateL, whL]
  have hpre : SChain [up i, dn i] ([([up i], Shape.cup i, [dn i])] ++ a.map (whL [up i, dn i] [dn i]))
      [up i, dn i, up i, dn i] := by
    refine SChain.append (t' := [up i, dn i, up i, dn i]) ⟨rfl, rfl⟩ ?_
    simpa using ha.whisk [up i, dn i] [dn i]
  have hlen : ([([up i], Shape.cup i, [dn i])] ++ a.map (whL [up i, dn i] [dn i])).length =
      a.length + 1 := by simp
  have s1 : cl D Sc ν [up i, dn i] [] ((mateL i a).map (whL [up i] []) ++ [([], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] [] ([([up i], Shape.cup i, [dn i])] ++ a.map (whL [up i, dn i] [dn i]) ++
        [([], Shape.cap i, [up i, dn i]), ([], Shape.cap i, [])]) := by
    rw [e0, cl_swapRL_at _ (a.length + 1) ([up i, dn i], Shape.cap i, []) ([], Shape.cap i, []) []
      (by rw [← hlen, List.drop_left]) (by simp [Shape.dom]) (by simp [Shape.dom, Shape.cod])]
    rw [← hlen, List.take_left]
    simp [Shape.parity, zsign_zero, swapRL, Shape.dom, Shape.cod]
  -- Step 2: the outer cap moves below `a` (super interchange; the cap is even).
  have s2 : cl D Sc ν [up i, dn i] [] ([([up i], Shape.cup i, [dn i])] ++
        a.map (whL [up i, dn i] [dn i]) ++ [([], Shape.cap i, [up i, dn i]), ([], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] [] ([([up i], Shape.cup i, [dn i]), ([], Shape.cap i, [up i, dn i])] ++
        a.map (whL [] [dn i]) ++ [([], Shape.cap i, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn i]) (T := [])
      [([up i], Shape.cup i, [dn i])] [([], Shape.cap i, [])] [] [] (Shape.cap i)
      (t₀ := [up i, dn i]) (t₁ := [up i, dn i]) (B := a.map (whL [] [dn i]))
      (by simpa using ha.whisk [] [dn i])
    simp only [Shape.parity, zero_mul, zsign_zero, one_smul] at E
    convert E.symm using 2 <;> simp [whL, Shape.dom, Shape.cod, List.append_assoc]
  -- Step 3: the zigzag `(ε ⊗ 1) ∘ (1 ⊗ η) = 1` on the upward strand, with `Fᵢ` on the right.
  have s3 : cl D Sc ν [up i, dn i] [] ([([up i], Shape.cup i, [dn i]), ([], Shape.cap i, [up i, dn i])] ++
        a.map (whL [] [dn i]) ++ [([], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn i] [] ([] ++ a.map (whL [] [dn i]) ++ [([], Shape.cap i, [])]) := by
    have E := cl_zigE Sc i (wt D ν [dn i])
    refine cl_step ν [] (a.map (whL [] [dn i]) ++ [([], Shape.cap i, [])]) [] [dn i] E rfl ?_
      (by simp [whL]) (by simp)
    refine SChain.append (t' := [up i, dn i]) (by simpa using ha.whisk [] [dn i]) ⟨rfl, rfl⟩
  rw [s1, s2, s3, List.nil_append]

variable (Sc) in
/-- **Composition of right mates**: `mate(a) ≫ mate(b) = (-1)^{|a||b|} mate(b ≫ a)`, where
`b ≫ a` is `b` followed by `a` on the upward strand. -/
theorem cl_mate_comp (i : I) (ν : X) {a b : List (LayerData I)} (ha : SChain [up i] a [up i])
    (hb : SChain [up i] b [up i]) :
    cl D Sc ν [dn i] [dn i] (mateL i a ++ mateL i b) =
      zsign k (parsum D a * parsum D b) • cl D Sc ν [dn i] [dn i] (mateL i (b ++ a)) := by
  set c := Shape.cup i
  set κ := Shape.cap i
  have hc0 : c.parity D = 0 := rfl
  have hk0 : κ.parity D = 0 := rfl
  -- A: the second cup moves below the first cap.
  have sA : cl D Sc ν [dn i] [dn i] (mateL i a ++ mateL i b) =
      cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ a.map (whL [dn i] [dn i]) ++
        [([], c, [dn i, up i, dn i]), ([dn i, up i, dn i], κ, [])] ++
        b.map (whL [dn i] [dn i]) ++ [([dn i], κ, [])]) := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [dn i] [dn i]
      ([([], c, [dn i])] ++ a.map (whL [dn i] [dn i]))
      (b.map (whL [dn i] [dn i]) ++ [([dn i], κ, [])]) [] [dn i] [] c κ
    rw [hc0, zero_mul, zsign_zero, one_smul] at E
    simp only [mateL, List.append_assoc, List.cons_append, List.nil_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil, c, κ, Shape.dom, Shape.cod] at E
    rw [← E]
  -- B: `b` moves below the cap `([dn, up, dn], κ, [])`.
  have sB : cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ a.map (whL [dn i] [dn i]) ++
        [([], c, [dn i, up i, dn i]), ([dn i, up i, dn i], κ, [])] ++
        b.map (whL [dn i] [dn i]) ++ [([dn i], κ, [])]) =
      cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ a.map (whL [dn i] [dn i]) ++
        [([], c, [dn i, up i, dn i])] ++ b.map (whL [dn i] [dn i, up i, dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn i]) (T := [dn i])
      ([([], c, [dn i])] ++ a.map (whL [dn i] [dn i]) ++ [([], c, [dn i, up i, dn i])])
      [([dn i], κ, [])] (s := [dn i, up i]) (s' := [dn i, up i]) (t := [dn i, up i, dn i])
      (t' := [dn i]) (A := b.map (whL [dn i] [])) (B := [([dn i], κ, [])])
      (by simpa using hb.whisk [dn i] []) (by simp [κ, Shape.dom, Shape.cod])
    simp only [parsum_cons, parsum_nil, hk0, add_zero, mul_zero, zsign_zero, one_smul,
      map_whL_map_whL] at E
    simp only [List.map_cons, List.map_nil, whL, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] at E ⊢
    exact E.symm
  -- C: the second cup moves below `a`.
  have sC : cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ a.map (whL [dn i] [dn i]) ++
        [([], c, [dn i, up i, dn i])] ++ b.map (whL [dn i] [dn i, up i, dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) =
      cl D Sc ν [dn i] [dn i] ([([], c, [dn i]), ([], c, [dn i, up i, dn i])] ++
        a.map (whL [dn i, up i, dn i] [dn i]) ++ b.map (whL [dn i] [dn i, up i, dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [dn i]) (T := [dn i])
      [([], c, [dn i])] (b.map (whL [dn i] [dn i, up i, dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) [] [] c
      (t₀ := [dn i, up i, dn i]) (t₁ := [dn i, up i, dn i]) (B := a.map (whL [dn i] [dn i]))
      (by simpa using ha.whisk [dn i] [dn i])
    simp only [hc0, zero_mul, zsign_zero, one_smul, map_whL_map_whL] at E
    simp only [c, Shape.dom, Shape.cod, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E ⊢
    exact E.symm
  -- D: `a` and `b` are exchanged (sign `(-1)^{|a||b|}`).
  have sD : cl D Sc ν [dn i] [dn i] ([([], c, [dn i]), ([], c, [dn i, up i, dn i])] ++
        a.map (whL [dn i, up i, dn i] [dn i]) ++ b.map (whL [dn i] [dn i, up i, dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) =
      zsign k (parsum D a * parsum D b) •
      cl D Sc ν [dn i] [dn i] ([([], c, [dn i]), ([], c, [dn i, up i, dn i])] ++
        b.map (whL [dn i] [dn i, up i, dn i]) ++ a.map (whL [dn i, up i, dn i] [dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn i]) (T := [dn i])
      [([], c, [dn i]), ([], c, [dn i, up i, dn i])]
      [([dn i, up i, dn i], κ, []), ([dn i], κ, [])] (s := [dn i, up i]) (s' := [dn i, up i])
      (t := [dn i, up i, dn i]) (t' := [dn i, up i, dn i]) (A := b.map (whL [dn i] []))
      (B := a.map (whL [dn i] [dn i])) (by simpa using hb.whisk [dn i] [])
      (by simpa using ha.whisk [dn i] [dn i])
    simp only [parsum_map_whL, map_whL_map_whL, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E ⊢
    rw [E, smul_smul, ← zsign_add, mul_comm (parsum D b), ← two_mul,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero, one_smul]
  -- E: the first cup moves above the second cup and `b`.
  have sE : cl D Sc ν [dn i] [dn i] ([([], c, [dn i]), ([], c, [dn i, up i, dn i])] ++
        b.map (whL [dn i] [dn i, up i, dn i]) ++ a.map (whL [dn i, up i, dn i] [dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) =
      cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++
        [([dn i, up i], c, [dn i])] ++ a.map (whL [dn i, up i, dn i] [dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) := by
    have E1 := cl_swap_ctx (Sc := Sc) (μ := ν) [dn i] [dn i] []
      (b.map (whL [dn i] [dn i, up i, dn i]) ++ a.map (whL [dn i, up i, dn i] [dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) [] [] [dn i] c c
    simp only [hc0, zero_mul, zsign_zero, one_smul, c, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append, List.append_assoc] at E1
    have E2 := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn i]) (T := [dn i])
      [([], c, [dn i])] (a.map (whL [dn i, up i, dn i] [dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) (s := [dn i, up i]) (s' := [dn i, up i])
      (t := [dn i]) (t' := [dn i, up i, dn i]) (A := b.map (whL [dn i] []))
      (B := [([], c, [dn i])]) (by simpa using hb.whisk [dn i] []) (by simp [c, Shape.dom, Shape.cod])
    simp only [parsum_cons, parsum_nil, hc0, add_zero, mul_zero, zsign_zero, one_smul,
      map_whL_map_whL] at E2
    simp only [c, List.map_cons, List.map_nil, whL, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] at E1 E2 ⊢
    rw [← E1, ← E2]
  -- F: the last cap moves below the other cap and `a`.
  have sF : cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++
        [([dn i, up i], c, [dn i])] ++ a.map (whL [dn i, up i, dn i] [dn i]) ++
        [([dn i, up i, dn i], κ, []), ([dn i], κ, [])]) =
      cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++
        [([dn i, up i], c, [dn i]), ([dn i], κ, [up i, dn i])] ++ a.map (whL [dn i] [dn i]) ++
        [([dn i], κ, [])]) := by
    have E1 := cl_swap_ctx' (Sc := Sc) (μ := ν) [dn i] [dn i]
      ([([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++ [([dn i, up i], c, [dn i])] ++
        a.map (whL [dn i, up i, dn i] [dn i])) [] [dn i] [] [] κ κ
    simp only [hk0, zero_mul, zsign_zero, one_smul, κ, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append, List.append_assoc] at E1
    have E2 := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [dn i]) (T := [dn i])
      ([([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++ [([dn i, up i], c, [dn i])])
      [([dn i], κ, [])] [dn i] [] κ (t₀ := [up i, dn i]) (t₁ := [up i, dn i])
      (B := a.map (whL [] [dn i])) (by simpa using ha.whisk [] [dn i])
    simp only [hk0, zero_mul, zsign_zero, one_smul, map_whL_map_whL] at E2
    simp only [κ, Shape.dom, Shape.cod, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E1 E2 ⊢
    rw [E1, ← E2]
  -- G: the zigzag on the upward strand.
  have sG : cl D Sc ν [dn i] [dn i] ([([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++
        [([dn i, up i], c, [dn i]), ([dn i], κ, [up i, dn i])] ++ a.map (whL [dn i] [dn i]) ++
        [([dn i], κ, [])]) =
      cl D Sc ν [dn i] [dn i] (mateL i (b ++ a)) := by
    have E := cl_zigE Sc i (wt D ν [dn i])
    have := cl_step ν (pre := [([], c, [dn i])] ++ b.map (whL [dn i] [dn i]))
      (post := a.map (whL [dn i] [dn i]) ++ [([dn i], κ, [])]) [dn i] [dn i] E
      (L := [([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++
        [([dn i, up i], c, [dn i]), ([dn i], κ, [up i, dn i])] ++ a.map (whL [dn i] [dn i]) ++
        [([dn i], κ, [])])
      (L' := [([], c, [dn i])] ++ b.map (whL [dn i] [dn i]) ++ [] ++
        (a.map (whL [dn i] [dn i]) ++ [([dn i], κ, [])])) (s₀ := [dn i]) (t₀ := [dn i])
      (SChain.append (t' := [dn i, up i, dn i]) ⟨rfl, rfl⟩ (by simpa using hb.whisk [dn i] [dn i]))
      (SChain.append (t' := [dn i, up i, dn i]) (by simpa using ha.whisk [dn i] [dn i]) ⟨rfl, rfl⟩)
      (by simp [whL, c, κ]) rfl
    rw [this]
    simp [mateL, List.map_append, List.append_assoc, c, κ]
  rw [sA, sB, sC, sD, sE, sF, sG]

/-! ## Downward dots (2.1), (2.2) -/

/-- The downward dot on `Fᵢ` (2.1): the right mate of the upward dot. -/
def ddotL (i : I) : List (LayerData I) := mateL i (dotsL [] i [] 1)

theorem parsum_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    parsum D (dotsL u i v n) = (n : ZMod 2) * D.parity i := by
  simp [parsum, dotsL, Shape.parity, List.sum_replicate, nsmul_eq_mul]

theorem natCast_div_two_succ (n : ℕ) : (((n + 1) / 2 : ℕ) : ZMod 2) = ((n / 2 : ℕ) : ZMod 2) + n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  · rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

variable (Sc) in
/-- **Brundan–Ellis (2.2)**: the `n`-th power of the downward dot is `(-1)^{|i|⌊n/2⌋}` times the
right mate of the `n`-th power of the upward dot. -/
theorem cl_ddot_pow (i : I) (ν : X) (n : ℕ) :
    cpow (cl D Sc ν [dn i] [dn i] (ddotL i)) n =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [dn i] [dn i] (mateL i (dotsL [] i [] n)) := by
  have hd : ∀ m, SChain [up i] (dotsL [] i [] m) [up i] := fun m => sChain_dotsL [] i [] m
  induction n with
  | zero =>
    have := cl_zigF Sc i ν
    simp only [cpow_zero, Nat.zero_div, Nat.cast_zero, mul_zero, zsign_zero, one_smul]
    rw [show mateL i (dotsL [] i [] 0) = [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])] by
      simp [mateL, dotsL], this, cl_nil]
  | succ n ih =>
    rw [cpow_succ, ih, Linear.smul_comp, ddotL, cl_comp (sChain_mateL i (hd n)) (sChain_mateL i (hd 1)),
      cl_mate_comp Sc i ν (hd n) (hd 1), smul_smul, ← zsign_add, parsum_dotsL, parsum_dotsL,
      show dotsL [] i [] 1 ++ dotsL [] i [] n = dotsL [] i [] (n + 1) by
        simp [dotsL, List.replicate_succ]]
    congr 2
    rw [natCast_div_two_succ, Nat.cast_one, one_mul, mul_add]
    congr 1
    rw [mul_assoc, zmod2_mul_self, mul_comm]

/-- `n` downward dots on `Fᵢ`, as the `n`-fold concatenation of the downward dot. -/
def ddotsL (i : I) (n : ℕ) : List (LayerData I) := (List.replicate n (ddotL i)).flatten

theorem sChain_ddotL (i : I) : SChain [dn i] (ddotL i) [dn i] :=
  sChain_mateL i (sChain_dotsL [] i [] 1)

theorem sChain_ddotsL (i : I) (n : ℕ) : SChain [dn i] (ddotsL i n) [dn i] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ddotsL, List.replicate_succ', List.flatten_append, List.flatten_singleton]
    exact ih.append (sChain_ddotL i)

theorem cl_ddotsL (μ : X) (i : I) (n : ℕ) :
    cl D Sc μ [dn i] [dn i] (ddotsL i n) = cpow (cl D Sc μ [dn i] [dn i] (ddotL i)) n := by
  induction n with
  | zero => simp [ddotsL, cl_nil]
  | succ n ih =>
    rw [cpow_succ, ← ih, cl_comp (sChain_ddotsL i n) (sChain_ddotL i), ddotsL, ddotsL,
      List.replicate_succ', List.flatten_append, List.flatten_singleton]

variable (Sc) in
/-- **Brundan–Ellis (2.3), first identity**: `n` upward dots on the upward leg of the rightward cup
equal `(-1)^{|i|⌊n/2⌋}` times `n` downward dots on its downward leg. -/
theorem eq_2_3_a (i : I) (ν : X) (n : ℕ) :
    cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ (dotsL [] i [] n).map (whL [dn i] [])) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [] [dn i, up i] ([([], Shape.cup i, [])] ++ (ddotsL i n).map (whL [] [up i])) := by
  rw [cl_cup_slide Sc i ν (sChain_dotsL [] i [] n)]
  have E : cl D Sc (wt D ν [up i]) [dn i] [dn i] (ddotsL i n) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc (wt D ν [up i]) [dn i] [dn i] (mateL i (dotsL [] i [] n)) := by
    rw [cl_ddotsL, cl_ddot_pow]
  have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := []) (t₀ := [dn i, up i])
    [([], Shape.cup i, [])] [] [] [up i] E (L := [([], Shape.cup i, [])] ++ (ddotsL i n).map (whL [] [up i]) ++ [])
    ⟨rfl, rfl⟩ rfl rfl
  have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := []) (t₀ := [dn i, up i])
    (pre := [([], Shape.cup i, [])]) (u := []) (v := [up i]) (post := []) (s := [dn i])
    (t := [dn i]) ⟨rfl, rfl⟩ rfl (mateL i (dotsL [] i [] n))
  rw [List.append_nil] at h1
  rw [h1, map_smul, h2, List.append_nil, smul_smul, ← zsign_add, ← mul_add,
    ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, mul_zero, zsign_zero, one_smul]

variable (Sc) in
/-- **Brundan–Ellis (2.3), second identity**: `n` upward dots on the upward leg of the rightward
cap equal `(-1)^{|i|⌊n/2⌋}` times `n` downward dots on its downward leg. -/
theorem eq_2_3_b (i : I) (ν : X) (n : ℕ) :
    cl D Sc ν [up i, dn i] [] ((dotsL [] i [] n).map (whL [] [dn i]) ++ [([], Shape.cap i, [])]) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν [up i, dn i] [] ((ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])]) := by
  rw [cl_cap_slide Sc i ν (sChain_dotsL [] i [] n)]
  have E : cl D Sc (wt D ν []) [dn i] [dn i] (ddotsL i n) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc (wt D ν []) [dn i] [dn i] (mateL i (dotsL [] i [] n)) := by
    rw [cl_ddotsL, cl_ddot_pow]
  have h1 := cl_stepL (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [])
    [] [([], Shape.cap i, [])] [up i] [] E
    (L := [] ++ (ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])]) rfl ⟨rfl, rfl⟩ rfl
  have h2 := ctxL_cl (D := D) (Sc := Sc) ν (s₀ := [up i, dn i]) (t₀ := [])
    (pre := []) (u := [up i]) (v := []) (post := [([], Shape.cap i, [])]) (s := [dn i])
    (t := [dn i]) rfl ⟨rfl, rfl⟩ (mateL i (dotsL [] i [] n))
  rw [List.nil_append] at h1 h2
  rw [h1, map_smul, h2, smul_smul, ← zsign_add, ← mul_add,
    ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, mul_zero, zsign_zero, one_smul]

/-! ## Pitchfork relations (2.4) -/

variable (Sc) in
/-- **Brundan–Ellis (2.4), first identity**: on `Eᵢ Eⱼ Fᵢ 1_λ`, the crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ`
followed by the rightward cap `ε` on the left equals the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`
followed by the rightward cap on the right. -/
theorem eq_2_4_a (i j : I) (ν : X) :
    cl D Sc ν [up i, up j, dn i] [up j]
        ((sigmaL i j).map (whL [up i] []) ++ [([], Shape.cap i, [up j])]) =
      cl D Sc ν [up i, up j, dn i] [up j]
        [([], Shape.cross i j, [dn i]), ([up j], Shape.cap i, [])] := by
  set c := Shape.cup i
  set κ := Shape.cap i
  have hk0 : κ.parity D = 0 := rfl
  -- the outer cap moves below the cap of `σ`
  have s1 : cl D Sc ν [up i, up j, dn i] [up j]
        ((sigmaL i j).map (whL [up i] []) ++ [([], κ, [up j])]) =
      cl D Sc ν [up i, up j, dn i] [up j]
        [([up i], c, [up j, dn i]), ([up i, dn i], Shape.cross i j, [dn i]),
          ([], κ, [up j, up i, dn i]), ([up j], κ, [])] := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [up i, up j, dn i] [up j]
      [([up i], c, [up j, dn i]), ([up i, dn i], Shape.cross i j, [dn i])] [] [] [up j] [] κ κ
    simp only [hk0, zero_mul, zsign_zero, one_smul, κ, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append] at E
    simp only [sigmaL, whL, List.map_cons, List.map_nil, κ, c, List.cons_append, List.nil_append,
      List.append_nil] at E ⊢
    exact E
  -- the outer cap moves below the crossing
  have s2 : cl D Sc ν [up i, up j, dn i] [up j]
        [([up i], c, [up j, dn i]), ([up i, dn i], Shape.cross i j, [dn i]),
          ([], κ, [up j, up i, dn i]), ([up j], κ, [])] =
      cl D Sc ν [up i, up j, dn i] [up j]
        [([up i], c, [up j, dn i]), ([], κ, [up i, up j, dn i]),
          ([], Shape.cross i j, [dn i]), ([up j], κ, [])] := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [up i, up j, dn i] [up j]
      [([up i], c, [up j, dn i])] [([up j], κ, [])] [] [] [dn i] κ (Shape.cross i j)
    simp only [hk0, zero_mul, zsign_zero, one_smul, κ, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append] at E
    simp only [κ, c] at E ⊢
    exact E
  -- the zigzag on the upward strand `Eᵢ`
  have s3 : cl D Sc ν [up i, up j, dn i] [up j]
        [([up i], c, [up j, dn i]), ([], κ, [up i, up j, dn i]),
          ([], Shape.cross i j, [dn i]), ([up j], κ, [])] =
      cl D Sc ν [up i, up j, dn i] [up j]
        ([] ++ [([], Shape.cross i j, [dn i]), ([up j], κ, [])]) := by
    have E := cl_zigE Sc i (wt D ν [up j, dn i])
    exact cl_step ν [] [([], Shape.cross i j, [dn i]), ([up j], κ, [])] [] [up j, dn i] E rfl
      (by simp [Shape.dom, Shape.cod, κ]) (by simp [whL, c, κ]) rfl
  rw [s1, s2, s3, List.nil_append]

variable (Sc) in
/-- **Brundan–Ellis (2.4), second identity**: on `Eⱼ 1_λ`, the rightward cup `η` (to the right of
`Eⱼ`) followed by the crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` equals the rightward cup (to the left of `Eⱼ`)
followed by the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`. -/
theorem eq_2_4_b (i j : I) (ν : X) :
    cl D Sc ν [up j] [dn i, up j, up i]
        ([([up j], Shape.cup i, [])] ++ (sigmaL i j).map (whL [] [up i])) =
      cl D Sc ν [up j] [dn i, up j, up i]
        [([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])] := by
  set c := Shape.cup i
  set κ := Shape.cap i
  have hc0 : c.parity D = 0 := rfl
  have s1 : cl D Sc ν [up j] [dn i, up j, up i]
        ([([up j], c, [])] ++ (sigmaL i j).map (whL [] [up i])) =
      cl D Sc ν [up j] [dn i, up j, up i]
        [([], c, [up j]), ([dn i, up i, up j], c, []), ([dn i], Shape.cross i j, [dn i, up i]),
          ([dn i, up j], κ, [up i])] := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [up j] [dn i, up j, up i] []
      [([dn i], Shape.cross i j, [dn i, up i]), ([dn i, up j], κ, [up i])] [] [up j] [] c c
    simp only [hc0, zero_mul, zsign_zero, one_smul, c, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append] at E
    simp only [sigmaL, whL, List.map_cons, List.map_nil, κ, c, List.cons_append, List.nil_append,
      List.append_nil] at E ⊢
    exact E
  have s2 : cl D Sc ν [up j] [dn i, up j, up i]
        [([], c, [up j]), ([dn i, up i, up j], c, []), ([dn i], Shape.cross i j, [dn i, up i]),
          ([dn i, up j], κ, [up i])] =
      cl D Sc ν [up j] [dn i, up j, up i]
        [([], c, [up j]), ([dn i], Shape.cross i j, []), ([dn i, up j, up i], c, []),
          ([dn i, up j], κ, [up i])] := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [up j] [dn i, up j, up i] [([], c, [up j])]
      [([dn i, up j], κ, [up i])] [dn i] [] [] (Shape.cross i j) c
    simp only [hc0, mul_zero, zsign_zero, one_smul, c, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append] at E
    simp only [c] at E ⊢
    exact E
  have s3 : cl D Sc ν [up j] [dn i, up j, up i]
        [([], c, [up j]), ([dn i], Shape.cross i j, []), ([dn i, up j, up i], c, []),
          ([dn i, up j], κ, [up i])] =
      cl D Sc ν [up j] [dn i, up j, up i]
        ([([], c, [up j]), ([dn i], Shape.cross i j, [])] ++ []) := by
    have E := cl_zigE Sc i (wt D ν [])
    exact cl_step ν [([], c, [up j]), ([dn i], Shape.cross i j, [])] [] [dn i, up j] [] E
      (by simp [Shape.dom, Shape.cod, c]) rfl (by simp [whL, c, κ]) rfl
  rw [s1, s2, s3, List.append_nil]

/-! ## Downward crossings (2.1) and the pitchfork relations (2.5) -/

/-- The downward crossing `Fᵢ Fⱼ → Fⱼ Fᵢ` (2.1), the right mate of `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`: the cup
`η` of colour `j` on the left, the crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` (1.11), the cap `ε` of colour `j`
on the right. -/
def dcrossL (i j : I) : List (LayerData I) :=
  [([], Shape.cup j, [dn i, dn j])] ++ (sigmaL i j).map (whL [dn j] [dn j]) ++
    [([dn j, dn i], Shape.cap j, [])]

theorem sChain_dcrossL (i j : I) : SChain [dn i, dn j] (dcrossL i j) [dn j, dn i] := by
  refine SChain.append (t' := [dn j, dn i, up j, dn j])
    (SChain.append (t' := [dn j, up j, dn i, dn j]) ⟨rfl, rfl⟩ ?_) ⟨rfl, rfl⟩
  simpa using (sChain_sigmaL i j).whisk [dn j] [dn j]

theorem parsum_sigmaL (i j : I) : parsum D (sigmaL i j) = D.parity i * D.parity j := by
  simp [parsum, sigmaL, Shape.parity]

variable (Sc) in
/-- **Brundan–Ellis (2.5), first identity**: on `Fⱼ 1_λ`, the rightward cup `η` of colour `i`
(to the left of `Fⱼ`) followed by `σ : Eᵢ Fⱼ → Fⱼ Eᵢ` equals the rightward cup (to the right of
`Fⱼ`) followed by the downward crossing `Fⱼ Fᵢ → Fᵢ Fⱼ`. -/
theorem eq_2_5_a (i j : I) (ν : X) :
    cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([], Shape.cup i, [dn j])] ++ (sigmaL j i).map (whL [dn i] [])) =
      cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([dn j], Shape.cup i, [])] ++ (dcrossL j i).map (whL [] [up i])) := by
  set c := Shape.cup i
  set κ := Shape.cap i
  have hc0 : c.parity D = 0 := rfl
  have hσ := sChain_sigmaL j i
  -- the two cups are exchanged
  have s1 : cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([dn j], c, [])] ++ (dcrossL j i).map (whL [] [up i])) =
      cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([], c, [dn j]), ([dn i, up i, dn j], c, [])] ++ (sigmaL j i).map (whL [dn i] [dn i, up i]) ++
          [([dn i, dn j], κ, [up i])]) := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [dn j] [dn i, dn j, up i] []
      ((sigmaL j i).map (whL [dn i] [dn i, up i]) ++ [([dn i, dn j], κ, [up i])]) [] [dn j] [] c c
    simp only [hc0, zero_mul, zsign_zero, one_smul, c, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append] at E
    simp only [dcrossL, map_whL_map_whL, List.map_append, List.map_cons, List.map_nil, whL, c, κ,
      List.cons_append, List.nil_append, List.append_nil] at E ⊢
    exact E
  -- the cup on the right moves above `σ`
  have s2 : cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([], c, [dn j]), ([dn i, up i, dn j], c, [])] ++ (sigmaL j i).map (whL [dn i] [dn i, up i]) ++
          [([dn i, dn j], κ, [up i])]) =
      cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([], c, [dn j])] ++ (sigmaL j i).map (whL [dn i] []) ++
          [([dn i, dn j, up i], c, []), ([dn i, dn j], κ, [up i])]) := by
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := [dn j]) (T := [dn i, dn j, up i])
      [([], c, [dn j])] [([dn i, dn j], κ, [up i])] (s := [dn i, up i, dn j])
      (s' := [dn i, dn j, up i]) (t := []) (t' := [dn i, up i]) (A := (sigmaL j i).map (whL [dn i] []))
      (B := [([], c, [])]) (by simpa using hσ.whisk [dn i] []) ⟨rfl, rfl⟩
    simp only [parsum_cons, parsum_nil, hc0, add_zero, mul_zero, zsign_zero, one_smul,
      map_whL_map_whL] at E
    simp only [List.map_cons, List.map_nil, whL, c, κ, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] at E ⊢
    exact E.symm
  -- the zigzag on the upward strand `Eᵢ`
  have s3 : cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([], c, [dn j])] ++ (sigmaL j i).map (whL [dn i] []) ++
          [([dn i, dn j, up i], c, []), ([dn i, dn j], κ, [up i])]) =
      cl D Sc ν [dn j] [dn i, dn j, up i]
        ([([], c, [dn j])] ++ (sigmaL j i).map (whL [dn i] []) ++ []) := by
    have E := cl_zigE Sc i (wt D ν [])
    refine cl_step ν ([([], c, [dn j])] ++ (sigmaL j i).map (whL [dn i] [])) [] [dn i, dn j] [] E
      ?_ rfl (by simp [whL, c, κ]) rfl
    exact SChain.append (t' := [dn i, up i, dn j]) ⟨rfl, rfl⟩ (by simpa using hσ.whisk [dn i] [])
  rw [s1, s2, s3, List.append_nil]

variable (Sc) in
/-- **Brundan–Ellis (2.5), second identity**: on `Eᵢ Fⱼ Fᵢ 1_λ`, the crossing
`σ : Eᵢ Fⱼ → Fⱼ Eᵢ` followed by the rightward cap `ε` of colour `i` on the right equals the
downward crossing `Fⱼ Fᵢ → Fᵢ Fⱼ` followed by the rightward cap on the left. -/
theorem eq_2_5_b (i j : I) (ν : X) :
    cl D Sc ν [up i, dn j, dn i] [dn j]
        ((sigmaL j i).map (whL [] [dn i]) ++ [([dn j], Shape.cap i, [])]) =
      cl D Sc ν [up i, dn j, dn i] [dn j]
        ((dcrossL j i).map (whL [up i] []) ++ [([], Shape.cap i, [dn j])]) := by
  set c := Shape.cup i
  set κ := Shape.cap i
  have hk0 : κ.parity D = 0 := rfl
  have hσ := sChain_sigmaL j i
  -- the outer cap moves below the cap of the downward crossing
  have s1 : cl D Sc ν [up i, dn j, dn i] [dn j]
        ((dcrossL j i).map (whL [up i] []) ++ [([], κ, [dn j])]) =
      cl D Sc ν [up i, dn j, dn i] [dn j]
        ([([up i], c, [dn j, dn i])] ++ (sigmaL j i).map (whL [up i, dn i] [dn i]) ++
          [([], κ, [dn j, up i, dn i]), ([dn j], κ, [])]) := by
    have E := cl_swap_ctx' (Sc := Sc) (μ := ν) [up i, dn j, dn i] [dn j]
      ([([up i], c, [dn j, dn i])] ++ (sigmaL j i).map (whL [up i, dn i] [dn i])) [] [] [dn j] [] κ κ
    simp only [hk0, zero_mul, zsign_zero, one_smul, κ, Shape.dom, Shape.cod, List.append_nil,
      List.nil_append, List.cons_append] at E
    simp only [dcrossL, map_whL_map_whL, List.map_append, List.map_cons, List.map_nil, whL, c, κ,
      List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at E ⊢
    exact E
  -- the outer cap moves below `σ`
  have s2 : cl D Sc ν [up i, dn j, dn i] [dn j]
        ([([up i], c, [dn j, dn i])] ++ (sigmaL j i).map (whL [up i, dn i] [dn i]) ++
          [([], κ, [dn j, up i, dn i]), ([dn j], κ, [])]) =
      cl D Sc ν [up i, dn j, dn i] [dn j]
        ([([up i], c, [dn j, dn i]), ([], κ, [up i, dn j, dn i])] ++
          (sigmaL j i).map (whL [] [dn i]) ++ [([dn j], κ, [])]) := by
    have E := cl_interchange_one (D := D) (Sc := Sc) (μ := ν) (S := [up i, dn j, dn i]) (T := [dn j])
      [([up i], c, [dn j, dn i])] [([dn j], κ, [])] [] [] κ (t₀ := [up i, dn j, dn i])
      (t₁ := [dn j, up i, dn i]) (B := (sigmaL j i).map (whL [] [dn i]))
      (by simpa using hσ.whisk [] [dn i])
    simp only [hk0, zero_mul, zsign_zero, one_smul, map_whL_map_whL] at E
    simp only [κ, Shape.dom, Shape.cod, List.append_nil, List.nil_append, List.cons_append,
      List.append_assoc] at E ⊢
    exact E.symm
  -- the zigzag on the upward strand `Eᵢ`
  have s3 : cl D Sc ν [up i, dn j, dn i] [dn j]
        ([([up i], c, [dn j, dn i]), ([], κ, [up i, dn j, dn i])] ++
          (sigmaL j i).map (whL [] [dn i]) ++ [([dn j], κ, [])]) =
      cl D Sc ν [up i, dn j, dn i] [dn j]
        ([] ++ (sigmaL j i).map (whL [] [dn i]) ++ [([dn j], κ, [])]) := by
    have E := cl_zigE Sc i (wt D ν [dn j, dn i])
    refine cl_step ν [] ((sigmaL j i).map (whL [] [dn i]) ++ [([dn j], κ, [])]) [] [dn j, dn i] E
      rfl ?_ (by simp [whL, c, κ]) (by simp)
    exact SChain.append (t' := [dn j, up i, dn i]) (by simpa using hσ.whisk [] [dn i]) ⟨rfl, rfl⟩
  rw [s1, s2, s3, List.nil_append]

end OddMath.SKM
