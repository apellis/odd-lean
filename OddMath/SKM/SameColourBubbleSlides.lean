/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlidesConnected
/-!
# Same-colour bubble slides

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 7.3(i–ii), (7.7)–(7.10), for every nonnegative shifted degree
and every weight. Both genuine and fake bubbles are included.

The natural counterclockwise family at nonnegative weight is obtained by
closing the cup pitchfork and evaluating the two-crossing dotted curl.
The clockwise family at negative weight follows from (6.3); its boundary
correction at coroot value −1 is retained. Ordered inverse-series uniqueness
then supplies the opposite family in each range. The finite sign sums give
`r+1` for even colour, and `2r+1` at even dot counts for odd colour.
No relation is added and no scalar is specialized.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- Same-colour closure of the cup pitchfork, before evaluating curls. -/
private theorem pcuL_b_same (i : I) (μ : X) (n : ℕ) :
    pcuL cs i i μ ≫ pcuS i i μ ≫ pcuB i i μ n =
      zsign k (D.parity i * (n : ZMod 2)) •
        (reta cs i μ ≫ ∑ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
          cl D Sc μ [up i, up i, dn i] [up i]
            (tauEEF i ++ dotsL [] i [up i, dn i] (n - 1 - s) ++
              dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])])) := by
  have ht := sChain_tauEEF i
  have hs : SChain [up i, up i, dn i] ((sigmaL i i).map (whL [up i] []))
      [up i, dn i, up i] := by simpa using (sChain_sigmaL i i).whisk [up i] []
  have he : SChain [up i, dn i, up i] ((epsL i n).map (whL [] [up i])) [up i] := by
    simpa using (sChain_epsL i n).whisk [] [up i]
  rw [pcuL, pcuS, pcuB, Category.assoc, cl_comp hs he,
    show crossL [] i i [dn i] = tauEEF i from rfl,
    cl_comp ht (hs.append he), ← List.append_assoc, tau_sigma_epsL, tau_dots_tau,
    Linear.comp_smul]
  rfl

/-- The inversion on the right pair is minus the identity at nonnegative weight. -/
private theorem pcuT_S_same_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    pcuT (Sc := Sc) i i μ ≫ pcuS i i μ = -𝟙 _ := by
  have E := congrArg (plcL D Sc μ [up i] [] [dn i, up i] [dn i, up i])
    (eq_2_12_b Sc i (wt D μ []))
  rw [show (-D.h i (wt D μ [])).toNat = 0 by simp only [wt_nil]; omega,
    range_zero, sum_empty, zero_sub, map_neg, plcL_cl, plcL_cl, List.map_nil, cl_nil] at E
  rw [pcuT, pcuS, cl_comp (by simpa using (sChain_lcrossL i i).whisk [up i] [])
    (by simpa using (sChain_sigmaL i i).whisk [up i] []), ← List.map_append]
  exact E

private theorem pcuR_b_same_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (n : ℕ) :
    pcuR cs i i μ ≫ pcuS i i μ ≫ pcuB i i μ n =
      -bubbleL_left cs i i μ n := by
  rw [pcuR, Category.assoc, ← Category.assoc (pcuT i i μ), pcuT_S_same_nonneg i μ hh,
    Preadditive.neg_comp, Category.id_comp, Preadditive.comp_neg]
  congr 1
  rw [bubbleL_left, lbub, bubL_nat, plcL_comp_of_mem μ [] [up i] (etaP_mem cs i _)
    (cl_mem_homPar (sChain_epsL i n) rfl), plcL_cl]
  rfl

private theorem same_curl_term (i : I) (μ : X) (a s : ℕ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i]
      (tauEEF i ++ dotsL [] i [up i, dn i] a ++ dotsL [up i] i [dn i] s ++
        [([up i], Shape.cap i, [])]) =
      zsign k (D.parity i * (a : ZMod 2) * (s : ZMod 2)) •
        ((reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i]
          (tauEEF i ++ dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])])) ≫
            cl D Sc μ [up i] [up i] (dotsL [] i [] a)) := by
  have hI := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up i, up i, dn i]) (T := [up i]) (tauEEF i) []
    (sChain_dotsL [] i [] a) (sChain_epsL i s)
  have ex : (dotsL [] i [] a).map (whL [] [up i, dn i]) =
      dotsL [] i [up i, dn i] a := by simp [dotsL, whL]
  have ey : (epsL i s).map (whL [up i] []) =
      dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])] := by
    simp [epsL, dotsL, whL]
  have ez : (dotsL [] i [] a).map (whL [] []) = dotsL [] i [] a := by simp
  simp only [List.append_nil, List.nil_append, ex, ey, ez, parsum_dotsL, parsum_epsL] at hI
  have hp : (a : ZMod 2) * D.parity i * ((s : ZMod 2) * D.parity i) =
      D.parity i * (a : ZMod 2) * s := by
    rw [mul_mul_mul_comm, zmod2_mul_self']; ring
  rw [hp] at hI
  have hc : SChain [up i, up i, dn i]
      (tauEEF i ++ dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])]) [up i] := by
    exact ((sChain_tauEEF i).append (sChain_dotsL [up i] i [dn i] s)).append
      (by simp [Shape.dom, Shape.cod])
  simp only [List.append_assoc] at hI ⊢
  rw [hI, Linear.comp_smul]
  congr 1
  rw [Category.assoc]
  have E := cl_comp (D := D) (Sc := Sc) (μ := μ) hc (sChain_dotsL [] i [] a)
  simp only [List.append_assoc] at E
  erw [E]
  rfl

private theorem bubbleL_same_nested_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (n : ℕ) :
    bubbleL_left cs i i μ n =
      ∑ s ∈ range n, ∑ r ∈ range ((s : ℤ) - D.h i μ + 1).toNat,
        zsign k (D.parity i * ((n : ZMod 2) + s + (n - 1 - s : ℕ) * (s : ZMod 2) +
          (D.h i μ : ZMod 2) * r + 1)) •
          ((cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫
            rbub i μ (bubL cs i μ ((s : ℤ) - r - 1))) ≫
              cl D Sc μ [up i] [up i] (dotsL [] i [] (n - 1 - s))) := by
  have H := congrArg (fun f => f ≫ pcuS i i μ ≫ pcuB i i μ n) (eq_7_5_b cs i i μ)
  rw [pcuL_b_same, pcuR_b_same_nonneg cs i μ hh] at H
  have H' := congrArg Neg.neg H
  simp only [neg_neg] at H'
  rw [← H']
  simp only [Preadditive.comp_sum, Linear.comp_smul, same_curl_term, smul_sum, smul_smul]
  simp only [tauEEF, eq_5_20, Preadditive.neg_comp, Preadditive.sum_comp, Linear.smul_comp,
    smul_neg, smul_sum, smul_smul, Finset.sum_neg_distrib, neg_neg]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro r _
  rw [← zsign_add, ← zsign_add, ← zsign_add]
  congr 2
  ring

private theorem same_slide_L_term (i : I) (μ : X) (n s r : ℕ) (hs : s < n) :
    zsign k (D.parity i * ((n : ZMod 2) + s + (n - 1 - s : ℕ) * (s : ZMod 2) +
      (D.h i μ : ZMod 2) * r + 1)) •
      ((cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫
        rbub i μ (bubL cs i μ ((s : ℤ) - r - 1))) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] (n - 1 - s))) =
    zsign k (D.parity i * ((n - 1 - s + r : ℕ) : ZMod 2) * ((s + 1 : ℕ) : ZMod 2)) •
      (rbub i μ (bubL cs i μ ((s : ℤ) - r - 1)) ≫
        cl D Sc μ [up i] [up i] (dotsL [] i [] (n - 1 - s + r))) := by
  have hb := bub_dots_commR i μ (bubL_mem cs i (wt D μ []) ((s : ℤ) - r - 1)) r
  have hb' := congrArg (zsign k
    ((D.parity i * (((s : ℤ) - r - 1 + D.h i μ + 1 : ℤ) : ZMod 2)) *
      ((r : ZMod 2) * D.parity i)) • ·) hb
  simp only [wt_nil, smul_smul, zsign_mul_self', one_smul] at hb'
  rw [← hb', Linear.smul_comp, smul_smul, ← zsign_add, Category.assoc, cl_dots_dots,
    Nat.add_comm r]
  congr 2
  have hn : n = (n - 1 - s) + s + 1 := by omega
  have he : (n : ZMod 2) = ((n - 1 - s : ℕ) : ZMod 2) + s + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun m : ℕ => (m : ZMod 2)) hn
  push_cast
  rw [he]
  generalize D.parity i = p
  generalize ((n - 1 - s : ℕ) : ZMod 2) = a
  generalize (s : ZMod 2) = b
  generalize (r : ZMod 2) = c
  generalize ((D.h i μ : ℤ) : ZMod 2) = h
  revert p a b c h
  decide

private theorem same_triangle_reindex {M : Type*} [AddCommMonoid M]
    (n N h : ℕ) (hn : n = N + h + 1) (f : ℕ → ℕ → M) :
    (∑ s ∈ range n, ∑ r ∈ range ((s : ℤ) - h + 1).toNat,
      f (n - 1 - s + r) (n - 1 - s)) =
      ∑ t ∈ range (N + 1), ∑ a ∈ range (t + 1), f t a := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨n - 1 - x.1 + x.2, n - 1 - x.1⟩)
    (fun x => ⟨n - 1 - x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨s, r⟩ hm
    simp only [mem_sigma, mem_range] at hm ⊢
    omega
  · rintro ⟨t, a⟩ hm
    simp only [mem_sigma, mem_range] at hm ⊢
    omega
  · rintro ⟨s, r⟩ hm
    simp only [mem_sigma, mem_range] at hm
    dsimp only
    congr 1 <;> omega
  · rintro ⟨t, a⟩ hm
    simp only [mem_sigma, mem_range] at hm
    dsimp only
    congr 1 <;> omega
  · intro x _
    rfl

include Sc in
private theorem same_slide_coefficient (i : I) (n t : ℕ) (ht : t < n) :
    (∑ a ∈ range (t + 1), zsign k (D.parity i * (t : ZMod 2) * ((n - a : ℕ) : ZMod 2))) =
      if D.parity i * (t : ZMod 2) = 0 then (t + 1 : k) else 0 := by
  by_cases hp : D.parity i * (t : ZMod 2) = 0
  · simp [hp, zsign_zero]
  rw [ite_eq_right hp]
  have hi : D.parity i = 1 := by
    rcases zmod2_cases (D.parity i) with h | h
    · simp [h] at hp
    · exact h
  have ht' : (t : ZMod 2) = 1 := by
    rcases zmod2_cases (t : ZMod 2) with h | h
    · simp [h] at hp
    · exact h
  have hf (a : ℕ) (ha : a ∈ range (t + 1)) :
      zsign k (D.parity i * (t : ZMod 2) * ((n - (t + 1 - 1 - a) : ℕ) : ZMod 2)) =
        -zsign k (D.parity i * (t : ZMod 2) * ((n - a : ℕ) : ZMod 2)) := by
    have ha' : a ≤ t := by have := mem_range.mp ha; omega
    simp only [Nat.add_sub_cancel, hi, ht', one_mul]
    rw [Nat.cast_sub (by omega : t - a ≤ n), Nat.cast_sub ha', Nat.cast_sub (by omega : a ≤ n), ht']
    have he : (n : ZMod 2) - (1 - a) = 1 + ((n : ZMod 2) - a) := by
      generalize (n : ZMod 2) = b
      generalize (a : ZMod 2) = c
      revert b c
      decide
    rw [he, zsign_add, zsign_one', neg_one_mul]
  have H := sum_range_reflect
    (fun a => zsign k (D.parity i * (t : ZMod 2) * ((n - a : ℕ) : ZMod 2))) (t + 1)
  rw [sum_congr rfl hf, sum_neg_distrib, neg_eq_iff_add_eq_zero, ← two_mul] at H
  exact (Sc.two_isUnit ⟨i, hi⟩).mul_left_cancel (by simpa using H)

private theorem bubbleL_same_shift_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (N : ℕ) :
    lbub i μ (bubLs cs i (wt D μ [up i]) N) =
      ∑ t ∈ range (N + 1), (if D.parity i * (t : ZMod 2) = 0 then (t + 1 : k) else 0) •
        (rbub i μ (bubLs cs i (wt D μ []) ((N : ℤ) - t)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] t)) := by
  let h := (D.h i μ).toNat
  let n := N + h + 1
  have hh' : (h : ℤ) = D.h i μ := Int.toNat_of_nonneg hh
  have hn : n = N + h + 1 := rfl
  have H := bubbleL_same_nested_nonneg cs i μ hh n
  have hl : lbub i μ (bubLs cs i (wt D μ [up i]) N) = bubbleL_left cs i i μ n := by
    simp only [bubLs, bubbleL_left, h_wt_up]
    congr 2
    dsimp [n]
    omega
  rw [hl, H]
  let f := fun (t a : ℕ) => zsign k (D.parity i * (t : ZMod 2) * ((n - a : ℕ) : ZMod 2)) •
    (rbub i μ (bubLs cs i (wt D μ []) ((N : ℤ) - t)) ≫
      cl D Sc μ [up i] [up i] (dotsL [] i [] t))
  have hsums : (∑ s ∈ range n, ∑ r ∈ range ((s : ℤ) - D.h i μ + 1).toNat,
      zsign k (D.parity i * ((n : ZMod 2) + s + (n - 1 - s : ℕ) * (s : ZMod 2) +
        (D.h i μ : ZMod 2) * r + 1)) •
        ((cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫
          rbub i μ (bubL cs i μ ((s : ℤ) - r - 1))) ≫
            cl D Sc μ [up i] [up i] (dotsL [] i [] (n - 1 - s)))) =
      ∑ s ∈ range n, ∑ r ∈ range ((s : ℤ) - h + 1).toNat,
        f (n - 1 - s + r) (n - 1 - s) := by
    rw [hh']
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro r _
    rw [same_slide_L_term cs i μ n s r (mem_range.mp hs)]
    dsimp only [f]
    have ha : n - (n - 1 - s) = s + 1 := by have := mem_range.mp hs; omega
    rw [ha]
    congr 2
    congr 1
    simp only [bubLs, wt_nil]
    congr 1
    have ha' : ((n - 1 - s : ℕ) : ℤ) = (n : ℤ) - 1 - s := by
      have := mem_range.mp hs
      omega
    push_cast
    rw [ha']
    have hn' : (n : ℤ) = N + h + 1 := by exact_mod_cast hn
    omega
  rw [hsums, same_triangle_reindex n N h hn]
  apply sum_congr rfl
  intro t ht
  dsimp only [f]
  rw [← sum_smul, same_slide_coefficient (Sc := Sc) i n t (by
    have := mem_range.mp ht
    omega)]

private theorem bubbleR_same_curls_nonpos (i : I) (μ : X) (hh : D.h i μ ≤ -1) (n : ℕ) :
    bubbleR_right cs i i μ n =
      (∑ s ∈ range n, zsign k (D.parity i * (n - 1 - s : ℕ) * (D.parity i * s) + D.parity i * s) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] s) ≫ curl18 cs i μ (n - 1 - s))) +
      dsc cs i μ • cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
  have H := congrArg (T2 (Sc := Sc) i μ n ≫ ·) (eq_6_3 cs i μ hh)
  have eT2 : T2 i μ n = plcL D Sc μ [up i] [] [] [dn i, up i]
      (cl D Sc (wt D μ []) [] [dn i, up i] (etaL i n)) := by rw [plcL_cl]; rfl
  have hR1 : T2 i μ n ≫ reps cs i μ = bubbleR_right cs i i μ n := by
    rw [eT2, reps, ← plcL_comp_of_mem μ [up i] [] (etaL_mem i _ n) (epsP_mem cs i _), ← bubR_nat]
    rfl
  have hR2 : T2 i μ n ≫ cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])] =
      cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
    rw [eT2]; exact etaL_capR i μ n
  rw [Preadditive.comp_neg, T2_L63, neg_neg, Preadditive.comp_sub, Linear.comp_smul, hR1, hR2] at H
  exact (eq_sub_iff_add_eq.mp H).symm

private theorem same_slide_R_term (i : I) (μ : X) (a s r : ℕ) :
    zsign k (D.parity i * (a : ZMod 2) * (D.parity i * s) + D.parity i * s) •
      (cl D Sc μ [up i] [up i] (dotsL [] i [] s) ≫
        (zsign k (D.parity i * (D.h i μ : ZMod 2) * r) •
          (lbub i μ (bubR cs i (wt D μ [up i]) ((a : ℤ) - r - 1)) ≫
            cl D Sc μ [up i] [up i] (dotsL [] i [] r)))) =
      zsign k (D.parity i * ((s + r : ℕ) : ZMod 2) * ((D.h i μ : ZMod 2) + s)) •
        (lbub i μ (bubR cs i (wt D μ [up i]) ((a : ℤ) - r - 1)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] (s + r))) := by
  rw [Linear.comp_smul, smul_smul, ← Category.assoc,
    dots_bub_comm i μ (bubR_mem cs i (wt D μ [up i]) ((a : ℤ) - r - 1)) s,
    Linear.smul_comp, smul_smul, ← zsign_add, ← zsign_add, Category.assoc, cl_dots_dots]
  congr 2
  simp only [h_wt_up]
  push_cast
  generalize D.parity i = p
  generalize (a : ZMod 2) = a'
  generalize (s : ZMod 2) = s'
  generalize (r : ZMod 2) = r'
  generalize ((D.h i μ : ℤ) : ZMod 2) = h
  revert p a' s' r' h
  decide

include Sc in
private theorem same_slide_coefficient_add (i : I) (t : ℕ) (b : ZMod 2) :
    (∑ a ∈ range (t + 1), zsign k (D.parity i * (t : ZMod 2) * (b + a))) =
      if D.parity i * (t : ZMod 2) = 0 then (t + 1 : k) else 0 := by
  have he (a : ℕ) (ha : a ∈ range (t + 1)) :
      zsign k (D.parity i * (t : ZMod 2) * (b + a)) =
        zsign k (D.parity i * (t : ZMod 2) * (b + ((t + 1 : ℕ) : ZMod 2))) *
          zsign k (D.parity i * (t : ZMod 2) * ((t + 1 - a : ℕ) : ZMod 2)) := by
    rw [← zsign_add, Nat.cast_sub (by have := mem_range.mp ha; omega)]
    congr 1
    generalize D.parity i = p
    generalize (t : ZMod 2) = q
    generalize ((t + 1 : ℕ) : ZMod 2) = x
    generalize (a : ZMod 2) = y
    revert p q x y b
    decide
  rw [sum_congr rfl he, ← mul_sum, same_slide_coefficient (Sc := Sc) i (t + 1) t (by omega)]
  split_ifs with hp
  · simp only [hp, zero_mul, zsign_zero, one_mul]
  · exact mul_zero _

private theorem bubbleR_same_shift_nonpos (i : I) (μ : X) (hh : D.h i μ ≤ -1) (N : ℕ) :
    rbub i μ (bubRs cs i (wt D μ []) N) =
      ∑ t ∈ range (N + 1), (if D.parity i * (t : ZMod 2) = 0 then (t + 1 : k) else 0) •
        (lbub i μ (bubRs cs i (wt D μ [up i]) ((N : ℤ) - t)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] t)) := by
  let n := ((N : ℤ) - D.h i μ - 1).toNat
  have hn : (n : ℤ) = N - D.h i μ - 1 := Int.toNat_of_nonneg (by omega)
  have hNn : N ≤ n := by omega
  let B := fun (t : ℕ) => lbub i μ (bubRs cs i (wt D μ [up i]) ((N : ℤ) - t)) ≫
    cl D Sc μ [up i] [up i] (dotsL [] i [] t)
  let F := fun (s r : ℕ) => zsign k
    (D.parity i * ((s + r : ℕ) : ZMod 2) * ((D.h i μ : ZMod 2) + s)) • B (s + r)
  let G := fun s => ∑ r ∈ range (N + 1 - s), F s r
  have hterm (s : ℕ) (hs : s < n) :
      zsign k (D.parity i * (n - 1 - s : ℕ) * (D.parity i * s) + D.parity i * s) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] s) ≫ curl18 cs i μ (n - 1 - s)) = G s := by
    have hb : (((n - 1 - s : ℕ) : ℤ) + D.h i μ + 3).toNat = N + 1 - s := by omega
    rw [curl18, leps, eq_5_18, hb, Preadditive.comp_sum, smul_sum]
    dsimp only [G]
    apply sum_congr rfl
    intro r _
    rw [same_slide_R_term]
    dsimp only [F, B]
    congr 2
    congr 1
    simp only [bubRs, h_wt_up]
    congr 1
    push_cast
    omega
  have hGn : G n = dsc cs i μ • cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
    by_cases he : D.h i μ = -1
    · have hnN : n = N := by omega
      simp only [G, hnN, Nat.add_sub_cancel_left, sum_range_one, F, B, Nat.add_zero]
      have hz : D.parity i * (N : ZMod 2) * ((D.h i μ : ZMod 2) + N) = 0 := by
        rw [he]
        push_cast
        generalize D.parity i = p
        generalize (N : ZMod 2) = q
        revert p q
        decide
      rw [hz, zsign_zero, one_smul, sub_self, bubRs_zero, lbub, map_smul,
        plcL_id, Linear.smul_comp]
      erw [Category.id_comp]
      rw [dsc, ite_eq_left he, c_wt_up]
    · have hz : N + 1 - n = 0 := by omega
      simp [G, hz, dsc, he]
  have hstart : rbub i μ (bubRs cs i (wt D μ []) N) = bubbleR_right cs i i μ n := by
    simp only [bubRs, bubbleR_right]
    rw [hn]
    rfl
  rw [hstart, bubbleR_same_curls_nonpos cs i μ hh,
    sum_congr rfl (fun s hs => hterm s (mem_range.mp hs)), ← hGn, ← sum_range_succ]
  have hbound : (∑ s ∈ range (n + 1), G s) = ∑ s ∈ range (N + 1), G s := by
    apply sum_range_eq_of_zero _ (by omega)
    intro s hs _
    simp [G, show N + 1 - s = 0 by omega]
  rw [hbound]
  change (∑ s ∈ range (N + 1), ∑ r ∈ range (N + 1 - s), F s r) = _
  rw [← sum_range_diag_flip]
  apply sum_congr rfl
  intro t ht
  have hinner : (∑ s ∈ range (t + 1), F s (t - s)) =
      (∑ s ∈ range (t + 1), zsign k (D.parity i * (t : ZMod 2) * ((D.h i μ : ZMod 2) + s))) • B t := by
    rw [sum_smul]
    apply sum_congr rfl
    intro s hs
    dsimp only [F]
    rw [Nat.add_sub_of_le (by have := mem_range.mp hs; omega : s ≤ t)]
  rw [hinner, same_slide_coefficient_add (Sc := Sc)]

private def sameColourCoefficient (i : I) (r : ℕ) : k :=
  if D.parity i * (r : ZMod 2) = 0 then (r + 1 : k) else 0

private def sameColourSeries (i : I) (μ : X) (r : ℕ) :=
  sameColourCoefficient (D := D) (k := k) i r • cl D Sc μ [up i] [up i] (dotsL [] i [] r)

private def sameColourRHSR (i : I) (μ : X) (n : ℕ) :=
  ∑ r ∈ range (n + 1), sameColourCoefficient (D := D) (k := k) i r •
    (lbub i μ (bubRs cs i (wt D μ [up i]) ((n : ℤ) - r)) ≫
      cl D Sc μ [up i] [up i] (dotsL [] i [] r))

private def sameColourRHSL (i : I) (μ : X) (n : ℕ) :=
  ∑ r ∈ range (n + 1), sameColourCoefficient (D := D) (k := k) i r •
    (rbub i μ (bubLs cs i (wt D μ []) ((n : ℤ) - r)) ≫
      cl D Sc μ [up i] [up i] (dotsL [] i [] r))

private theorem sameColourR_normalize (i : I) (μ : X) (n : ℕ) :
    bubbleConvolution (fun m => lbub i μ (bubbleCoeffR cs i (wt D μ [up i]) m))
      (sameColourSeries (Sc := Sc) i μ) n = (cs.c μ i : k) • sameColourRHSR cs i μ n := by
  simp only [bubbleConvolution, sameColourSeries, bubbleCoeffR, lbub, map_smul,
    Linear.smul_comp, Linear.comp_smul, smul_smul, sameColourRHSR, smul_sum, c_wt_up]
  apply sum_congr rfl
  intro r hr
  have hrn : r ≤ n := by have := mem_range.mp hr; omega
  rw [Nat.cast_sub hrn]
  congr 1
  ring

private theorem sameColourL_normalize (i : I) (μ : X) (n : ℕ) :
    bubbleConvolution (sameColourSeries (Sc := Sc) i μ)
      (fun m => rbub i μ (bubbleCoeffL cs i (wt D μ []) m)) n =
      (isg k (D.parity i) n * (↑(cs.c μ i)⁻¹ : k)) • sameColourRHSL cs i μ n := by
  rw [bubbleConvolution, ← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  rw [sameColourRHSL, smul_sum]
  apply sum_congr rfl
  intro r hr
  have hrn : r ≤ n := by have := mem_range.mp hr; omega
  rw [show n - (n - r) = r by omega]
  simp only [sameColourSeries, bubbleCoeffL, rbub, map_smul, Linear.smul_comp,
    Linear.comp_smul, smul_smul, Nat.cast_sub hrn]
  by_cases hp : D.parity i * (r : ZMod 2) = 0
  · have hc := bub_dots_commR i μ (bubL_mem cs i (wt D μ [])
      (((n : ℤ) - r) + D.h i (wt D μ []) - 1)) r
    have hp' : (r : ZMod 2) * D.parity i = 0 := by rwa [mul_comm]
    rw [hp', mul_zero, zsign_zero, one_smul] at hc
    change rbub i μ (bubLs cs i (wt D μ []) ((n : ℤ) - r)) ≫ _ =
      _ ≫ rbub i μ (bubLs cs i (wt D μ []) ((n : ℤ) - r)) at hc
    dsimp only [rbub] at hc
    rw [← hc]
    have he : isg k (D.parity i) ((n : ℤ) - r) = isg k (D.parity i) n := by
      simp only [isg, Int.cast_sub, Int.cast_natCast, mul_sub, hp, sub_zero]
    rw [he]
    rfl
  · simp [sameColourCoefficient, hp]

private theorem sameColour_slide_all (i : I) (μ : X) :
    (∀ n : ℕ, rbub i μ (bubRs cs i (wt D μ []) n) = sameColourRHSR cs i μ n) ∧
    (∀ n : ℕ, lbub i μ (bubLs cs i (wt D μ [up i]) n) = sameColourRHSL cs i μ n) := by
  let Rr := fun n => rbub i μ (bubbleCoeffR cs i (wt D μ []) n)
  let Rl := fun n => lbub i μ (bubbleCoeffR cs i (wt D μ [up i]) n)
  let Lr := fun n => rbub i μ (bubbleCoeffL cs i (wt D μ []) n)
  let Ll := fun n => lbub i μ (bubbleCoeffL cs i (wt D μ [up i]) n)
  let Q := sameColourSeries (Sc := Sc) i μ
  have hzQ : Q 0 = 𝟙 _ := by
    simp only [Q, sameColourSeries, sameColourCoefficient, Nat.cast_zero, mul_zero,
      ite_true, zero_add, one_smul, dotsL, List.replicate_zero, cl_nil]
  have H := bubbleConvolution_inverse Rr Rl Lr Ll Q
    (by simp only [Rr, bubbleCoeffR_zero, rbub, plcL_id]; rfl)
    (by simp only [Rl, bubbleCoeffR_zero, lbub, plcL_id]; rfl)
    (by simp only [Lr, bubbleCoeffL_zero, rbub, plcL_id]; rfl)
    (by simp only [Ll, bubbleCoeffL_zero, lbub, plcL_id]; rfl) hzQ
    (bubbleCoeff_key_place cs i μ [up i] []) (bubbleCoeff_key_place cs i μ [] [up i])
  have hR : Rr = bubbleConvolution Rl Q ↔
      ∀ n : ℕ, rbub i μ (bubRs cs i (wt D μ []) n) = sameColourRHSR cs i μ n := by
    rw [funext_iff]
    apply forall_congr'
    intro n
    change rbub i μ (bubbleCoeffR cs i (wt D μ []) n) = _ ↔ _
    rw [sameColourR_normalize]
    simp only [bubbleCoeffR, rbub]
    rw [map_smul]
    exact (cs.c μ i).isUnit.smul_left_cancel
  have hL : Ll = bubbleConvolution Q Lr ↔
      ∀ n : ℕ, lbub i μ (bubLs cs i (wt D μ [up i]) n) = sameColourRHSL cs i μ n := by
    rw [funext_iff]
    apply forall_congr'
    intro n
    change lbub i μ (bubbleCoeffL cs i (wt D μ [up i]) n) = _ ↔ _
    rw [sameColourL_normalize]
    simp only [bubbleCoeffL, lbub, map_smul, c_wt_up]
    exact ((zsign_isUnit _).mul (cs.c μ i)⁻¹.isUnit).smul_left_cancel
  rw [hR, hL] at H
  rcases lt_or_ge (D.h i μ) 0 with hh | hh
  · have hr : ∀ n : ℕ, rbub i μ (bubRs cs i (wt D μ []) n) = sameColourRHSR cs i μ n :=
      fun n => bubbleR_same_shift_nonpos cs i μ (by omega) n
    exact ⟨hr, H.mp hr⟩
  · have hl : ∀ n : ℕ, lbub i μ (bubLs cs i (wt D μ [up i]) n) = sameColourRHSL cs i μ n :=
      fun n => bubbleL_same_shift_nonneg cs i μ hh n
    exact ⟨H.mpr hl, hl⟩

private theorem sameColour_odd_sum {M : Type*} [AddCommGroup M] [Module k M]
    (i : I) (hi : D.parity i = 1) (n : ℕ) (B : ℕ → M) :
    (∑ r ∈ range (n + 1), sameColourCoefficient (D := D) (k := k) i r • B r) =
      ∑ r ∈ range (n / 2 + 1), (2 * r + 1 : k) • B (2 * r) := by
  simp only [sameColourCoefficient, hi, one_mul, ite_smul, zero_smul]
  rw [← sum_filter]
  refine sum_nbij' (fun r => r / 2) (fun r => 2 * r) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_range] at hr ⊢
    omega
  · intro r hr
    simp only [mem_filter, mem_range] at hr ⊢
    constructor
    · omega
    · simp only [Nat.cast_mul, Nat.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  · intro r hr
    have hd := Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff r 2).mp (mem_filter.mp hr).2)
    omega
  · intro r _
    omega
  · intro r hr
    have hd := Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff r 2).mp (mem_filter.mp hr).2)
    have he : 2 * (r / 2) = r := by omega
    rw [he]
    congr 1
    have he' := congrArg (fun m : ℕ => (m : k)) he
    push_cast at he'
    rw [he']

/-- BE2 Proposition 7.3(i), (7.7), including all fake bubbles. -/
theorem eq_7_7 (i : I) (μ : X) (hi : D.parity i = 0) (n : ℕ) :
    rbub i μ (bubRs cs i (wt D μ []) n) =
      ∑ r ∈ range (n + 1), (r + 1 : k) •
        (lbub i μ (bubRs cs i (wt D μ [up i]) ((n : ℤ) - r)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] r)) := by
  simpa only [sameColourRHSR, sameColourCoefficient, hi, zero_mul, ite_true] using
    (sameColour_slide_all cs i μ).1 n

/-- BE2 Proposition 7.3(i), (7.8), including all fake bubbles. -/
theorem eq_7_8 (i : I) (μ : X) (hi : D.parity i = 0) (n : ℕ) :
    lbub i μ (bubLs cs i (wt D μ [up i]) n) =
      ∑ r ∈ range (n + 1), (r + 1 : k) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫
          rbub i μ (bubLs cs i (wt D μ []) ((n : ℤ) - r))) := by
  rw [(sameColour_slide_all cs i μ).2, sameColourRHSL]
  apply sum_congr rfl
  intro r _
  simp only [sameColourCoefficient, hi, zero_mul, ite_true]
  congr 1
  exact bubbleL_right_dots_even cs i i μ _ r (by rw [hi, mul_zero])

/-- BE2 Proposition 7.3(ii), (7.9), with coefficient `2r+1`. -/
theorem eq_7_9 (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ) :
    rbub i μ (bubRs cs i (wt D μ []) n) =
      ∑ r ∈ range (n / 2 + 1), (2 * r + 1 : k) •
        (lbub i μ (bubRs cs i (wt D μ [up i]) ((n : ℤ) - 2 * r)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] (2 * r))) := by
  rw [(sameColour_slide_all cs i μ).1, sameColourRHSR, sameColour_odd_sum i hi]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- BE2 Proposition 7.3(ii), (7.10), with coefficient `2r+1`. -/
theorem eq_7_10 (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ) :
    lbub i μ (bubLs cs i (wt D μ [up i]) n) =
      ∑ r ∈ range (n / 2 + 1), (2 * r + 1 : k) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] (2 * r)) ≫
          rbub i μ (bubLs cs i (wt D μ []) ((n : ℤ) - 2 * r))) := by
  rw [(sameColour_slide_all cs i μ).2, sameColourRHSL, sameColour_odd_sum i hi]
  apply sum_congr rfl
  intro r _
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  exact bubbleL_right_dots_even cs i i μ _ (2 * r) (by
    rw [Nat.cast_mul, Nat.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_mul])

end OddMath.SKM
