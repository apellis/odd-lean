/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.RelationsNF
import OddMath.SKM.Grading
import OddMath.SKM.Placement
import OddMath.SKM.K0Relations
import OddMath.SKM.SummandRetracts
import OddMath.SKM.LaurentianK0

/-!
# The identity of a word factors through sorted words

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity: an indecomposable
summand of `Q^m Π^a E_𝐚 1_λ` of width `N` is a summand of some `Q^{m'} Π^{a'} E_𝐢 F_𝐢′ 1_λ` with
`|𝐢| + |𝐢′| = N`, by the inversion relations (1.12)–(1.14) (cf. Khovanov–Lauda,
arXiv:0807.3250v1, proof of Lemma 3.38). This file proves the diagrammatic input: in the
presented 2-category, the identity of every word `w` is a linear combination of composites
`w → u → w` of normal-form diagrams of opposite degrees and equal parities, through **sorted**
words `u` (all upward letters to the left of all downward letters) with `|u| ≤ |w|` and
`|u| ≡ |w| mod 2` (`thru_sorted`).

## Main declarations

* `Thru μ w P`: the identity of `E_w 1_μ` is a combination of such composites through words `u`
  with `P u`; `Thru.trans`, `Thru.mono`, `Thru.whisker`.
* `thru_dn_up`: the inversion relations, for a downward letter followed by an upward one.
* `invR`: the number of downward letters followed later by an upward one; `Sorted`.
* `thru_sorted`: the identity of every word factors through sorted words.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D)

/-! ### Inversions -/

/-- The number of pairs (downward letter, later upward letter) of a word. -/
def invR : List (Letter I) → ℕ
  | [] => 0
  | l :: w => (if l.1 then 0 else w.countP (fun m => m.1)) + invR w

/-- A word is **sorted** if all its upward letters are to the left of all its downward letters. -/
def Sorted (w : List (Letter I)) : Prop := ∃ a b : List I, w = a.map up ++ b.map dn

theorem countP_sorted (a b : List I) :
    (a.map up ++ b.map dn).countP (fun m : Letter I => m.1) = a.length := by
  simp [List.countP_append, List.countP_map, Function.comp_def]

theorem sorted_of_invR_eq_zero : ∀ w : List (Letter I), invR w = 0 → Sorted w
  | [] => fun _ => ⟨[], [], rfl⟩
  | (ε, i) :: w => fun h => by
    simp only [invR] at h
    obtain ⟨a, b, rfl⟩ := sorted_of_invR_eq_zero w (by omega)
    cases ε
    · have h1 : (a.map up ++ b.map dn).countP (fun m : Letter I => m.1) = 0 := by
        simp only [Bool.false_eq_true, ↓reduceIte] at h; omega
      rw [countP_sorted] at h1
      obtain rfl := List.eq_nil_of_length_eq_zero h1
      exact ⟨[], i :: b, rfl⟩
    · exact ⟨i :: a, b, rfl⟩

theorem exists_dn_up_of_invR_ne_zero : ∀ w : List (Letter I), invR w ≠ 0 →
    ∃ (u v : List (Letter I)) (j i : I), w = u ++ dn j :: up i :: v
  | [] => fun h => (h rfl).elim
  | l :: w => fun h => by
    by_cases hw : invR w = 0
    · obtain ⟨a, b, rfl⟩ := sorted_of_invR_eq_zero w hw
      obtain ⟨ε, j⟩ := l
      simp only [invR, hw, add_zero] at h
      cases ε
      · simp only [Bool.false_eq_true, ↓reduceIte, countP_sorted] at h
        obtain ⟨i, a, rfl⟩ : ∃ i a', a = i :: a' := by
          cases a with
          | nil => simp at h
          | cons i a' => exact ⟨i, a', rfl⟩
        exact ⟨[], a.map up ++ b.map dn, j, i, rfl⟩
      · simp at h
    · obtain ⟨u, v, j, i, rfl⟩ := exists_dn_up_of_invR_ne_zero w hw
      exact ⟨l :: u, v, j, i, rfl⟩

theorem invR_swap (i j : I) (v : List (Letter I)) :
    ∀ u : List (Letter I), invR (u ++ up i :: dn j :: v) < invR (u ++ dn j :: up i :: v)
  | [] => by simp [invR]
  | l :: u => by
    have := invR_swap i j v u
    have e : (u ++ up i :: dn j :: v).countP (fun m : Letter I => m.1) =
        (u ++ dn j :: up i :: v).countP (fun m : Letter I => m.1) := by
      simp [List.countP_append]
    simp only [List.cons_append, invR, e]
    omega

theorem invR_del (i j : I) (v : List (Letter I)) :
    ∀ u : List (Letter I), invR (u ++ v) < invR (u ++ dn j :: up i :: v)
  | [] => by simp [invR]
  | l :: u => by
    have := invR_del i j v u
    have e : (u ++ v).countP (fun m : Letter I => m.1) ≤
        (u ++ dn j :: up i :: v).countP (fun m : Letter I => m.1) := by
      simp [List.countP_append]
    simp only [List.cons_append, invR]
    split_ifs <;> omega

/-! ### Factorizations of the identity -/

/-- The parity of a layer list. -/
abbrev parL (L : List (LayerData I)) : ZMod 2 := (L.map fun x => x.2.1.parity D).sum

variable {Sc} in
/-- Composites `w → u → w` of normal-form diagrams of opposite degrees and equal parities through
words `u` with `P u`. -/
def thruSet (μ : X) (w : List (Letter I)) (P : List (Letter I) → Prop) :
    Set ((pres D Sc).obj (ob D μ w) ⟶ (pres D Sc).obj (ob D μ w)) :=
  {f | ∃ (u : List (Letter I)) (A B : List (LayerData I)), P u ∧ SChain w A u ∧ SChain u B w ∧
    gsum D sy μ A + gsum D sy μ B = 0 ∧ parL (D := D) A = parL (D := D) B ∧
    f = cl D Sc μ w u A ≫ cl D Sc μ u w B}

/-- The identity of `E_w 1_μ` is a linear combination of composites through words with `P`. -/
def Thru (μ : X) (w : List (Letter I)) (P : List (Letter I) → Prop) : Prop :=
  𝟙 _ ∈ Submodule.span k (thruSet (Sc := Sc) sy μ w P)

variable {Sc sy}

theorem thru_self {μ : X} {w : List (Letter I)} {P : List (Letter I) → Prop} (h : P w) :
    Thru Sc sy μ w P :=
  Submodule.subset_span ⟨w, [], [], h, rfl, rfl, by simp [gsum], rfl,
    by rw [cl_nil, Category.comp_id]⟩

theorem Thru.mono {μ : X} {w : List (Letter I)} {P Q : List (Letter I) → Prop}
    (h : Thru Sc sy μ w P) (hPQ : ∀ u, P u → Q u) : Thru Sc sy μ w Q := by
  refine Submodule.span_mono ?_ h
  rintro _ ⟨u, A, B, hu, hA, hB, hd, hp, rfl⟩
  exact ⟨u, A, B, hPQ u hu, hA, hB, hd, hp, rfl⟩

theorem parL_append (A B : List (LayerData I)) :
    parL (D := D) (A ++ B) = parL (D := D) A + parL (D := D) B := by
  simp [parL]

/-- Composing with diagrams of opposite degree and equal parity keeps factorizations. -/
theorem sandwich_mem {μ : X} {w u : List (Letter I)} {P : List (Letter I) → Prop}
    {A B : List (LayerData I)} (hA : SChain w A u) (hB : SChain u B w)
    (hd : gsum D sy μ A + gsum D sy μ B = 0) (hp : parL (D := D) A = parL (D := D) B)
    {f} (hf : f ∈ Submodule.span k (thruSet (Sc := Sc) sy μ u P)) :
    cl D Sc μ w u A ≫ f ≫ cl D Sc μ u w B ∈ Submodule.span k (thruSet (Sc := Sc) sy μ w P) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨t, A', B', ht, hA', hB', hd', hp', rfl⟩ := hg
    refine Submodule.subset_span ⟨t, A ++ A', B' ++ B, ht, hA.append hA', hB'.append hB,
      by rw [gsum_append, gsum_append]; omega,
      by rw [parL_append, parL_append, hp, hp']; ring, ?_⟩
    simp only [Category.assoc]
    rw [cl_comp hB' hB, ← Category.assoc, cl_comp hA hA']
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp, Preadditive.comp_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [Linear.smul_comp, Linear.comp_smul]
    exact Submodule.smul_mem _ r hx

theorem Thru.trans {μ : X} {w : List (Letter I)} {P Q : List (Letter I) → Prop}
    (h : Thru Sc sy μ w P) (hPQ : ∀ u, P u → Thru Sc sy μ u Q) : Thru Sc sy μ w Q := by
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨u, A, B, hu, hA, hB, hd, hp, rfl⟩
  have := sandwich_mem hA hB hd hp (hPQ u hu)
  rwa [Category.id_comp] at this

theorem gsum_map_whL (μ : X) (u v : List (Letter I)) (A : List (LayerData I)) :
    gsum D sy μ (A.map (whL u v)) = gsum D sy (wt D μ v) A := by
  simp only [gsum, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [whL, wt_append]

theorem parL_map_whL (u v : List (Letter I)) (A : List (LayerData I)) :
    parL (D := D) (A.map (whL u v)) = parL (D := D) A := by
  simp only [parL, List.map_map]
  rfl

/-- Factorizations can be whiskered by words on both sides. -/
theorem Thru.whisker {μ : X} {s : List (Letter I)} {P : List (Letter I) → Prop}
    (u v : List (Letter I)) (h : Thru Sc sy (wt D μ v) s P) :
    Thru Sc sy μ (u ++ s ++ v) (fun t => ∃ t', P t' ∧ t = u ++ t' ++ v) := by
  have h1 : plcL D Sc μ u v s s (𝟙 _) = 𝟙 _ := by
    rw [← cl_nil, plcL_cl, List.map_nil, cl_nil]
  unfold Thru
  rw [← h1]
  have : Submodule.map (plcL D Sc μ u v s s) (Submodule.span k (thruSet (Sc := Sc) sy _ s P)) ≤
      Submodule.span k (thruSet (Sc := Sc) sy μ (u ++ s ++ v)
        (fun t => ∃ t', P t' ∧ t = u ++ t' ++ v)) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨t, A, B, ht, hA, hB, hd, hp, rfl⟩
    refine Submodule.subset_span ⟨u ++ t ++ v, A.map (whL u v), B.map (whL u v),
      ⟨t, ht, rfl⟩, hA.whisk u v, hB.whisk u v,
      by rw [gsum_map_whL, gsum_map_whL]; exact hd,
      by rw [parL_map_whL, parL_map_whL]; exact hp, ?_⟩
    rw [plcL_cl_comp μ u v A B hA hB, plcL_cl, plcL_cl]
  exact this (Submodule.mem_map_of_mem h)

/-! ### The inversion relations -/

/-- **Inversion relations (1.12)–(1.14)**: the identity of `F_j E_i 1_ν` factors through
`E_i F_j 1_ν`, and, when `i = j`, through `1_ν`. -/
theorem thru_dn_up (ν : X) (j i : I) :
    Thru Sc sy ν [dn j, up i] (fun t => t = [up i, dn j] ∨ t = []) := by
  by_cases hij : j = i
  · subst hij
    rcases le_total 0 (D.h j ν) with hh | hh
    · have e := cl_invP₂ Sc j ν hh
      rw [cl_nil] at e
      have : 𝟙 ((pres D Sc).obj (ob D ν [dn j, up j])) =
          -(cl D Sc ν [dn j, up j] [up j, dn j] (lcrossL j j) ≫
            cl D Sc ν [up j, dn j] [dn j, up j] (sigmaL j j)) := by
        rw [cl_comp (sChain_lcrossL j j) (sChain_sigmaL j j), e, neg_neg]
      unfold Thru
      rw [this]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, _, _, Or.inl rfl,
        sChain_lcrossL j j, sChain_sigmaL j j, by simp, by simp, rfl⟩)
    · have e := cl_invM₁ Sc j ν hh
      rw [cl_nil] at e
      unfold Thru
      rw [← e]
      refine Submodule.add_mem _ (Submodule.neg_mem _ ?_) (Submodule.sum_mem _ fun n _ => ?_)
      · rw [← cl_comp (sChain_lcrossL j j) (sChain_sigmaL j j)]
        exact Submodule.subset_span ⟨_, _, _, Or.inl rfl,
          sChain_lcrossL j j, sChain_sigmaL j j, by simp, by simp, rfl⟩
      · rw [← cl_comp (sChain_dcapL j n) (sChain_etaL j n)]
        exact Submodule.subset_span ⟨_, _, _, Or.inr rfl,
          sChain_dcapL j n, sChain_etaL j n, by simp; ring, by simp [mul_comm], rfl⟩
  · have e := cl_invNe₂ Sc j i ν hij
    rw [cl_nil, ← cl_comp (sChain_lcrossL j i) (sChain_sigmaL j i)] at e
    unfold Thru
    rw [← e]
    exact Submodule.subset_span ⟨_, _, _, Or.inl rfl,
      sChain_lcrossL j i, sChain_sigmaL j i, by simp, by simp, rfl⟩

/-! ### Sorting -/

/-- **The identity of every word factors through sorted words** `u` with `|u| ≤ |w|` and
`|u| ≡ |w| mod 2`. -/
theorem thru_sorted (μ : X) (w : List (Letter I)) :
    Thru Sc sy μ w (fun u => Sorted u ∧ u.length ≤ w.length ∧ u.length % 2 = w.length % 2) := by
  induction h : invR w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h0 : invR w = 0
    · exact thru_self ⟨sorted_of_invR_eq_zero w h0, le_rfl, rfl⟩
    obtain ⟨u, v, j, i, rfl⟩ := exists_dn_up_of_invR_ne_zero w h0
    have hw : u ++ dn j :: up i :: v = u ++ [dn j, up i] ++ v := by simp
    rw [hw]
    refine ((thru_dn_up (Sc := Sc) (sy := sy) (wt D μ v) j i).whisker u v).trans ?_
    rintro _ ⟨t, ht | ht, rfl⟩
    · subst ht
      have hlt := invR_swap i j v u
      have e1 : u ++ [up i, dn j] ++ v = u ++ up i :: dn j :: v := by simp
      rw [e1]
      refine (ih _ (h ▸ hlt) _ rfl).mono ?_
      rintro t ⟨hs, hl, hp⟩
      refine ⟨hs, ?_, ?_⟩ <;> simp only [List.length_append, List.length_cons, List.length_nil] at hl hp ⊢ <;> omega
    · subst ht
      have hlt := invR_del i j v u
      have e1 : u ++ [] ++ v = u ++ v := by simp
      rw [e1]
      refine (ih _ (h ▸ hlt) _ rfl).mono ?_
      rintro t ⟨hs, hl, hp⟩
      refine ⟨hs, ?_, ?_⟩ <;> simp only [List.length_append, List.length_cons, List.length_nil] at hl hp ⊢ <;> omega

/-! ### Indecomposable summands of words -/

section Completed

open K0Relations StringDiagrams.KrullSchmidt

variable {k : Type w} [Field k] {Sc : Scalars D k} (cs : CScalars Sc) (hc : Sc.Homogeneous)
  (hf : sy.DegreeLocallyFinite)

theorem parity_add_self (a b : ZMod 2) : a + (a + b) = b := by
  rw [← add_assoc, ZModModule.add_self, zero_add]

include cs hf in
/-- **Sorting summands (BE2, proof of Theorem 11.7; KL III, Lemma 3.38)**: an indecomposable
retract of `Q^m Π^a E_w 1_ν` in `𝔘̇(𝔤)` is a retract of some `Q^n Π^b E_u 1_ν` with `u` sorted,
`|u| ≤ |w|` and `|u| ≡ |w| mod 2`. The hypothesis `sy.DegreeLocallyFinite` gives the
finite-dimensional Hom-spaces of Krull–Schmidt; see `UGr.degreeHomFinite`. -/
theorem exists_retract_sorted {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ}
    {a : ZMod 2} {Z : weight Sc sy hc μ ⟶ weight Sc sy hc ν} (hZ : IsIndec Z)
    (ι : Z ⟶ completed Sc sy hc μ ν w hw m a) (π : completed Sc sy hc μ ν w hw m a ⟶ Z)
    (h : ι ≫ π = 𝟙 Z) :
    ∃ (u : List (Letter I)) (hu : wt D ν u = μ) (n : ℤ) (b : ZMod 2),
      Sorted u ∧ u.length ≤ w.length ∧ u.length % 2 = w.length % 2 ∧
      ∃ (ι' : Z ⟶ completed Sc sy hc μ ν u hu n b)
        (π' : completed Sc sy hc μ ν u hu n b ⟶ Z), ι' ≫ π' = 𝟙 Z := by
  have : HomFinite k (weight Sc sy hc μ ⟶ weight Sc sy hc ν) := by
    let a : UGr D Sc sy hc := ⟨μ⟩
    let b : UGr D Sc sy hc := ⟨ν⟩
    have := UGr.degreeHomFinite sy cs hc hf a b
    exact inferInstanceAs (HomFinite k (GSKar k (a ⟶ b)))
  have ht := thru_sorted (Sc := Sc) (sy := sy) ν w
  obtain ⟨N, c, g, hg⟩ := Submodule.mem_span_set'.mp ht
  choose u A B hP hA hB hd hp hfg using fun j => (g j).2
  have hu : ∀ j, wt D ν (u j) = μ := fun j => ((hA j).wt_eq D ν).trans hw
  let n : Fin N → ℤ := fun j => m - gsum D sy ν (A j)
  let b : Fin N → ZMod 2 := fun j => a + parL (D := D) (A j)
  let U : ∀ j, shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν (u j) (hu j) (n j) (b j) :=
    fun j => c j • lift Sc sy hc (A j) (hA j) (by simp only [n]; ring)
      (by simp only [b]; rw [parity_add_self])
  let V : ∀ j, shifted Sc sy hc μ ν (u j) (hu j) (n j) (b j) ⟶ shifted Sc sy hc μ ν w hw m a :=
    fun j => lift Sc sy hc (B j) (hB j) (by simp only [n]; linarith [hd j])
      (by simp only [b]; rw [add_comm, ← add_assoc, ZModModule.add_self, zero_add, hp j])
  have htot : ∑ j, U j ≫ V j = 𝟙 _ := by
    let forget : (shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a) →+
        ((pres D Sc).obj (ob D ν w) ⟶ (pres D Sc).obj (ob D ν w)) :=
      { toFun := fun f => f.1.1
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hfi : Function.Injective forget := fun _ _ h => Subtype.ext (Subtype.ext h)
    apply hfi
    rw [map_sum]
    change ∑ j, (U j ≫ V j).1.1 = 𝟙 ((pres D Sc).obj (ob D ν w))
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfg j]
    simp only [U, V, Linear.smul_comp]
    rfl
  let F := inclusion Sc sy hc μ ν
  obtain ⟨j, -, π', hπ'⟩ := Summands.exists_retract_of_sum k hZ Finset.univ
    (fun j => ι ≫ F.map (U j)) (fun j => F.map (V j) ≫ π) (by
      calc ∑ j ∈ Finset.univ, (ι ≫ F.map (U j)) ≫ F.map (V j) ≫ π
          = ι ≫ F.map (∑ j, U j ≫ V j) ≫ π := by
            rw [F.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
            simp only [F.map_comp, Category.assoc]
        _ = 𝟙 Z := by rw [htot, F.map_id, Category.id_comp, h])
  exact ⟨u j, hu j, n j, b j, (hP j).1, (hP j).2.1, (hP j).2.2, _, π', hπ'⟩

end Completed

end OddMath.SKM
