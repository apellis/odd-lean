/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.WeightedSeparation
import OddMath.QuiverHecke.Basis
import Mathlib.Data.Finset.Prod

/-!
# Bounded cyclotomic separation

Supporting the affine-algebra separation step toward Brundan–Ellis §8,
Nondegeneracy Conjecture (research issue #345). These arguments use affine
PBW independence, not independence of its image in SKM.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA

theorem permutation_length_le_choose_two (n : ℕ) (w : Equiv.Perm (Fin n)) :
    length n w ≤ n.choose 2 := by
  classical
  rw [length_eq_invCount]
  unfold invCount invSet
  calc
    _ ≤ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card :=
      Finset.card_le_card (by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩)
    _ = n.choose 2 := by
      simpa using (Finset.card_product_filter_lt (s := Finset.univ (α := Fin n)))

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- PBW words with dot count at most `d`. -/
def DotAtMost (t t' : List I) (d : ℕ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k ((fun i : NFIdx t t' => i.nf (D := D) (Sc := Sc)) ''
    {i | i.1.1.length ≤ d})

/-- PBW words with dot count at least `d`. -/
def DotAtLeast (t t' : List I) (d : ℕ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k ((fun i : NFIdx t t' => i.nf (D := D) (Sc := Sc)) ''
    {i | d ≤ i.1.1.length})

theorem disjoint_dotAtMost_dotAtLeast (t t' : List I) {d N : ℕ} (h : d < N) :
    Disjoint (DotAtMost D Sc t t' d) (DotAtLeast D Sc t t' N) := by
  apply (linearIndependent_nf D Sc t t').disjoint_span_image
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [Set.mem_ofPred_eq] at hi hj
  omega

theorem weightedNF_le_dotAtLeast (t t' : List I) (m : ℕ) {s : ℤ} {d : ℕ}
    (hd : (d : ℤ) ≤ s) : WeightedNF D Sc t t' m s ≤ DotAtLeast D Sc t t' d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, hf, w, hw, hs, h, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨(l, w), hl, hf, h⟩, by simp only [Set.mem_ofPred_eq]; omega, rfl⟩

/-- The power of the dot on the first strand; the separation theorem assumes
the strand word is nonempty, so this is never an out-of-range dot. -/
def firstDotPower (t : List I) (N : ℕ) :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc t t ((List.replicate N 0).map PG.dot)
    (by simpa only [tgt_map_dot] using sChain_pl t ((List.replicate N 0).map PG.dot))

/-- A cyclotomic generator between two affine normal forms has no low-dot
PBW coordinates. The two permutation lengths account for the loss `2L`. -/
theorem nf_firstDotPower_nf_mem {t u t' : List I} (a : NFIdx t u) (b : NFIdx u t')
    {N : ℕ} (ht : 0 < t.length) (hN : 2 * t.length.choose 2 ≤ N) :
    a.nf (D := D) (Sc := Sc) ≫ firstDotPower D Sc u N ≫ b.nf ∈
      DotAtLeast D Sc t t' (N - 2 * t.length.choose 2) := by
  have hu : u.length = t.length := length_of_sChain a.2.2.2
  have hm : ∀ p ∈ List.replicate N 0, p < t.length := by
    intro p hp
    have : p = 0 := (List.mem_replicate.mp hp).2
    omega
  have ha := permutation_length_le_choose_two t.length a.1.2
  have hb := permutation_length_le_choose_two u.length b.1.2
  have hchoose : u.length.choose 2 = t.length.choose 2 := congrArg (fun n => n.choose 2) hu
  rw [hchoose] at hb
  unfold NFIdx.nf firstDotPower
  rw [cl_comp, cl_comp]
  apply weightedNF_le_dotAtLeast D Sc t t' _ _ (word_mem_weightedNF D Sc _ _)
  simp only [positionedScore_append]
  rw [positionedScore_dots a.2.2.1,
    positionedScore_cw (validWord_canWord t.length a.1.2),
    positionedScore_dots hm, List.length_replicate]
  have hfb : ∀ p ∈ b.1.1, p < t.length := by simpa only [hu] using b.2.2.1
  rw [positionedScore_dots hfb]
  have hvc : ValidWord t.length (canWord u.length b.1.2) := by
    intro x hx
    have := validWord_canWord u.length b.1.2 x hx
    omega
  rw [positionedScore_cw hvc, length_canWord, length_canWord]
  omega

theorem dotAtLeast_antitone (t t' : List I) {d e : ℕ} (h : d ≤ e) :
    DotAtLeast D Sc t t' e ≤ DotAtLeast D Sc t t' d :=
  Submodule.span_mono (Set.image_mono fun _ hi => h.trans hi)

/-- Arbitrary left and right multipliers may first be expanded in the independent
affine PBW bases, so their unreduced crossing counts cause no loss of control. -/
theorem firstDotPower_sandwich_mem {t u t' : List I}
    (a : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D u))
    (b : (pres D Sc).obj (ob D u) ⟶ (pres D Sc).obj (ob D t'))
    {N : ℕ} (ht : 0 < t.length) (hN : 2 * t.length.choose 2 ≤ N) :
    a ≫ firstDotPower D Sc u N ≫ b ∈ DotAtLeast D Sc t t' (N - 2 * t.length.choose 2) := by
  have ha : a ∈ Submodule.span k (Set.range fun i : NFIdx t u => i.nf (D := D) (Sc := Sc)) := by
    rw [span_nf]; trivial
  have hb : b ∈ Submodule.span k (Set.range fun i : NFIdx u t' => i.nf (D := D) (Sc := Sc)) := by
    rw [span_nf]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨j, rfl⟩ := hb
      exact nf_firstDotPower_nf_mem D Sc i j ht hN
    | zero => simp
    | add b c _ _ hb hc =>
      simp only [Preadditive.comp_add]
      exact Submodule.add_mem _ hb hc
    | smul c b _ hb =>
      simp only [Linear.comp_smul]
      exact Submodule.smul_mem _ c hb
  | zero => simp
  | add a c _ _ ha hc =>
    simp only [Preadditive.add_comp]
    exact Submodule.add_mem _ ha hc
  | smul c a _ ha =>
    simp only [Linear.smul_comp]
    exact Submodule.smul_mem _ c ha

/-- The two-sided span of cyclotomic dot powers with exponent at least `N`.
Every intermediate strand word and every affine left/right multiplier is included. -/
def CyclotomicSpan (t t' : List I) (N : ℕ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ u : List I, 0 < u.length ∧ ∃ M : ℕ, N ≤ M ∧
    ∃ a : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D u),
    ∃ b : (pres D Sc).obj (ob D u) ⟶ (pres D Sc).obj (ob D t'),
      a ≫ firstDotPower D Sc u M ≫ b = f}

theorem cyclotomicSpan_comp {t u t' : List I} {N : ℕ}
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D u)}
    (hf : f ∈ CyclotomicSpan D Sc t u N)
    (g : (pres D Sc).obj (ob D u) ⟶ (pres D Sc).obj (ob D t')) :
    f ≫ g ∈ CyclotomicSpan D Sc t t' N := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, hv, M, hM, a, b, rfl⟩ := hf
    apply Submodule.subset_span
    exact ⟨v, hv, M, hM, a, b ≫ g, by simp only [Category.assoc]⟩
  | zero => simp
  | add f h _ _ hf hh =>
    rw [Preadditive.add_comp]
    exact Submodule.add_mem _ hf hh
  | smul c f _ hf =>
    rw [Linear.smul_comp]
    exact Submodule.smul_mem _ c hf

theorem comp_cyclotomicSpan {t u t' : List I} {N : ℕ}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D u))
    {g : (pres D Sc).obj (ob D u) ⟶ (pres D Sc).obj (ob D t')}
    (hg : g ∈ CyclotomicSpan D Sc u t' N) :
    f ≫ g ∈ CyclotomicSpan D Sc t t' N := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨v, hv, M, hM, a, b, rfl⟩ := hg
    apply Submodule.subset_span
    exact ⟨v, hv, M, hM, f ≫ a, b, by simp only [Category.assoc]⟩
  | zero => simp
  | add g h _ _ hg hh =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ hg hh
  | smul c g _ hg =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c hg

/-- The cyclotomic relation ideal has no bounded low-dot PBW coordinates. -/
theorem cyclotomicSpan_le_dotAtLeast {t t' : List I} {N : ℕ}
    (ht : 0 < t.length) (hN : 2 * t.length.choose 2 ≤ N) :
    CyclotomicSpan D Sc t t' N ≤ DotAtLeast D Sc t t' (N - 2 * t.length.choose 2) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u, _, M, hM, a, b, rfl⟩
  exact dotAtLeast_antitone D Sc t t' (Nat.sub_le_sub_right hM _)
    (firstDotPower_sandwich_mem D Sc a b ht (hN.trans hM))

/-- Affine monomial cyclotomic quotients detect every PBW combination of at most
`d` dots once `N > d + 2 * choose(n,2)`. This theorem assumes no SKM action. -/
theorem cyclotomic_quotient_injective_on_dotAtMost {t t' : List I} {d N : ℕ}
    (ht : 0 < t.length) (hN : d + 2 * t.length.choose 2 < N) :
    Function.Injective (fun x : DotAtMost D Sc t t' d =>
      (CyclotomicSpan D Sc t t' N).mkQ (x : (pres D Sc).obj (ob D t) ⟶
        (pres D Sc).obj (ob D t'))) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hmem : (x : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) - y ∈
      CyclotomicSpan D Sc t t' N := (Submodule.Quotient.eq _).mp hxy
  exact Submodule.disjoint_def.mp
    (disjoint_dotAtMost_dotAtLeast D Sc t t' (by omega)) _
    (Submodule.sub_mem _ x.property y.property)
    (cyclotomicSpan_le_dotAtLeast D Sc ht (by omega) hmem)

end OddMath.QuiverHecke
