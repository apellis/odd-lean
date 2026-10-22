/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Centre
import OddMath.QuiverHecke.HnBasis

/-!
# `H_n` is finite over its centre

BE2, arXiv:1701.04133v2, §11 uses, in the proof of Theorem 11.7, that the quiver Hecke
superalgebra `H_n` is finite as a module over its centre. The colour set `I` may be infinite in
BE2, and then `H_n` is a direct sum of infinitely many blocks, so the statement is made block by
block: for a finite set `W` of words closed under permutation of letters, every element of `H_n`
supported on `W × W` is a combination `∑_{g ∈ G} z_g g` of a fixed finite set `G` with central
coefficients `z_g` (`exists_centre_finite`). For a finite colour set this is all of `H_n`
(`exists_centre_finite_of_fintype`).

The central elements are `∑_{t ∈ W} 1_t ζ_t(q)`, where `ζ_t` sends the variable `(c, j)` to the
`j`-th elementary symmetric function of the squared dots of colour `c` on `t` (`Centre.lean`).
A dot `x_p` on a strand of colour `c` satisfies `x_p^{2s} = ∑_j ± e_{j+1} x_p^{2(s - j - 1)}`
with `s` the number of strands of colour `c` (Vieta), so every dot monomial reduces to one with
exponents below `2n`, times central elements.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

/-! ## Dot monomials -/

theorem sChain_dots (t : List I) (l : List ℕ) : SChain t (pl t (l.map PG.dot)) t := by
  have := sChain_pl t (l.map PG.dot)
  rwa [tgt_map_dot] at this

/-- The dots on the strands of `l`, bottom first. -/
def dcl (t : List I) (l : List ℕ) : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc t t (l.map PG.dot) (sChain_dots t l)

theorem dcl_append (t : List I) (l l' : List ℕ) :
    dcl D Sc t (l ++ l') = dcl D Sc t l ≫ dcl D Sc t l' := by
  rw [dcl, dcl, dcl, cl_comp]
  exact cl_congr D Sc _ _ (by simp)

theorem dcl_nil (t : List I) : dcl D Sc t [] = 𝟙 _ := cl_nil D Sc t _

theorem dcl_two (t : List I) (p : ℕ) : dcl D Sc t (List.replicate 2 p) = ySq D Sc t p := by
  unfold ySq xd
  rw [cl_comp]
  exact cl_congr D Sc _ _ rfl

theorem sqDots_X_pow (t : List I) (p s : ℕ) :
    (sqDots D Sc t (MvPolynomial.X p ^ s) : _ ⟶ _) = dcl D Sc t (List.replicate (2 * s) p) := by
  induction s with
  | zero => simp [dcl_nil, End.one_def]
  | succ s ih =>
    rw [pow_succ, map_mul, End.mul_def, sqDots_X, ih, ← dcl_two, ← dcl_append,
      ← List.replicate_add]
    congr 2; ring

/-- The dot monomial with exponent `m p` on strand `p < n`, strands in increasing order. -/
def dotList (n : ℕ) (m : ℕ → ℕ) : List ℕ := (List.range n).flatMap fun p => List.replicate (m p) p

theorem dotList_split {n p : ℕ} (hp : p < n) (m : ℕ → ℕ) :
    dotList n m = (List.range' 0 p).flatMap (fun q => List.replicate (m q) q) ++
      List.replicate (m p) p ++
        (List.range' (p + 1) (n - (p + 1))).flatMap fun q => List.replicate (m q) q := by
  rw [dotList, List.range_eq_range', show n = p + (1 + (n - (p + 1))) by omega,
    ← List.range'_append, ← List.range'_append]
  simp only [List.flatMap_append, List.range'_one, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, Nat.one_mul, Nat.zero_add]
  rw [show p + (1 + (n - (p + 1))) - (p + 1) = n - (p + 1) by omega]

theorem flatMap_update {l : List ℕ} {p : ℕ} (hp : p ∉ l) (m : ℕ → ℕ) (e : ℕ) :
    l.flatMap (fun q => List.replicate (Function.update m p e q) q) =
      l.flatMap fun q => List.replicate (m q) q := by
  refine List.flatMap_congr fun q hq => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hp hq)]

/-- The span of the bounded dot monomials times the central family. -/
def Red (t : List I) : Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t)) :=
  Submodule.span k {f | ∃ m : ℕ → ℕ, (∀ p, m p ≤ 2 * t.length) ∧
    ∃ q, f = dcl D Sc t (dotList t.length m) ≫ zeta D Sc t q}

theorem zeta_X (t : List I) (c : I) (j : ℕ) :
    zeta D Sc t (MvPolynomial.X (c, j)) = sqDots D Sc t (esymmS (colPos t c) j) := by
  simp [zeta, symmMap]

/-- Vieta for the squared dots: `x_p^{2s} = ∑_j (-1)^j x_p^{2(s-j-1)} e_{j+1}` with `e_{j+1}`
central, for `s` the number of strands of the colour of `p`. -/
theorem dcl_replicate_card {t : List I} {p : ℕ} (hp : p < t.length) :
    dcl D Sc t (List.replicate (2 * (colPos t t[p]).card) p) =
      ∑ j ∈ Finset.range (colPos t t[p]).card, ((-1 : k) ^ j) •
        (dcl D Sc t (List.replicate (2 * ((colPos t t[p]).card - (j + 1))) p) ≫
          zeta D Sc t (MvPolynomial.X (t[p], j + 1))) := by
  have hpS : p ∈ colPos t t[p] := mem_colPos.mpr (List.getElem?_eq_getElem hp)
  rw [← sqDots_X_pow, X_pow_card hpS, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zeta_X, ← sqDots_X_pow, map_mul, map_mul, map_pow, map_neg, map_one,
    show ((-1 : End ((pres D Sc).obj (ob D t))) ^ j) = algebraMap k _ ((-1) ^ j) by simp,
    ← Algebra.smul_def, End.mul_def]

theorem comp_zeta_mem_red {t : List I} {f} (hf : f ∈ Red D Sc t) (q : MvPolynomial (I × ℕ) k) :
    f ≫ (zeta D Sc t q : _ ⟶ _) ∈ Red D Sc t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, hm, q', rfl⟩ := hf
    refine Submodule.subset_span ⟨m, hm, q * q', ?_⟩
    rw [Category.assoc, map_mul, End.mul_def]
  | zero => simp
  | add f g _ _ hf hg => rw [Preadditive.add_comp]; exact add_mem hf hg
  | smul c f _ hf => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hf

/-- **Reduction of dot monomials.** -/
theorem dcl_dotList_mem (t : List I) (m : ℕ → ℕ) :
    dcl D Sc t (dotList t.length m) ∈ Red D Sc t := by
  set n := t.length
  induction hN : ∑ p ∈ Finset.range n, m p using Nat.strong_induction_on generalizing m with
  | _ N ih =>
    by_cases hb : ∀ p < n, m p < 2 * n
    · refine Submodule.subset_span ⟨fun p => if p < n then m p else 0, fun p => ?_, 1, ?_⟩
      · dsimp only
        split_ifs with h
        · exact (hb p h).le
        · exact Nat.zero_le _
      · have e : dotList n (fun p => if p < n then m p else 0) = dotList n m :=
          List.flatMap_congr fun p hp => by simp only [List.mem_range.mp hp, ↓reduceIte]
        rw [e, map_one, End.one_def, Category.comp_id]
    · simp only [not_forall, not_lt] at hb
      obtain ⟨p, hp, hmp⟩ := hb
      have hsn : (colPos t t[p]).card ≤ n := by
        have : colPos t t[p] ⊆ Finset.range n := fun q hq =>
          Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp (mem_colPos.mp hq)).1
        simpa using Finset.card_le_card this
      have hA : p ∉ List.range' 0 p := by simp
      have hB : p ∉ List.range' (p + 1) (n - (p + 1)) := by simp
      have key : dcl D Sc t (dotList n m) = ∑ j ∈ Finset.range (colPos t t[p]).card,
          ((-1 : k) ^ j) • (dcl D Sc t (dotList n (Function.update m p (m p - 2 * (j + 1)))) ≫
            zeta D Sc t (MvPolynomial.X (t[p], j + 1))) := by
        conv_lhs => rw [dotList_split hp, show m p = (m p - 2 * (colPos t t[p]).card) +
          2 * (colPos t t[p]).card by omega, List.replicate_add, dcl_append, dcl_append,
          dcl_append, dcl_replicate_card D Sc hp]
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        congr 1
        rw [dotList_split hp, Function.update_self, flatMap_update hA, flatMap_update hB,
          show m p - 2 * (j + 1) = (m p - 2 * (colPos t t[p]).card) +
            2 * ((colPos t t[p]).card - (j + 1)) by omega, List.replicate_add, dcl_append,
          dcl_append, dcl_append]
        simp only [Category.assoc, zeta_comp]
      rw [key]
      refine Submodule.sum_mem _ fun j hj =>
        Submodule.smul_mem _ _ (comp_zeta_mem_red D Sc (ih _ ?_ _ rfl) _)
      rw [← hN]
      refine Finset.sum_lt_sum (fun q _ => ?_) ⟨p, Finset.mem_range.mpr hp, ?_⟩
      · by_cases hq : q = p
        · subst hq; rw [Function.update_self]; omega
        · rw [Function.update_of_ne hq]
      · rw [Function.update_self]; omega

/-! ## Words of a nonzero Hom space have the same letters -/

theorem act_perm (g : PG) (t : List I) : (g.act t).Perm t := by
  cases g with
  | dot p => exact List.Perm.refl _
  | cross a =>
    simp only [PG.act]
    split
    · next x y r h =>
      conv_rhs => rw [← List.take_append_drop a t, h]
      exact List.Perm.append_left _ (List.Perm.swap _ _ _)
    · exact List.Perm.refl _

theorem tgt_perm (t : List I) (gs : List PG) : (tgt t gs).Perm t := by
  induction gs generalizing t with
  | nil => exact List.Perm.refl _
  | cons g gs ih => exact (ih _).trans (act_perm g t)

theorem hom_eq_zero_of_not_perm {t t' : List I} (h : ¬ t'.Perm t)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) : f = 0 := by
  have hf : f ∈ (⊤ : Submodule k _) := Submodule.mem_top
  rw [← span_normalForms D Sc t t'] at hf
  have e : {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') |
      ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
        ∃ w : Equiv.Perm (Fin t.length),
          ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (Categorification.TypeA.canWord t.length w)) h = f}
        = ∅ := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨l, -, -, w, hc, -⟩
    exact h (tgt_eq hc ▸ tgt_perm t _)
  rwa [e, Submodule.span_empty, Submodule.mem_bot] at hf

/-! ## Central elements of `H_n` -/

section Hn
variable {n : ℕ}

/-- The central element `∑_{t ∈ W} 1_t ζ_t(q)` of `H_n`. -/
def zetaHn (W : Finset (Word I n)) (q : MvPolynomial (I × ℕ) k) : Hn D Sc n :=
  ∑ t ∈ W, Hn.single t t (zeta D Sc t.val q)

theorem zetaHn_mul_single (W : Finset (Word I n)) (q : MvPolynomial (I × ℕ) k) (a b : Word I n)
    (f : wordObj D Sc b ⟶ wordObj D Sc a) (ha : a ∈ W) :
    zetaHn D Sc W q * Hn.single a b f = Hn.single a b (f ≫ zeta D Sc a.val q) := by
  classical
  rw [zetaHn, Finset.sum_mul, Finset.sum_eq_single a]
  · exact Hn.single_mul_single a a b _ f
  · intro t _ hta
    exact FiniteHomMatrix.single_mul_single_of_ne t t a b hta _ f
  · intro h; exact absurd ha h

theorem single_mul_zetaHn (W : Finset (Word I n)) (q : MvPolynomial (I × ℕ) k) (a b : Word I n)
    (f : wordObj D Sc b ⟶ wordObj D Sc a) (hb : b ∈ W) :
    Hn.single a b f * zetaHn D Sc W q = Hn.single a b (zeta D Sc b.val q ≫ f) := by
  classical
  rw [zetaHn, Finset.mul_sum, Finset.sum_eq_single b]
  · exact Hn.single_mul_single a b b f _
  · intro t _ htb
    exact FiniteHomMatrix.single_mul_single_of_ne a b t t (Ne.symm htb) f _
  · intro h; exact absurd hb h

/-- `W` is a union of blocks: closed under permuting the letters of a word. -/
def IsBlock (W : Finset (Word I n)) : Prop := ∀ a b : Word I n, a.val.Perm b.val → (a ∈ W ↔ b ∈ W)

theorem zetaHn_mem_center {W : Finset (Word I n)} (hW : IsBlock W) (q : MvPolynomial (I × ℕ) k) :
    zetaHn D Sc W q ∈ Set.center (Hn D Sc n) := by
  refine Semigroup.mem_center_iff.mpr fun x => ?_
  induction x using FiniteHomMatrix.induction with
  | hz => rw [zero_mul, mul_zero]
  | ha x y hx hy => rw [add_mul, mul_add, hx, hy]
  | hs a b f =>
    by_cases hf : f = 0
    · subst hf
      have : FiniteHomMatrix.single (obj := wordObj D Sc) a b 0 = 0 := by
        simp [FiniteHomMatrix.single]
      rw [this, zero_mul, mul_zero]
    have hp : a.val.Perm b.val := by
      by_contra h
      exact hf (hom_eq_zero_of_not_perm D Sc h f)
    by_cases hb : b ∈ W
    · have ha : a ∈ W := (hW a b hp).mpr hb
      rw [single_mul_zetaHn D Sc W q a b f hb, zetaHn_mul_single D Sc W q a b f ha]
      congr 1
      exact zeta_comp D Sc f q
    · have ha : a ∉ W := fun ha => hb ((hW a b hp).mp ha)
      classical
      rw [zetaHn, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_eq_zero fun t ht => FiniteHomMatrix.single_mul_single_of_ne a b t t
          (by rintro rfl; exact hb ht) f _,
        Finset.sum_eq_zero fun t ht => FiniteHomMatrix.single_mul_single_of_ne t t a b
          (by rintro rfl; exact ha ht) _ f]

/-- The combinations `∑_{g ∈ G} z_g g` with central coefficients `z_g`. -/
def centreSpan (G : Finset (Hn D Sc n)) : Submodule k (Hn D Sc n) where
  carrier := {x | ∃ c : Hn D Sc n → Hn D Sc n, (∀ g, c g ∈ Set.center (Hn D Sc n)) ∧
    x = ∑ g ∈ G, c g * g}
  zero_mem' := ⟨0, fun _ => Set.zero_mem_center, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun g => Set.add_mem_center (hc g) (hc' g), by
      simp [add_mul, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    refine ⟨a • c, fun g => Semigroup.mem_center_iff.mpr fun y => ?_, ?_⟩
    · rw [Pi.smul_apply, mul_smul_comm, smul_mul_assoc, Semigroup.mem_center_iff.mp (hc g) y]
    · simp [Finset.smul_sum, smul_mul_assoc]

theorem mul_mem_centreSpan {G : Finset (Hn D Sc n)} {z g : Hn D Sc n}
    (hz : z ∈ Set.center (Hn D Sc n)) (hg : g ∈ G) : z * g ∈ centreSpan D Sc G := by
  classical
  refine ⟨fun g' => if g' = g then z else 0, fun g' => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hz
    · exact Set.zero_mem_center
  · simp [hg]

open scoped Classical in
open Categorification.TypeA in
/-- A generator: the matrix entry `x^m ψ_w : b → a` at `(a, b)`, with exponents `m_p ≤ 2n`, or
zero if the canonical word of `w` does not go from `b` to `a`. -/
def genElt (a b : Word I n) (m : Fin n → Fin (2 * n + 1)) (w : Equiv.Perm (Fin n)) :
    Hn D Sc n :=
  if h : SChain b.val (pl b.val ((dotList n fun p => if hp : p < n then (m ⟨p, hp⟩ : ℕ) else 0).map
      PG.dot ++ cw (canWord n w))) a.val then
    Hn.single a b (cl D Sc b.val a.val _ h) else 0

/-- The finite generating set of the block `W` over the centre. -/
def gens (W : Finset (Word I n)) : Finset (Hn D Sc n) := by
  classical
  exact ((W ×ˢ W) ×ˢ (Finset.univ ×ˢ Finset.univ)).image
    fun x => genElt D Sc x.1.1 x.1.2 x.2.1 x.2.2

theorem count_dotList (n : ℕ) (m : ℕ → ℕ) (a : ℕ) :
    (dotList n m).count a = if a < n then m a else 0 := by
  rw [dotList, List.count_flatMap]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Function.comp_apply, List.count_replicate, beq_iff_eq]
    rcases lt_trichotomy a n with h | rfl | h
    · simp [h, show a < n + 1 by omega, show n ≠ a by omega]
    · simp
    · simp [show ¬ a < n by omega, show ¬ a < n + 1 by omega, show n ≠ a by omega]

theorem perm_dotList {n : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < n) :
    l.Perm (dotList n fun p => l.count p) := by
  rw [List.perm_iff_count]
  intro a
  rw [count_dotList]
  split_ifs with ha
  · rfl
  · exact List.count_eq_zero.mpr fun h => ha (hl a h)

open Categorification.TypeA in
theorem single_mem_centreSpan {W : Finset (Word I n)} (hW : IsBlock W) {a b : Word I n}
    (ha : a ∈ W) (hb : b ∈ W) (f : wordObj D Sc b ⟶ wordObj D Sc a) :
    Hn.single a b f ∈ centreSpan D Sc (gens D Sc W) := by
  obtain ⟨bv, rfl⟩ := b
  have hf : f ∈ (⊤ : Submodule k ((pres D Sc).obj (ob D bv) ⟶ (pres D Sc).obj (ob D a.val))) :=
    Submodule.mem_top
  rw [← span_normalForms D Sc bv a.val] at hf
  induction hf using Submodule.span_induction with
  | zero => simp
  | add f g _ _ hf hg =>
    simpa [FiniteHomMatrix.single, DFinsupp.single_add] using add_mem hf hg
  | smul c f _ hf =>
    simpa [FiniteHomMatrix.single, DFinsupp.single_smul] using
      (centreSpan D Sc (gens D Sc W)).smul_mem c hf
  | mem f hf =>
    obtain ⟨l, -, hl, w, h, rfl⟩ := hf
    set R := cw (canWord bv.length w)
    have hsingle_smul : ∀ (c : k) (F : (pres D Sc).obj (ob D bv) ⟶ (pres D Sc).obj (ob D a.val)),
        Hn.single (D := D) (Sc := Sc) a ⟨bv, rfl⟩ (c • F) = c • Hn.single a ⟨bv, rfl⟩ F := by
      intro c F; simp [DFinsupp.single_smul]
    -- sort the dots into `dotList`
    obtain ⟨c, -, h', e⟩ := dots_perm (D := D) (Sc := Sc) [] R (perm_dotList hl) hl h
    have e' : cl D Sc bv a.val (l.map PG.dot ++ R) h = c • cl D Sc bv a.val
        ((dotList bv.length fun p => l.count p).map PG.dot ++ R) h' := e
    rw [e', hsingle_smul]
    refine Submodule.smul_mem _ c ?_
    generalize (fun p => l.count p) = m at h' ⊢
    have hR : SChain bv (pl bv R) a.val := by
      have := sChain_suffix (Q := []) (M := (dotList bv.length m).map PG.dot) (R := R) h'
      simpa using this
    have hsplit : cl D Sc bv a.val ((dotList bv.length m).map PG.dot ++ R) h' =
        dcl D Sc bv (dotList bv.length m) ≫ cl D Sc bv a.val R hR := by
      rw [dcl, cl_comp]
    rw [hsplit]
    have key : ∀ g ∈ Red D Sc bv, Hn.single (D := D) (Sc := Sc) a ⟨bv, rfl⟩
        (g ≫ cl D Sc bv a.val R hR) ∈ centreSpan D Sc (gens D Sc W) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | zero => simp
      | add f g _ _ hf hg =>
        simpa [Preadditive.add_comp, FiniteHomMatrix.single, DFinsupp.single_add] using
          add_mem hf hg
      | smul c f _ hf =>
        rw [Linear.smul_comp, hsingle_smul]
        exact Submodule.smul_mem _ c hf
      | mem g hg =>
        obtain ⟨m', hm', q, rfl⟩ := hg
        rw [Category.assoc, zeta_comp, ← Category.assoc,
          ← zetaHn_mul_single D Sc W q a ⟨bv, rfl⟩ _ ha]
        refine mul_mem_centreSpan D Sc (zetaHn_mem_center D Sc hW q) ?_
        set mf : Fin bv.length → Fin (2 * bv.length + 1) := fun p => ⟨m' p, by
          have := hm' p; omega⟩
        have hd : (dotList bv.length fun p => if hp : p < bv.length then (mf ⟨p, hp⟩ : ℕ) else 0) =
            dotList bv.length m' :=
          List.flatMap_congr fun p hp => by simp [List.mem_range.mp hp, mf]
        have hS : SChain bv (pl bv ((dotList bv.length fun p =>
            if hp : p < bv.length then (mf ⟨p, hp⟩ : ℕ) else 0).map PG.dot ++
              cw (canWord bv.length w))) a.val := by
          rw [hd]; exact sChain_append_of (sChain_dots bv _) hR
        have hg : genElt D Sc a ⟨bv, rfl⟩ mf w = Hn.single a ⟨bv, rfl⟩
            (dcl D Sc bv (dotList bv.length m') ≫ cl D Sc bv a.val R hR) := by
          simp only [genElt, hS, ↓reduceDIte]
          rw [dcl, cl_comp]
          congr 1
          refine cl_congr D Sc _ _ ?_
          rw [hd]
        rw [← hg]
        classical
        exact Finset.mem_image.mpr ⟨((a, ⟨bv, rfl⟩), (mf, w)), by simp [ha, hb], rfl⟩
    exact key _ (dcl_dotList_mem D Sc bv m)

/-- **`H_n` is finite over its centre, block by block** (BE2, arXiv:1701.04133v2, §11, proof of
Theorem 11.7). For a finite set `W` of words closed under permuting letters, there is a finite
set `G ⊆ H_n` such that every element of `H_n` supported on `W × W` is `∑_{g ∈ G} z_g g` with
every `z_g` central in `H_n`. -/
theorem exists_centre_finite (W : Finset (Word I n)) (hW : IsBlock W) :
    ∃ G : Finset (Hn D Sc n), ∀ x : Hn D Sc n, (∀ a b, x (a, b) ≠ 0 → a ∈ W ∧ b ∈ W) →
      ∃ c : Hn D Sc n → Hn D Sc n, (∀ g, c g ∈ Set.center (Hn D Sc n)) ∧
        x = ∑ g ∈ G, c g * g := by
  refine ⟨gens D Sc W, fun x hx => ?_⟩
  suffices x ∈ centreSpan D Sc (gens D Sc W) from this
  classical
  rw [← DFinsupp.sum_single (f := x)]
  refine Submodule.sum_mem _ fun p hp => ?_
  obtain ⟨ha, hb⟩ := hx p.1 p.2 (DFinsupp.mem_support_iff.mp hp)
  convert single_mem_centreSpan D Sc hW ha hb (x p) using 1
  simp only [Hn.single, FiniteHomMatrix.single]
  congr
  exact Subsingleton.elim _ _

/-- **`H_n` is finite over its centre** for a finite colour set. -/
theorem exists_centre_finite_of_finite [Finite I] :
    ∃ G : Finset (Hn D Sc n), ∀ x : Hn D Sc n, ∃ c : Hn D Sc n → Hn D Sc n,
      (∀ g, c g ∈ Set.center (Hn D Sc n)) ∧ x = ∑ g ∈ G, c g * g := by
  classical
  have := Fintype.ofFinite I
  let : Fintype (Word I n) := inferInstanceAs (Fintype (List.Vector I n))
  obtain ⟨G, hG⟩ := exists_centre_finite D Sc (Finset.univ : Finset (Word I n)) (by simp [IsBlock])
  exact ⟨G, fun x => hG x fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩

end Hn

end OddMath.QuiverHecke
