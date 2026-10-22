/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.DividedPowerSpan

/-!
# Indecomposable summands of words are absolutely indecomposable of type M

Brundan–Ellis, arXiv:1701.04133v2, **Corollary 11.4**, in its projective form: over a field `k`,
let `P = (t, f)` be an indecomposable summand of a word `t` in `Ḣ_{q,π}`, cut out by an even
degree-zero idempotent `f`. Then

* every even degree-zero endomorphism of `P` is a scalar plus a nilpotent, i.e. the local ring
  `End(P)` has residue field `k` (`CornerResidue`); this is the projective counterpart of the
  absolute irreducibility of the simple heads;
* `P` has no odd degree-zero automorphism, i.e. `P ≇ ΠP` (`CornerNoOddUnit`); this is type `M`.

BE2 deduce the corollary from Theorem 11.3 by the counting argument of Khovanov–Lauda,
arXiv:0803.4121v2, Corollary 3.19 (absolute irreducibility) and Hill–Wang, arXiv:1202.2769v2,
Proposition 6.15 (type `M`). Here both parts are proved instead along the induction of the
surjectivity half of Theorem 11.3 (`OddMath.QuiverHecke.DividedPowerSpan`), on the length of the
word and then downwards on the length of an `i`-tail. The base case is the empty word, whose
endomorphisms are scalars. In the inductive step `P` is a summand of `Z ⊗ P(i^{(ε)})` with `Z` an
indecomposable summand of `s`. Either `P` is a summand of a word with a longer `i`-tail
(induction), or the complementary summand of `Z ⊗ P(i^{(ε)})` is a sum of maps through longer
tails. In the latter case, modulo maps through longer tails, every degree-zero endomorphism of
`P` has leading term `a ⊗ 1_{i^{(ε)}}` with `a` an endomorphism of `Z` of the same parity
(`tailT_conj_sub_mem`, using that `P(i^{(ε)})` has only scalar endomorphisms in degrees `≤ 0`).
So the two properties pass from `Z` to `P`.

## Main declarations

* `CornerResidue f`, `CornerNoOddUnit f`, `CornerTypeM f`: the two properties of an idempotent.
* `CornerTypeM.of_retracts`: they depend only on the summand, not on the idempotent.
* `cornerTypeM_of_retract_word`, `cornerTypeM_of_isIndec`: Corollary 11.4.
-/

noncomputable section

open CategoryTheory StringDiagrams MonoidalCategory GradedSupercategory KrullSchmidt
open CategoryTheory.Idempotents OddMath.SKM.Summands

namespace OddMath.QuiverHecke

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X}
  {k : Type w} [Field k] {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D}
  {hc : Sc.Homogeneous}

/-! ## The two properties -/

section Corner

variable {t : List I}

/-- Every even degree-zero endomorphism in the corner of `f` is a scalar multiple of `f` plus a
nilpotent: the local ring `End(t, f)` has residue field `k`. -/
def CornerResidue (f : HEnd D Sc sy hc t) : Prop :=
  ∀ a : HEnd D Sc sy hc t, a ∈ homPiece D Sc sy hc t t 0 0 → f ≫ a ≫ f = a →
    ∃ c : k, IsNilpotent (id (a - c • f) : End (hObj D Sc sy hc t))

/-- The corner of `f` has no odd degree-zero unit: `(t, f) ≇ Π(t, f)`. -/
def CornerNoOddUnit (f : HEnd D Sc sy hc t) : Prop :=
  ∀ x y : HEnd D Sc sy hc t, x ∈ homPiece D Sc sy hc t t 0 1 → y ∈ homPiece D Sc sy hc t t 0 1 →
    f ≫ x ≫ f = x → f ≫ y ≫ f = y → x ≫ y = f → y ≫ x = f → False

/-- **Corollary 11.4 for one summand**: residue field `k` and type `M`. -/
def CornerTypeM (f : HEnd D Sc sy hc t) : Prop :=
  CornerResidue f ∧ CornerNoOddUnit f

end Corner

/-! ## Invariance under isomorphism of summands -/

section Transfer

variable {t t' : List I} {f : HEnd D Sc sy hc t} {f' : HEnd D Sc sy hc t'}
  {α : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'} {β : hObj D Sc sy hc t' ⟶ hObj D Sc sy hc t}

theorem conj_pow_succ (hαβ : α ≫ β = f) {x : HEnd D Sc sy hc t} (hx : x ≫ f = x) (n : ℕ) :
    (id (β ≫ x ≫ α) : End (hObj D Sc sy hc t')) ^ (n + 1) =
      β ≫ ((id x : End (hObj D Sc sy hc t)) ^ (n + 1) : End (hObj D Sc sy hc t)) ≫ α := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (id (β ≫ x ≫ α) : End (hObj D Sc sy hc t')) (n + 1), End.mul_def, ih,
      pow_succ (id x : End (hObj D Sc sy hc t)) (n + 1), End.mul_def]
    simp only [id, Category.assoc]
    rw [reassoc_of% hαβ, reassoc_of% hx]

theorem cornerTypeM_of_equiv {d : ℤ} {q : ZMod 2} (hf : f ≫ f = f)
    (hα : α ∈ homPiece D Sc sy hc t t' d q) (hβ : β ∈ homPiece D Sc sy hc t' t (-d) q)
    (hαc : f ≫ α = α) (hβc : β ≫ f = β) (hαβ : α ≫ β = f) (hβα : β ≫ α = f')
    (h : CornerTypeM f) : CornerTypeM f' := by
  have hαc' : α ≫ f' = α := by rw [← hβα, reassoc_of% hαβ, hαc]
  have hβc' : f' ≫ β = β := by rw [← hβα, Category.assoc, hαβ, hβc]
  have hconj : ∀ {pa : ZMod 2} {a : HEnd D Sc sy hc t'}, a ∈ homPiece D Sc sy hc t' t' 0 pa →
      α ≫ a ≫ β ∈ homPiece D Sc sy hc t t 0 pa := fun {pa a} ha =>
    mem_homPiece_cast (comp_mem_homPiece hα (comp_mem_homPiece ha hβ)) (by ring)
      (by rw [add_comm pa, ← add_assoc, Supercategory.zmod2_add_self, zero_add])
  have hcorner : ∀ {a : HEnd D Sc sy hc t'}, f ≫ (α ≫ a ≫ β) ≫ f = α ≫ a ≫ β := fun {a} => by
    simp only [Category.assoc, hβc]; rw [reassoc_of% hαc]
  have hback : ∀ {a : HEnd D Sc sy hc t'}, f' ≫ a ≫ f' = a → β ≫ (α ≫ a ≫ β) ≫ α = a :=
    fun {a} ha => by simp only [Category.assoc]; rw [reassoc_of% hβα, hβα]; exact ha
  refine ⟨fun a ha hfa => ?_, fun x y hx hy hfx hfy hxy hyx => ?_⟩
  · obtain ⟨c, N, hN⟩ := h.1 _ (hconj ha) hcorner
    refine ⟨c, N + 1, ?_⟩
    have hx : (α ≫ a ≫ β - c • f) ≫ f = α ≫ a ≫ β - c • f := by
      rw [Preadditive.sub_comp, Linear.smul_comp, hf]; simp only [Category.assoc, hβc]
    have e : a - c • f' = β ≫ (α ≫ a ≫ β - c • f) ≫ α := by
      rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul,
        reassoc_of% hβc, hβα, hback hfa]
    change (id (a - c • f') : End (hObj D Sc sy hc t')) ^ (N + 1) = 0
    rw [e, conj_pow_succ hαβ hx, pow_succ, hN, zero_mul]
    simp
  · have hf' : f' ≫ f' = f' := by rw [← hβα, Category.assoc, reassoc_of% hαβ, reassoc_of% hβc]
    have hr : ∀ {g : HEnd D Sc sy hc t'}, f' ≫ g ≫ f' = g → g ≫ f' = g := fun {g} hg => by
      rw [← hg]; simp only [Category.assoc, hf']
    have hprod : ∀ {g g' : HEnd D Sc sy hc t'}, f' ≫ g ≫ f' = g → g ≫ g' = f' →
        (α ≫ g ≫ β) ≫ α ≫ g' ≫ β = f := fun {g g'} hg hgg => by
      simp only [Category.assoc]
      rw [reassoc_of% hβα, reassoc_of% (hr hg), reassoc_of% hgg, reassoc_of% hαc', hαβ]
    exact h.2 (α ≫ x ≫ β) (α ≫ y ≫ β) (hconj hx) (hconj hy) hcorner hcorner (hprod hfx hxy)
      (hprod hfy hyx)

variable {e : HEnd D Sc sy hc t} {e' : HEnd D Sc sy hc t'} {he : e ≫ e = e} {he' : e' ≫ e' = e'}
  {hd0 : e ∈ degree (R := k) _ _ 0} {hp0 : e ∈ Supercategory.parity (R := k) _ _ 0}
  {hd0' : e' ∈ degree (R := k) _ _ 0} {hp0' : e' ∈ Supercategory.parity (R := k) _ _ 0}
  {n n' : ℤ} {p p' : ZMod 2}

/-- **The properties depend only on the summand.** If `Y` is a retract of `Q^n Π^p (t, e)` and of
`Q^{n'} Π^{p'} (t', e')`, the two idempotents cutting it out have the same properties. -/
theorem CornerTypeM.of_retracts {Y : HKar D Sc sy hc}
    {u : Y ⟶ raw (k := k) he hd0 hp0 n p} {v : raw (k := k) he hd0 hp0 n p ⟶ Y} (huv : u ≫ v = 𝟙 Y)
    {u' : Y ⟶ raw (k := k) he' hd0' hp0' n' p'} {v' : raw (k := k) he' hd0' hp0' n' p' ⟶ Y}
    (huv' : u' ≫ v' = 𝟙 Y) (h : CornerTypeM (evR (v ≫ u))) : CornerTypeM (evR (v' ≫ u')) := by
  refine cornerTypeM_of_equiv (α := evR (v ≫ u')) (β := evR (v' ≫ u)) (d := n - n') (q := p + p')
    (retract_idem u v huv) ⟨evR_mem_degree _, evR_mem_parity _⟩
    ⟨by simpa using evR_mem_degree (v' ≫ u), by simpa [add_comm] using evR_mem_parity (v' ≫ u)⟩
    ?_ ?_ ?_ ?_ h
  · rw [← evR_comp]; simp only [Category.assoc]; rw [reassoc_of% huv]
  · rw [← evR_comp]; simp only [Category.assoc]; rw [reassoc_of% huv]
  · rw [← evR_comp]; simp only [Category.assoc]; rw [reassoc_of% huv']
  · rw [← evR_comp]; simp only [Category.assoc]; rw [reassoc_of% huv]

end Transfer

/-! ## The inductive step -/

section Step

theorem pow_succ_mem_corner {t : List I} {f x : HEnd D Sc sy hc t} (hf : f ≫ f = f)
    (hx : x ∈ homPiece D Sc sy hc t t 0 0) (hfx : f ≫ x ≫ f = x) (M : ℕ) :
    (id x : End (hObj D Sc sy hc t)) ^ (M + 1) ∈ homPiece D Sc sy hc t t 0 0 ∧
      f ≫ ((id x : End (hObj D Sc sy hc t)) ^ (M + 1) : End (hObj D Sc sy hc t)) ≫ f =
        (id x : End (hObj D Sc sy hc t)) ^ (M + 1) := by
  have hl : f ≫ x = x := by rw [← hfx, reassoc_of% hf]
  induction M with
  | zero => simpa using ⟨hx, hfx⟩
  | succ M ih =>
    rw [pow_succ, End.mul_def]
    refine ⟨mem_homPiece_cast (comp_mem_homPiece hx ih.1) (by simp) (by simp), ?_⟩
    have hr : ((id x : End (hObj D Sc sy hc t)) ^ (M + 1) : End (hObj D Sc sy hc t)) ≫ f =
        (id x : End (hObj D Sc sy hc t)) ^ (M + 1) := by
      rw [← ih.2]; simp only [Category.assoc, hf]
    simp only [id, Category.assoc] at hr ⊢
    rw [hr, reassoc_of% hl]

variable {s : List I} {i : I} {ε : ℕ} {b : HEnd D Sc sy hc (List.replicate ε i)}
  (hb : b ≫ b = b) (hb0 : b ∈ homPiece D Sc sy hc (List.replicate ε i) (List.replicate ε i) 0 0)
  (hcorner : ∀ {n : ℤ} {p : ZMod 2} {c : HEnd D Sc sy hc (List.replicate ε i)},
    c ∈ homPiece D Sc sy hc (List.replicate ε i) (List.replicate ε i) n p → n ≤ 0 →
      b ≫ c ≫ b ∈ k ∙ b)
include hb hb0 hcorner

/-- **The step.** Let `z` be an even degree-zero idempotent of `s` cutting out an indecomposable
summand with residue field `k` and of type `M`, and `f₁` an idempotent in the corner of
`e = z ⊗ b` cutting out an indecomposable summand. If `f₁` is not, but `e - f₁` is, a sum of maps
through words ending in `i^{ε+1}`, then `f₁` has residue field `k` and type `M`. -/
theorem cornerTypeM_of_tail {z : HEnd D Sc sy hc s} (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz : z ≫ z = z)
    (hlocz : ∀ a : HEnd D Sc sy hc s, a ∈ homPiece D Sc sy hc s s 0 0 → z ≫ a ≫ z = a →
      IsNilpotent (id a : End (hObj D Sc sy hc s)) ∨ ∃ a' : HEnd D Sc sy hc s,
        a' ∈ homPiece D Sc sy hc s s 0 0 ∧ a ≫ a' = z ∧ a' ≫ a = z)
    (hMz : CornerTypeM z) {f₁ : HEnd D Sc sy hc (s ++ List.replicate ε i)} (hi₁ : f₁ ≫ f₁ = f₁)
    (hf₁0 : f₁ ∈ homPiece D Sc sy hc _ _ 0 0)
    (hl₁ : tailT s b z ≫ f₁ = f₁) (hr₁ : f₁ ≫ tailT s b z = f₁)
    (hJ₂ : tailT s b z - f₁ ∈ tailJ D Sc sy hc s i ε 0) (hJ₁ : f₁ ∉ tailJ D Sc sy hc s i ε 0)
    (hloc₁ : ∀ a : HEnd D Sc sy hc (s ++ List.replicate ε i), a ∈ homPiece D Sc sy hc _ _ 0 0 →
      f₁ ≫ a ≫ f₁ = a → IsNilpotent (id a : End (hObj D Sc sy hc (s ++ List.replicate ε i))) ∨
        ∃ a' : HEnd D Sc sy hc (s ++ List.replicate ε i), a' ∈ homPiece D Sc sy hc _ _ 0 0 ∧
          a ≫ a' = f₁ ∧ a' ≫ a = f₁) :
    CornerTypeM f₁ := by
  have hEc : ∀ {g : HEnd D Sc sy hc (s ++ List.replicate ε i)}, f₁ ≫ g ≫ f₁ = g →
      tailT s b z ≫ g ≫ tailT s b z = g := fun {g} hg => by
    rw [← hg]; simp only [Category.assoc, hr₁]; rw [reassoc_of% hl₁]
  have hzc : ∀ {g g' : HEnd D Sc sy hc s}, z ≫ g ≫ z = g → z ≫ g' ≫ z = g' →
      z ≫ (g ≫ g') ≫ z = g ≫ g' := fun {g g'} hg hg' => by
    have hl : z ≫ g = g := by rw [← hg, reassoc_of% hz]
    have hr : g' ≫ z = g' := by rw [← hg']; simp only [Category.assoc, hz]
    simp only [Category.assoc]; rw [hr, reassoc_of% hl]
  refine ⟨fun g hg hfg => ?_, fun x y hx hy hfx hfy hxy hyx => ?_⟩
  · -- residue field: `g - c f₁` has a power in `J`, hence is nilpotent
    obtain ⟨a, ha, haz, hv⟩ := tailT_conj_sub_mem hb0 hcorner hz0 hz hg
    rw [hEc hfg] at hv
    obtain ⟨c, hcn⟩ := hMz.1 a ha haz
    have hn : a - c • z ∈ homPiece D Sc sy hc s s 0 0 := sub_mem ha (Submodule.smul_mem _ c hz0)
    have hT : tailT s b (a - c • z) = tailT s b a - c • tailT s b z := by
      rw [sub_eq_add_neg, tailT_add, ← neg_smul, tailT_smul, neg_smul, ← sub_eq_add_neg]
    have hv' : (g - c • f₁) - tailT s b (a - c • z) ∈ tailV D Sc sy hc s i ε 1 0 := by
      have e : (g - c • f₁) - tailT s b (a - c • z) =
          (g - tailT s b a) + c • (tailT s b z - f₁) := by
        rw [hT, smul_sub]; abel
      rw [e]
      exact add_mem hv (Submodule.mem_sup_right (Submodule.smul_mem _ c hJ₂))
    obtain ⟨M, hM⟩ := pow_mem_tailJ_of_isNilpotent hb hb0 hn hcn hv'
    have hgc : g - c • f₁ ∈ homPiece D Sc sy hc _ _ 0 0 :=
      sub_mem hg (Submodule.smul_mem _ c hf₁0)
    have hfgc : f₁ ≫ (g - c • f₁) ≫ f₁ = g - c • f₁ := by
      rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul, hi₁,
        hi₁, hfg]
    obtain ⟨hP0, hPc⟩ := pow_succ_mem_corner hi₁ hgc hfgc M
    rcases hloc₁ _ hP0 hPc with ⟨N, hN⟩ | ⟨x', hx', hxx', -⟩
    · exact ⟨c, (M + 1) * N, by rw [pow_mul]; exact hN⟩
    · exact absurd (hxx' ▸ (by simpa using comp_mem_tailJ_right hx' hM)) hJ₁
  · -- type `M`: leading terms of an odd unit give an odd unit of `z`
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    obtain ⟨a, ha, haz, hva⟩ := tailT_conj_sub_mem hb0 hcorner hz0 hz hx
    rw [hEc hfx] at hva
    obtain ⟨a', ha', haz', hva'⟩ := tailT_conj_sub_mem hb0 hcorner hz0 hz hy
    rw [hEc hfy] at hva'
    have hT1 : ∀ {a : HEnd D Sc sy hc s}, a ∈ homPiece D Sc sy hc s s 0 1 →
        tailT s b a ∈ tailV D Sc sy hc s i ε 0 1 :=
      fun ha => Submodule.mem_sup_left (tailT_mem_tailN hb0 ha)
    have key : ∀ {w w' : HEnd D Sc sy hc (s ++ List.replicate ε i)} {a a' : HEnd D Sc sy hc s},
        a ∈ homPiece D Sc sy hc s s 0 1 → a' ∈ homPiece D Sc sy hc s s 0 1 →
        w - tailT s b a ∈ tailV D Sc sy hc s i ε 1 1 →
        w' - tailT s b a' ∈ tailV D Sc sy hc s i ε 1 1 →
        w ≫ w' - tailT s b (a ≫ a') ∈ tailV D Sc sy hc s i ε 1 0 := by
      intro w w' a a' ha ha' hw hw'
      have hw0 : w' ∈ tailV D Sc sy hc s i ε 0 1 := by
        simpa using add_mem (hT1 ha') (tailV_antitone 1 (Nat.zero_le 1) hw')
      have e : w ≫ w' - tailT s b (a ≫ a') =
          (w - tailT s b a) ≫ w' + tailT s b a ≫ (w' - tailT s b a') := by
        rw [← tailT_comp hb hb0 ha.2, Preadditive.sub_comp, Preadditive.comp_sub]; abel
      have h1 := tailV_comp hw hw0
      have h2 := tailV_comp (hT1 ha) hw'
      rw [h11, add_zero] at h1
      rw [h11, zero_add] at h2
      rw [e]; exact add_mem h1 h2
    have hxy' := key ha ha' hva hva'
    have hyx' := key ha' ha hva' hva
    rw [hxy] at hxy'
    rw [hyx] at hyx'
    have hprod : ∀ {a a' : HEnd D Sc sy hc s}, a ∈ homPiece D Sc sy hc s s 0 1 →
        a' ∈ homPiece D Sc sy hc s s 0 1 → a ≫ a' ∈ homPiece D Sc sy hc s s 0 0 :=
      fun ha ha' => mem_homPiece_cast (comp_mem_homPiece ha ha') (by simp) h11
    rcases hlocz _ (hprod ha ha') (hzc haz haz') with hn | ⟨r, hr, har, hra⟩
    · exact hJ₁ (idem_mem_tailJ_of_isNilpotent hb hb0 hi₁ (hprod ha ha') hn hxy')
    rcases hlocz _ (hprod ha' ha) (hzc haz' haz) with hn | ⟨r', -, -, hra'⟩
    · exact hJ₁ (idem_mem_tailJ_of_isNilpotent hb hb0 hi₁ (hprod ha' ha) hn hyx')
    have hza' : z ≫ a' = a' := by rw [← haz', reassoc_of% hz]
    have ha'z : a' ≫ z = a' := by rw [← haz']; simp only [Category.assoc, hz]
    have hrz : r ≫ z = z ≫ r := by
      calc r ≫ z = (r ≫ a ≫ a') ≫ r := by rw [← har]; simp only [Category.assoc]
        _ = z ≫ r := by rw [hra]
    have hlr : r' ≫ a' = a' ≫ r := by
      calc r' ≫ a' = r' ≫ a' ≫ (a ≫ a') ≫ r := by rw [har, ha'z]
        _ = (r' ≫ a' ≫ a) ≫ a' ≫ r := by simp only [Category.assoc]
        _ = a' ≫ r := by rw [hra', reassoc_of% hza']
    refine hMz.2 a (a' ≫ r) ha (mem_homPiece_cast (comp_mem_homPiece ha' hr) (by simp) (by simp))
      haz ?_ ?_ ?_
    · simp only [Category.assoc]; rw [hrz, reassoc_of% ha'z, reassoc_of% hza']
    · rw [← har, Category.assoc]
    · rw [← hlr, Category.assoc, ← hra']

end Step

/-! ## The induction -/

section Words

/-- **The inductive step** (as in `mk_mem_dpSpan_step`). Let `Y` be an indecomposable summand of
a shifted word `s i^ε`. If the indecomposable summands of shifts of `s`, and of shifted words of
the same length ending in `i^{ε+1}`, have residue field `k` and type `M`, so does `Y`. -/
theorem cornerTypeM_step {s : List I} {i : I} {ε : ℕ}
    (IHs : ∀ (n : ℤ) (p : ZMod 2) (Y : HKar D Sc sy hc), IsIndec Y →
      ∀ (u : Y ⟶ Wd D Sc sy hc s n p) (v : Wd D Sc sy hc s n p ⟶ Y), u ≫ v = 𝟙 Y →
      CornerTypeM (evR (v ≫ u)))
    (IHt : ∀ w : List I, List.replicate (ε + 1) i <:+ w →
      w.length = (s ++ List.replicate ε i).length → ∀ (n : ℤ) (p : ZMod 2) (Y : HKar D Sc sy hc),
      IsIndec Y → ∀ (u : Y ⟶ Wd D Sc sy hc w n p) (v : Wd D Sc sy hc w n p ⟶ Y), u ≫ v = 𝟙 Y →
      CornerTypeM (evR (v ≫ u)))
    {n : ℤ} {p : ZMod 2} {Y : HKar D Sc sy hc} (hY : IsIndec Y)
    (u : Y ⟶ Wd D Sc sy hc (s ++ List.replicate ε i) n p)
    (v : Wd D Sc sy hc (s ++ List.replicate ε i) n p ⟶ Y) (huv : u ≫ v = 𝟙 Y) :
    CornerTypeM (evR (v ≫ u)) := by
  classical
  have hb := dpIdem_idem D Sc sy hc i ε
  have hb0 := dpIdem_mem D Sc sy hc i ε
  -- the decomposition of `s` into indecomposables `Z_a`, with idempotents `z_a`
  obtain ⟨J, _, Z, ι, π, hZi, hιπ, -, hsumZ⟩ := exists_decomposition k (Wd D Sc sy hc s 0 0)
  let z : J → HEnd D Sc sy hc s := fun a => evR (π a ≫ ι a)
  have hz : ∀ a, z a ≫ z a = z a := fun a => retract_idem (ι a) (π a) (hιπ a)
  have hz0 : ∀ a, z a ∈ homPiece D Sc sy hc s s 0 0 :=
    fun a => ⟨retract_degree (ι a) (π a), retract_parity (ι a) (π a)⟩
  have hzsum : ∑ a, z a = 𝟙 _ := by
    change ∑ a, evR (π a ≫ ι a) = _
    rw [← evR_sum, hsumZ]
    rfl
  -- Lemma 11.1 for `i^ε`
  obtain ⟨C, _, mC, qC, σ, lam, hσ, hlam, hsl, hbσ, hlb⟩ := exists_dpSplitting D Sc sy hc i ε
  -- `1_{s i^ε} = ∑_{a,c} U_{ac} V_{ac}` through `Q^{m_c} Π^{q_c} (s i^ε, z_a ⊗ b)`
  let e : J → HEnd D Sc sy hc (s ++ List.replicate ε i) :=
    fun a => tailT s (dpIdem D Sc sy hc i ε) (z a)
  have he : ∀ a, e a ≫ e a = e a := fun a => tailT_idem hb hb0 (hz a) (hz0 a)
  have he0 : ∀ a, e a ∈ homPiece D Sc sy hc _ _ 0 0 := fun a => tailT_mem_homPiece hb0 (hz0 a)
  let R : J × C → HKar D Sc sy hc := fun x =>
    raw (k := k) (he x.1) (he0 x.1).1 (he0 x.1).2 (n + mC x.2) (p + qC x.2)
  let xU : J × C → HEnd D Sc sy hc (s ++ List.replicate ε i) := fun x =>
    (hObj D Sc sy hc s ◁ lam x.2) ≫ (z x.1 ▷ hObj D Sc sy hc (List.replicate ε i))
  let xV : J × C → HEnd D Sc sy hc (s ++ List.replicate ε i) := fun x =>
    (z x.1 ▷ hObj D Sc sy hc (List.replicate ε i)) ≫ (hObj D Sc sy hc s ◁ σ x.2)
  have hxU : ∀ x, xU x ∈ homPiece D Sc sy hc _ _ (-mC x.2) (qC x.2) := fun x =>
    mem_homPiece_cast (comp_mem_homPiece (whiskerLeft_mem_homPiece s (hlam x.2))
      (whiskerRight_mem_homPiece _ (hz0 x.1))) (add_zero _) (add_zero _)
  have hxV : ∀ x, xV x ∈ homPiece D Sc sy hc _ _ (mC x.2) (qC x.2) := fun x =>
    mem_homPiece_cast (comp_mem_homPiece (whiskerRight_mem_homPiece _ (hz0 x.1))
      (whiskerLeft_mem_homPiece s (hσ x.2))) (zero_add _) (zero_add _)
  let U : ∀ x, Wd D Sc sy hc (s ++ List.replicate ε i) n p ⟶ R x := fun x =>
    homR (xU x) (by rw [show n - (n + mC x.2) = -mC x.2 by ring]; exact (hxU x).1)
      (by rw [← add_assoc, Supercategory.zmod2_add_self, zero_add]; exact (hxU x).2)
      (by
        rw [Category.id_comp]
        simpa only [xU, e, tailT, Category.assoc] using
          corner_U (hz x.1) (hz0 x.1).2 hb0.2 (hlb x.2))
  let V : ∀ x, R x ⟶ Wd D Sc sy hc (s ++ List.replicate ε i) n p := fun x =>
    homR (xV x) (by rw [show n + mC x.2 - n = mC x.2 by ring]; exact (hxV x).1)
      (by rw [add_comm p, add_assoc, Supercategory.zmod2_add_self, add_zero]; exact (hxV x).2)
      (by
        rw [Category.comp_id]
        simpa only [xV, e, tailT, Category.assoc] using
          corner_V (hz x.1) (hz0 x.1).2 hb0.2 (hbσ x.2))
  have htot : ∑ x, U x ≫ V x = 𝟙 _ := by
    apply evR_injective
    rw [evR_sum, evR_id]
    simp only [evR_comp]
    change ∑ x, xU x ≫ xV x = 𝟙 _
    have h1 : ∀ x, xU x ≫ xV x = (hObj D Sc sy hc s ◁ (lam x.2 ≫ σ x.2)) ≫
        (z x.1 ▷ hObj D Sc sy hc (List.replicate ε i)) :=
      fun x => U_comp_V (hz x.1) (hz0 x.1).2 (hσ x.2).2
    simp only [h1]
    rw [Fintype.sum_prod_type_right]
    simp_rw [← Preadditive.comp_sum]
    rw [← sum_whiskerRight_hObj, hzsum, MonoidalSupercategory.id_whiskerRight (R := k)]
    simp_rw [Category.comp_id]
    rw [← whiskerLeft_sum_hObj, hsl, MonoidalSupercategory.whiskerLeft_id (R := k)]
    rfl
  -- `Y` is a summand of one of the `R x`
  have h1 : ∑ x, (u ≫ U x) ≫ (V x ≫ v) = 𝟙 Y := by
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, htot, Category.id_comp, huv]
  obtain ⟨x, -, v', hv'⟩ := exists_retract_of_sum k hY Finset.univ _ _ h1
  -- the idempotents `f₁ = v' u'` and `f₂ = e - f₁` in the corner of `e = z_a ⊗ b`
  have hi₁ := retract_idem (u ≫ U x) v' hv'
  have hf₁0 : evR (v' ≫ u ≫ U x) ∈ homPiece D Sc sy hc _ _ 0 0 :=
    ⟨retract_degree (u ≫ U x) v', retract_parity (u ≫ U x) v'⟩
  have hl₁ := retract_left (u ≫ U x) v'
  have hr₁ := retract_right (u ≫ U x) v'
  set f₁ := evR (v' ≫ u ≫ U x) with hf₁
  set f₂ := e x.1 - f₁ with hf₂
  have hi₂ : f₂ ≫ f₂ = f₂ := by
    simp only [f₂, Preadditive.sub_comp, Preadditive.comp_sub, he, hl₁, hr₁, hi₁, sub_self,
      sub_zero]
  have h₁₂ : f₁ ≫ f₂ = 0 := by simp only [f₂, Preadditive.comp_sub, hr₁, hi₁, sub_self]
  have hf₂0 : f₂ ∈ homPiece D Sc sy hc _ _ 0 0 := sub_mem (he0 x.1) hf₁0
  have he₁ : e x.1 ≫ f₁ ≫ e x.1 = f₁ := by rw [hr₁, hl₁]
  have he₂ : e x.1 ≫ f₂ ≫ e x.1 = f₂ := by
    simp only [f₂, Preadditive.sub_comp, Preadditive.comp_sub, he, hl₁, hr₁]
  have hloc := hloc_of_isIndec (hz x.1) (hz0 x.1)
    (IsIndec.of_iso (retractIso (ι x.1) (π x.1) (hιπ x.1)) (hZi x.1))
  have hY₁ := IsIndec.of_iso (retractIso (u ≫ U x) v' hv') hY
  refine CornerTypeM.of_retracts (u := u ≫ U x) (v := v') hv' huv ?_
  by_cases hJ₁ : f₁ ∈ tailJ D Sc sy hc s i ε 0
  · obtain ⟨w, hw, hl, n', p', u'', v'', huv''⟩ := exists_retract_word_of_mem_tailJ hi₁ hf₁0 hJ₁
      hY (retractIso (u ≫ U x) v' hv').hom (retractIso (u ≫ U x) v' hv').inv
      (retractIso (u ≫ U x) v' hv').hom_inv_id
    exact CornerTypeM.of_retracts huv'' hv' (IHt w hw hl n' p' Y hY u'' v'' huv'')
  · have hJ₂ : f₂ ∈ tailJ D Sc sy hc s i ε 0 :=
      (tail_idempotent_mem_tailJ hb hb0 (dpIdem_corner D Sc sy hc i ε) (hz0 x.1) (hz x.1) hloc
        hf₁0 hf₂0 he₁ he₂ hi₁ hi₂ h₁₂).resolve_left hJ₁
    exact cornerTypeM_of_tail hb hb0 (dpIdem_corner D Sc sy hc i ε) (hz0 x.1) (hz x.1) hloc
      (IHs 0 0 (Z x.1) (hZi x.1) (ι x.1) (π x.1) (hιπ x.1)) hi₁ hf₁0 hl₁ hr₁ hJ₂ hJ₁
      (hloc_of_isIndec hi₁ hf₁0 hY₁)

/-- Words of length zero: the endomorphisms of `𝟙` are scalars. -/
theorem cornerTypeM_nil {n : ℤ} {p : ZMod 2} {Y : HKar D Sc sy hc} (hY : IsIndec Y)
    (u : Y ⟶ Wd D Sc sy hc [] n p) (v : Wd D Sc sy hc [] n p ⟶ Y) (huv : u ≫ v = 𝟙 Y) :
    CornerTypeM (evR (v ≫ u)) := by
  have hidem := retract_idem u v huv
  refine ⟨fun a ha hfa => ?_, fun x y hx hy hfx hfy hxy hyx => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (mem_span_id_nil a)
    refine ⟨c, 1, ?_⟩
    have e : c • 𝟙 (hObj D Sc sy hc []) - c • evR (v ≫ u) = 0 := by
      conv_lhs => rw [← hfa]
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, hidem, sub_self]
    rw [pow_one]; exact e
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (mem_span_id_nil x)
    have hx0 : c • 𝟙 (hObj D Sc sy hc []) = 0 :=
      eq_zero_of_mem_homPiece hx (Submodule.smul_mem _ c ⟨GradedSupercategory.id_mem_degree _,
        Supercategory.id_mem _⟩) (Or.inr (by decide))
    rw [hx0, Limits.zero_comp] at hxy
    have hvu : v ≫ u = 0 := evR_injective hxy.symm
    have : 𝟙 Y = 0 := by
      rw [← huv, ← Category.comp_id (u ≫ v), ← huv]
      simp only [Category.assoc]
      rw [reassoc_of% hvu, Limits.zero_comp, Limits.comp_zero]
    exact hY.1 ((Limits.IsZero.iff_id_eq_zero _).2 this)

/-- **Summands of words.** Every indecomposable summand of a shifted word has residue field `k`
and type `M`: by induction on the length `m` of the word, and for fixed `m` by descending
induction on the length of an `i`-tail. -/
theorem cornerTypeM_of_retract_word (m : ℕ) :
    ∀ t : List I, t.length = m → ∀ (n : ℤ) (p : ZMod 2) (Y : HKar D Sc sy hc), IsIndec Y →
      ∀ (u : Y ⟶ Wd D Sc sy hc t n p) (v : Wd D Sc sy hc t n p ⟶ Y), u ≫ v = 𝟙 Y →
      CornerTypeM (evR (v ≫ u)) := by
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
  have tail : ∀ d ε (s : List I) (i : I), m - ε = d → (s ++ List.replicate ε i).length = m →
      1 ≤ ε → ∀ (n : ℤ) (p : ZMod 2) (Y : HKar D Sc sy hc), IsIndec Y →
      ∀ (u : Y ⟶ Wd D Sc sy hc (s ++ List.replicate ε i) n p)
        (v : Wd D Sc sy hc (s ++ List.replicate ε i) n p ⟶ Y), u ≫ v = 𝟙 Y →
      CornerTypeM (evR (v ≫ u)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IHd =>
    intro ε s i hd hlen hε n p Y hY u v huv
    have hs : s.length < m := by
      rw [List.length_append, List.length_replicate] at hlen
      omega
    refine cornerTypeM_step (fun n p Y hY u v huv => IHm s.length hs s rfl n p Y hY u v huv)
      (fun w hw hwl n p Y hY u v huv => ?_) hY u v huv
    obtain ⟨s', rfl⟩ := hw
    have hm : ε + 1 ≤ m := by
      rw [hlen, List.length_append, List.length_replicate] at hwl
      omega
    exact IHd (m - (ε + 1)) (by omega) (ε + 1) s' i rfl (hwl.trans hlen) (by omega) n p Y hY u v
      huv
  intro t ht n p Y hY u v huv
  rcases List.eq_nil_or_concat' t with rfl | ⟨s, i, rfl⟩
  · exact cornerTypeM_nil hY u v huv
  · exact tail _ 1 s i rfl (by simpa using ht) le_rfl n p Y hY u v huv

/-- **Brundan–Ellis, Corollary 11.4** (projective form). Over a field with homogeneous scalars,
let `f` be an even degree-zero idempotent of a word `t` such that `Q^n Π^p (t, f)` is
indecomposable in `Ḣ_{q,π}`. Then every even degree-zero endomorphism in the corner of `f` is a
scalar multiple of `f` plus a nilpotent (the local ring `End(t, f)` has residue field `k`), and
the corner of `f` has no odd degree-zero unit (`(t, f) ≇ Π(t, f)`: type `M`). -/
theorem cornerTypeM_of_isIndec {t : List I} {f : HEnd D Sc sy hc t} (hf : f ≫ f = f)
    (hf0 : f ∈ homPiece D Sc sy hc t t 0 0) {n : ℤ} {p : ZMod 2}
    (hind : IsIndec (raw (k := k) hf hf0.1 hf0.2 n p)) : CornerTypeM f := by
  let u : raw (k := k) hf hf0.1 hf0.2 n p ⟶ Wd D Sc sy hc t n p :=
    homR f (by simpa using hf0.1) (by rw [Supercategory.zmod2_add_self]; exact hf0.2)
      (by rw [Category.comp_id, hf])
  let v : Wd D Sc sy hc t n p ⟶ raw (k := k) hf hf0.1 hf0.2 n p :=
    homR f (by simpa using hf0.1) (by rw [Supercategory.zmod2_add_self]; exact hf0.2)
      (by rw [Category.id_comp, hf])
  have huv : u ≫ v = 𝟙 _ := evR_injective (by rw [evR_comp]; exact hf)
  have h := cornerTypeM_of_retract_word _ t rfl n p _ hind u v huv
  rwa [evR_comp, evR_homR, evR_homR, hf] at h

end Words

end OddMath.QuiverHecke
