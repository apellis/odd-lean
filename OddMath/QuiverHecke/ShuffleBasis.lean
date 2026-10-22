/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Basis
import Categorification.TypeA.Parabolic

/-!
# The shuffle basis: `1_{μ,ν} H(μ + ν)` is free over `H(μ) ⊗ H(ν)`

Hill–Wang, arXiv:1202.2769v2, **Proposition 6.4**, for the quiver Hecke superalgebras of
Brundan–Ellis, arXiv:1701.04133v2, §11 (input to BE2 Theorem 11.3): `1_{μ,ν} H(μ + ν)` is a free
graded left `H(μ) ⊗ H(ν)`-module with basis the elements `1_{μ,ν} τ_d`, `d` running over the
minimal length representatives of the cosets `(S_m × S_n) d` in `S_{m+n}`.

We prove the statement as in its proof, in the categorical form: for words `t`, `u'`, `v'` with
`|u'| + |v'| = |t|`, the elements `(a ⊗ b) ψ_d`, for `d` a shuffle (`TypeA.Shuffle`) and `a`, `b`
normal forms from the two halves of the top word of `ψ_d` to `u'` and `v'`, form a basis of
`Hom_H(t, u'v')` (`shuffleBasis`). Here `ψ_d` is the diagram of the canonical reduced word of `d`,
and `a ⊗ b = (1 ⊗ b)(a ⊗ 1)` in the monoidal supercategory `H`.

The proof is by triangularity against the normal form basis `basisNF`: moving the dots of `a` and
`b` below `ψ_d` and straightening the crossings, `(x^l ψ_{w₁} ⊗ x^{l'} ψ_{w₂}) ψ_d` agrees, up to
a unit and words with fewer crossings, with the normal form `x^{d⁻¹(l, m + l')} ψ_{(w₁ × w₂) d}`
(`shElt_approx`), and these leading terms run once over all normal forms (`ShIdx.leadEquiv`, by
the parabolic factorisation `TypeA.parabolicEquiv`). A family which is unitriangular with respect
to a basis is a basis (`basisOfTriangular`).

## Main results

* `cl_whiskerRight`, `cl_whiskerLeft`: whiskering words of positioned generators.
* `dots_down`: dots above a word of crossings move below it, to the permuted strands.
* `basisOfTriangular`: a unitriangular family is a basis.
* `shElt_approx`: the leading term of a shuffle basis element.
* `shuffleBasis` (**HW Proposition 6.4**).
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA MonoidalCategory
namespace OddMath.QuiverHecke

universe u v w
variable {I : Type u}

/-! ## Unitriangular families -/

section Triangular

variable {k V J : Type*} [CommRing k] [AddCommGroup V] [Module k V]

theorem repr_eq_zero_of_mem_span_image (e : Module.Basis J k V) {S : Set J} {x : V}
    (hx : x ∈ Submodule.span k (e '' S)) {j : J} (hj : j ∉ S) : e.repr x j = 0 := by
  rw [Module.Basis.mem_span_image] at hx
  by_contra h
  exact hj (hx (Finsupp.mem_support_iff.mpr h))

variable (e : Module.Basis J k V) (ℓ : J → ℕ) {b : J → V} {c : J → k}

/-- A family `b` with `b_j ≡ c_j e_j` modulo the span of the `e_x` with `ℓ x < ℓ j`, for units
`c_j`, is linearly independent. -/
theorem linearIndependent_of_triangular (hc : ∀ j, IsUnit (c j))
    (hb : ∀ j, b j - c j • e j ∈ Submodule.span k (e '' {x | ℓ x < ℓ j})) :
    LinearIndependent k b := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hne
  have hs : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hne⟩⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ ℓ hs
  rw [Finset.mem_filter] at hi₀
  have key : ∀ j ∈ s, g j * e.repr (b j) i₀ = if j = i₀ then g i₀ * c i₀ else 0 := by
    intro j hj
    by_cases hgj : g j = 0
    · split_ifs with h <;> simp_all
    have hlen := hmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
    have h0 := repr_eq_zero_of_mem_span_image e (hb j) (j := i₀) (by simp; omega)
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, sub_eq_zero] at h0
    rw [h0, e.repr_self, smul_eq_mul]
    split_ifs with h
    · subst h; simp
    · simp [Ne.symm h]
  have h1 := congrArg (fun v => e.repr v i₀) hg
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' s i₀] at h1
  simp only [hi₀.1, ↓reduceIte] at h1
  exact hi₀.2 ((hc i₀).mul_left_eq_zero.mp h1)

/-- A family `b` as in `linearIndependent_of_triangular` spans. -/
theorem span_eq_top_of_triangular (hc : ∀ j, IsUnit (c j))
    (hb : ∀ j, b j - c j • e j ∈ Submodule.span k (e '' {x | ℓ x < ℓ j})) :
    Submodule.span k (Set.range b) = ⊤ := by
  have he : ∀ n, ∀ j, ℓ j = n → e j ∈ Submodule.span k (Set.range b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hj
      have hlow : Submodule.span k (e '' {x | ℓ x < ℓ j}) ≤ Submodule.span k (Set.range b) :=
        Submodule.span_le.mpr (by
          rintro _ ⟨x, hx, rfl⟩
          exact ih (ℓ x) (hj ▸ hx) x rfl)
      obtain ⟨u, hu⟩ := hc j
      have : e j = (↑u⁻¹ : k) • (b j - (b j - c j • e j)) := by
        rw [sub_sub_cancel, smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
        (hlow (hb j)))
  rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact he _ j rfl

/-- The basis given by a unitriangular family. -/
def basisOfTriangular (hc : ∀ j, IsUnit (c j))
    (hb : ∀ j, b j - c j • e j ∈ Submodule.span k (e '' {x | ℓ x < ℓ j})) :
    Module.Basis J k V :=
  Module.Basis.mk (linearIndependent_of_triangular e ℓ hc hb)
    (span_eq_top_of_triangular e ℓ hc hb).ge

@[simp] theorem basisOfTriangular_apply (hc : ∀ j, IsUnit (c j))
    (hb : ∀ j, b j - c j • e j ∈ Submodule.span k (e '' {x | ℓ x < ℓ j})) (j : J) :
    basisOfTriangular e ℓ hc hb j = b j :=
  Module.Basis.mk_apply _ _ _

end Triangular

/-! ## Shifting and widening positioned words -/

/-- The generator `n` strands further right. -/
def PG.shift (n : ℕ) : PG → PG
  | .dot p => .dot (n + p)
  | .cross a => .cross (n + a)

@[simp] theorem PG.shift_dot (n p : ℕ) : (PG.dot p).shift n = .dot (n + p) := rfl
@[simp] theorem PG.shift_cross (n a : ℕ) : (PG.cross a).shift n = .cross (n + a) := rfl

theorem PG.ld_shift (l t : List I) (g : PG) :
    (g.shift l.length).ld (l ++ t) = (g.ld t).map (wh l []) := by
  cases g with
  | dot p =>
    simp only [PG.shift, PG.ld, List.drop_length_add_append]
    rcases hd : List.drop p t with _ | ⟨x, r⟩ <;> simp [wh, List.take_append]
  | cross a =>
    simp only [PG.shift, PG.ld, List.drop_length_add_append]
    rcases hd : List.drop a t with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [wh, List.take_append]

theorem PG.act_shift (l t : List I) (g : PG) :
    (g.shift l.length).act (l ++ t) = l ++ g.act t := by
  cases g with
  | dot p => rfl
  | cross a =>
    simp only [PG.shift, PG.act, List.drop_length_add_append]
    rcases hd : List.drop a t with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [List.take_append]

theorem pl_shift (l t : List I) (gs : List PG) :
    pl (l ++ t) (gs.map (PG.shift l.length)) = (pl t gs).map (wh l []) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => simp [PG.ld_shift, PG.act_shift, ih]

theorem tgt_shift (l t : List I) (gs : List PG) :
    tgt (l ++ t) (gs.map (PG.shift l.length)) = l ++ tgt t gs := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => simp [PG.act_shift, ih]

/-- The generators of `gs` lie on the first `n` strands. -/
def Fits (n : ℕ) (gs : List PG) : Prop := ∀ g ∈ gs, g.pos + g.width ≤ n

theorem PG.ld_append_right {t : List I} (r : List I) {g : PG} (hg : g.pos + g.width ≤ t.length) :
    g.ld (t ++ r) = (g.ld t).map (wh [] r) := by
  cases g with
  | dot p =>
    simp only [PG.pos, PG.width] at hg
    obtain ⟨x, hx⟩ : ∃ x, t.drop p = x :: t.drop (p + 1) :=
      ⟨t[p]'(by omega), List.drop_eq_getElem_cons _⟩
    have hx' : (t ++ r).drop p = x :: (t.drop (p + 1) ++ r) := by
      rw [List.drop_append_of_le_length (by omega), hx]; rfl
    simp only [PG.ld, hx, hx']
    simp [wh, List.take_append_of_le_length (show p ≤ t.length by omega)]
  | cross a =>
    simp only [PG.pos, PG.width] at hg
    obtain ⟨x, y, hx⟩ : ∃ x y, t.drop a = x :: y :: t.drop (a + 2) :=
      ⟨t[a]'(by omega), t[a + 1]'(by omega), by
        rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]⟩
    have hx' : (t ++ r).drop a = x :: y :: (t.drop (a + 2) ++ r) := by
      rw [List.drop_append_of_le_length (by omega), hx]; rfl
    simp only [PG.ld, hx, hx']
    simp [wh, List.take_append_of_le_length (show a ≤ t.length by omega)]

theorem PG.act_append_right {t : List I} (r : List I) {g : PG} (hg : g.pos + g.width ≤ t.length) :
    g.act (t ++ r) = g.act t ++ r := by
  cases g with
  | dot p => rfl
  | cross a =>
    simp only [PG.pos, PG.width] at hg
    obtain ⟨x, y, hx⟩ : ∃ x y, t.drop a = x :: y :: t.drop (a + 2) :=
      ⟨t[a]'(by omega), t[a + 1]'(by omega), by
        rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]⟩
    have hx' : (t ++ r).drop a = x :: y :: (t.drop (a + 2) ++ r) := by
      rw [List.drop_append_of_le_length (by omega), hx]; rfl
    simp only [PG.act, hx, hx']
    simp [List.take_append_of_le_length (show a ≤ t.length by omega)]

theorem pl_append_right {t : List I} (r : List I) {gs : List PG} (hgs : Fits t.length gs) :
    pl (t ++ r) gs = (pl t gs).map (wh [] r) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    have hg := hgs g (by simp)
    rw [pl_cons, pl_cons, PG.ld_append_right r hg, PG.act_append_right r hg,
      ih (fun g' hg' => by simpa using hgs g' (by simp [hg'])), List.map_append]

theorem tgt_append_right {t : List I} (r : List I) {gs : List PG} (hgs : Fits t.length gs) :
    tgt (t ++ r) gs = tgt t gs ++ r := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    have hg := hgs g (by simp)
    rw [tgt_cons, tgt_cons, PG.act_append_right r hg,
      ih (fun g' hg' => by simpa using hgs g' (by simp [hg']))]

variable {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w} [CommRing k]
  (Sc : SKM.Scalars D k)

theorem layList_wh (l r : List I) (ls : List (LayerData I)) :
    layList D (ls.map (wh l r)) = (layList D ls).map fun L => (L.wr r).wl (ob D l) := by
  simp [layList, lay, wh, Layer.wr, Layer.wl, ob]

/-- `f ⊗ 1_r` for a word `f` on the first strands. -/
theorem cl_whiskerRight {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') (r : List I)
    (hgs : Fits t.length gs) :
    cl D Sc t t' gs h ▷ (pres D Sc).obj (ob D r) =
      cl D Sc (t ++ r) (t' ++ r) gs (by
        rw [pl_append_right r hgs]; simpa using sChain_wh h [] r) := by
  rw [cl, Presentation.diag_whiskerRight, cl]
  apply Presentation.diag_eq_of_layers_eq
  simp [pl_append_right r hgs, layList, Layer.wr, lay, ob, wh]

/-- `1_l ⊗ g`: the word `g` shifted `|l|` strands to the right. -/
theorem cl_whiskerLeft (l : List I) {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    (pres D Sc).obj (ob D l) ◁ cl D Sc t t' gs h =
      cl D Sc (l ++ t) (l ++ t') (gs.map (PG.shift l.length)) (by
        rw [pl_shift]; simpa using sChain_wh h l []) := by
  rw [cl, Presentation.diag_whiskerLeft, cl]
  apply Presentation.diag_eq_of_layers_eq
  simp [pl_shift, layList, Layer.wl, lay, ob, wh]

/-! ## Moving dots below crossings -/

theorem cw_map_shift (n : ℕ) (σ : List ℕ) : (cw σ).map (PG.shift n) = cw (shiftWord n σ) := by
  simp [cw, shiftWord, List.map_reverse]

theorem dots_map_shift (n : ℕ) (l : List ℕ) :
    (l.map PG.dot).map (PG.shift n) = (l.map (n + ·)).map PG.dot := by
  simp

theorem fits_cw {n : ℕ} {σ : List ℕ} (hv : ValidWord n σ) : Fits n (cw σ) := by
  intro g hg
  simp only [cw, List.mem_map, List.mem_reverse] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  have := hv a ha
  simp [PG.pos, PG.width]; omega

theorem fits_dots {n : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < n) : Fits n (l.map PG.dot) := by
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  have := hl p hp
  simp [PG.pos, PG.width]; omega

theorem fits_append {n : ℕ} {gs hs : List PG} (h₁ : Fits n gs) (h₂ : Fits n hs) :
    Fits n (gs ++ hs) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  exacts [h₁ g hg, h₂ g hg]

/-- A word in the crossings `a ≥ ℓ` fixes the strands `p < ℓ`. -/
theorem extN_wordProd_of_lt {n ℓ : ℕ} {σ : List ℕ} (hv : ValidWord n σ) (hσ : ∀ a ∈ σ, ℓ ≤ a)
    {p : ℕ} (hp : p < ℓ) : Realization.extN n (wordProd n σ) p = p := by
  induction σ with
  | nil => simp
  | cons a σ ih =>
    have ha : a + 1 < n := hv a (by simp)
    have := hσ a (by simp)
    rw [wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      ih (fun x hx => hv x (by simp [hx])) (fun x hx => hσ x (by simp [hx])),
      Realization.extN_sadj ha]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

theorem extN_wordProd_inv_of_lt {n ℓ : ℕ} {σ : List ℕ} (hv : ValidWord n σ)
    (hσ : ∀ a ∈ σ, ℓ ≤ a) {p : ℕ} (hp : p < ℓ) :
    Realization.extN n (wordProd n σ)⁻¹ p = p := by
  rw [map_inv]
  conv_lhs => rw [← extN_wordProd_of_lt hv hσ hp]
  simp

variable {D Sc}

/-- A list of dots above the crossings of a word `σ` moves below them, to the strands
`w⁻¹(p)` for `w` the product of `σ`, up to a unit and fewer crossings. -/
theorem dots_down {t t' : List I} (P : List PG) {n : ℕ} (hn : t.length = n) (σ : List ℕ)
    (hv : ValidWord n σ) (L : List ℕ) (hL : ∀ p ∈ L, p < n) (R : List PG)
    (h : SChain t (pl t (P ++ cw σ ++ L.map PG.dot ++ R)) t') :
    ∃ h' : SChain t (pl t (P ++ (L.map (Realization.extN n (wordProd n σ)⁻¹)).map PG.dot ++
        cw σ ++ R)) t',
      Approx D Sc (crossCount P + σ.length + crossCount R) (cl D Sc t t' _ h)
        (cl D Sc t t' _ h') := by
  induction L generalizing P with
  | nil =>
    have e : P ++ cw σ ++ ([] : List ℕ).map PG.dot ++ R =
        P ++ (([] : List ℕ).map (Realization.extN n (wordProd n σ)⁻¹)).map PG.dot ++ cw σ ++ R := by
      simp
    exact ⟨e ▸ h, by rw [cl_eq_cl e h (e ▸ h)]; exact Approx.refl _ _⟩
  | cons p L ih =>
    have hp : p < n := hL p (by simp)
    have e₁ : P ++ cw σ ++ (p :: L).map PG.dot ++ R = P ++ cw σ ++ [PG.dot p] ++ (L.map PG.dot ++ R) := by
      simp
    obtain ⟨h₁, hA⟩ := dot_down (D := D) (Sc := Sc) P hn σ hv p hp _ (e₁ ▸ h)
    set q : ℕ := (((wordProd n σ)⁻¹ ⟨p, hp⟩ : Fin n) : ℕ)
    have hq : q = Realization.extN n (wordProd n σ)⁻¹ p := (Realization.extN_apply_lt _ hp).symm
    have e₂ : P ++ [PG.dot q] ++ cw σ ++ (L.map PG.dot ++ R) =
        (P ++ [PG.dot q]) ++ cw σ ++ L.map PG.dot ++ R := by simp
    obtain ⟨h₂, hB⟩ := ih (P ++ [PG.dot q]) (fun x hx => hL x (by simp [hx])) (e₂ ▸ h₁)
    have e₃ : P ++ [PG.dot q] ++ (L.map (Realization.extN n (wordProd n σ)⁻¹)).map PG.dot ++
        cw σ ++ R = P ++ ((p :: L).map (Realization.extN n (wordProd n σ)⁻¹)).map PG.dot ++
        cw σ ++ R := by
      simp [hq]
    refine ⟨e₃ ▸ h₂, ?_⟩
    rw [cl_eq_cl e₁ h (e₁ ▸ h), ← cl_eq_cl e₃ h₂ (e₃ ▸ h₂)]
    rw [cl_eq_cl e₂ h₁ (e₂ ▸ h₁)] at hA
    simp only [crossCount_append, crossCount_dots, crossCount_cons, crossCount_nil, PG.isCross,
      add_zero, zero_add] at hA hB ⊢
    exact hA.trans hB

variable (D Sc) in
/-- Words with fewer than `N` crossings lie in the span of the normal forms with `ℓ(w) < N`. -/
theorem low_le_span_nf (t t' : List I) (N : ℕ) :
    Low D Sc t t' N ≤
      Submodule.span k (basisNF D Sc t t' '' {i | length t.length i.1.2 < N}) := by
  rcases N with _ | j
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨gs, h, hc, rfl⟩
    exact absurd hc (Nat.not_lt_zero _)
  refine (low_le_filt D Sc j).trans ((filt_le_nf D Sc t j t').trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨l, hs, hl, w, hw, h, rfl⟩
  exact Submodule.subset_span ⟨⟨(l, w), hs, hl, h⟩, by simp; omega, by simp [NFIdx.nf]⟩

/-! ## Shuffles of words -/

section Shuffle

/-- A permutation of `Fin a` as a permutation of `Fin b`, for `a = b`. -/
def castPerm {a b : ℕ} (h : a = b) : Equiv.Perm (Fin a) ≃ Equiv.Perm (Fin b) :=
  Equiv.permCongr (finCongr h)

@[simp] theorem castPerm_rfl {a : ℕ} (w : Equiv.Perm (Fin a)) : castPerm rfl w = w := by
  ext; simp [castPerm]

theorem wordProd_canWord_castPerm {a b : ℕ} (h : a = b) (w : Equiv.Perm (Fin a)) :
    wordProd b (canWord a w) = castPerm h w := by
  subst h; simp

theorem isReduced_canWord_of_eq {a b : ℕ} (h : a = b) (w : Equiv.Perm (Fin a)) :
    IsReduced b (canWord a w) := by
  subst h; exact isReduced_canWord a w

theorem castPerm_injective {a b : ℕ} (h : a = b) : Function.Injective (castPerm h) :=
  (castPerm h).injective

theorem length_castPerm {a b : ℕ} (h : a = b) (w : Equiv.Perm (Fin a)) :
    length b (castPerm h w) = length a w := by
  subst h; simp

/-- The word at the top of `ψ_d`, the crossings of the canonical reduced word of `d`. -/
def shTop (t : List I) (d : Equiv.Perm (Fin t.length)) : List I := tgt t (cw (canWord t.length d))

/-- The first `m` letters of the word at the top of `ψ_d`. -/
def shL (t : List I) (m : ℕ) (d : Equiv.Perm (Fin t.length)) : List I := (shTop t d).take m

/-- The letters after the first `m` of the word at the top of `ψ_d`. -/
def shR (t : List I) (m : ℕ) (d : Equiv.Perm (Fin t.length)) : List I := (shTop t d).drop m

theorem shL_append_shR (t : List I) (m : ℕ) (d : Equiv.Perm (Fin t.length)) :
    shL t m d ++ shR t m d = shTop t d := List.take_append_drop _ _

theorem length_shL {t : List I} {m : ℕ} (hm : m ≤ t.length) (d : Equiv.Perm (Fin t.length)) :
    (shL t m d).length = m := by
  simp [shL, shTop]; omega

theorem length_shR (t : List I) (m : ℕ) (d : Equiv.Perm (Fin t.length)) :
    (shR t m d).length = t.length - m := by
  simp [shR, shTop]

/-- The word at the top of `ψ_{(a × b) d}`. -/
theorem tgt_parabolic {t : List I} {m : ℕ} (hm : m ≤ t.length) (d : Equiv.Perm (Fin t.length))
    {α β : List ℕ} (hα : ValidWord m α) :
    tgt t (cw (α ++ shiftWord m β ++ canWord t.length d)) =
      tgt (shL t m d) (cw α) ++ tgt (shR t m d) (cw β) := by
  rw [cw_append, cw_append, tgt_append, tgt_append]
  change tgt (tgt (shTop t d) _) _ = _
  have e : cw (shiftWord m β) = (cw β).map (PG.shift (shL t m d).length) := by
    rw [cw_map_shift, length_shL hm]
  rw [← shL_append_shR t m d, e, tgt_shift,
    tgt_append_right _ (fits_cw (by rw [length_shL hm]; exact hα))]

end Shuffle

/-! ## The shuffle basis index -/

section ShuffleIdx

variable {t u' v' : List I} (hN : u'.length + v'.length = t.length)

include hN in
theorem length_shL' (d : Equiv.Perm (Fin t.length)) : (shL t u'.length d).length = u'.length :=
  length_shL (by omega) d

include hN in
theorem length_shR' (d : Equiv.Perm (Fin t.length)) : (shR t u'.length d).length = v'.length := by
  rw [length_shR]; omega

/-- Indices of the shuffle basis of `Hom(t, u'v')`: a shuffle `d` (a minimal length
representative of a coset `(S_m × S_n) d`) and normal forms from the two halves of the top word
of `ψ_d` to `u'` and `v'`. -/
abbrev ShIdx := Σ d : Shuffle hN, NFIdx (shL t u'.length d.1) u' × NFIdx (shR t u'.length d.1) v'

variable {hN}

/-- The reduced word `ρ(a) (m + ρ(b)) ρ(d)` of `(a × b) d`. -/
def shWord (d : Shuffle hN) (a : Equiv.Perm (Fin (shL t u'.length d.1).length))
    (b : Equiv.Perm (Fin (shR t u'.length d.1).length)) : List ℕ :=
  canWord _ a ++ shiftWord u'.length (canWord _ b) ++ canWord t.length d.1

theorem shWord_spec (d : Shuffle hN) (a : Equiv.Perm (Fin (shL t u'.length d.1).length))
    (b : Equiv.Perm (Fin (shR t u'.length d.1).length)) :
    IsReduced t.length (shWord d a b) ∧ wordProd t.length (shWord d a b) =
      blockPerm hN (castPerm (length_shL' hN d.1) a) (castPerm (length_shR' hN d.1) b) * d.1 := by
  have h := IsReduced.parabolic hN (isReduced_canWord_of_eq (length_shL' hN d.1) a)
    (isReduced_canWord_of_eq (length_shR' hN d.1) b) (isReduced_canWord _ d.1)
    (by rw [wordProd_canWord]; exact d.2)
  refine ⟨h.1, ?_⟩
  rw [shWord, h.2, wordProd_canWord_castPerm, wordProd_canWord_castPerm, wordProd_canWord]

theorem tgt_shWord (d : Shuffle hN) (a : Equiv.Perm (Fin (shL t u'.length d.1).length))
    (b : Equiv.Perm (Fin (shR t u'.length d.1).length)) :
    tgt t (cw (shWord d a b)) = tgt (shL t u'.length d.1) (cw (canWord _ a)) ++
      tgt (shR t u'.length d.1) (cw (canWord _ b)) :=
  tgt_parabolic (by omega) d.1 (validWord_canWord _ _ |>.of_le (by rw [length_shL' hN]))

/-- The reduced word of an index. -/
def ShIdx.word (x : ShIdx hN) : List ℕ := shWord x.1 x.2.1.1.2 x.2.2.1.2

/-- The permutation `(a × b) d` of an index. -/
def ShIdx.perm (x : ShIdx hN) : Equiv.Perm (Fin t.length) :=
  blockPerm hN (castPerm (length_shL' hN x.1.1) x.2.1.1.2)
    (castPerm (length_shR' hN x.1.1) x.2.2.1.2) * x.1.1

theorem ShIdx.word_spec (x : ShIdx hN) :
    IsReduced t.length x.word ∧ wordProd t.length x.word = x.perm :=
  shWord_spec _ _ _

/-- The strands of the dots of an index, moved below `ψ_d`. -/
def ShIdx.dots (x : ShIdx hN) : List ℕ :=
  (x.2.2.1.1.map (u'.length + ·) ++ x.2.1.1.1).map (Realization.extN t.length x.1.1⁻¹)

theorem ShIdx.dots_lt (x : ShIdx hN) : ∀ p ∈ x.dots, p < t.length := by
  intro p hp
  simp only [ShIdx.dots, List.mem_map, List.mem_append] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hq' : q < t.length := by
    rcases hq with ⟨r, hr, rfl⟩ | hq
    · have := x.2.2.2.2.1 r hr
      rw [length_shR' hN] at this; omega
    · have := x.2.1.2.2.1 q hq
      rw [length_shL' hN] at this; omega
  rw [Realization.extN_apply_lt _ hq']
  exact Fin.is_lt _

theorem ShIdx.tgt_word (x : ShIdx hN) : tgt t (cw x.word) = u' ++ v' := by
  rw [ShIdx.word, tgt_shWord, NFIdx.tgt_cw, NFIdx.tgt_cw]

/-- The leading normal form `x^{d⁻¹(l)} ψ_{(a × b) d}` of a shuffle basis element. -/
def ShIdx.lead (x : ShIdx hN) : NFIdx t (u' ++ v') :=
  ⟨(x.dots.insertionSort (· ≤ ·), x.perm), List.pairwise_insertionSort _ _,
    fun p hp => x.dots_lt p ((List.mem_insertionSort _).mp hp), by
      have e : tgt t (List.map PG.dot (x.dots.insertionSort (· ≤ ·)) ++
          cw (canWord t.length x.perm)) = u' ++ v' := by
        rw [tgt_append, tgt_map_dot, ← x.tgt_word]
        exact tgt_cw_eq (validWord_canWord _ _) x.word_spec.1.1
          (by rw [wordProd_canWord, x.word_spec.2]) rfl
      exact e ▸ sChain_pl _ _⟩

theorem ShIdx.lead_val (x : ShIdx hN) : x.lead.1 = (x.dots.insertionSort (· ≤ ·), x.perm) := rfl

theorem ShIdx.lead_injective : Function.Injective (ShIdx.lead (hN := hN)) := by
  rintro ⟨⟨d, hd⟩, i, j⟩ ⟨⟨d', hd'⟩, i', j'⟩ he
  have he' := congrArg Subtype.val he
  rw [ShIdx.lead_val, ShIdx.lead_val, Prod.mk.injEq] at he'
  obtain ⟨hdots, hperm⟩ := he'
  obtain ⟨ha, hb, rfl⟩ := blockPerm_mul_injective hN hd hd' hperm
  have hw₁ := castPerm_injective _ ha
  have hw₂ := castPerm_injective _ hb
  set m := u'.length
  -- the dots, moved back up through `ψ_d`
  have hp : List.Perm (j.1.1.map (m + ·) ++ i.1.1) (j'.1.1.map (m + ·) ++ i'.1.1) := by
    have h₀ := List.perm_insertionSort (fun x1 x2 : ℕ => x1 ≤ x2) (ShIdx.dots ⟨⟨d, hd'⟩, (i', j')⟩)
    rw [← hdots] at h₀
    have h₁ := ((List.perm_insertionSort _ _).symm.trans h₀).map (Realization.extN t.length d)
    simp only [ShIdx.dots, List.map_map] at h₁
    have hid : Realization.extN t.length d ∘ Realization.extN t.length d⁻¹ = id := by
      ext p; simp [map_inv]
    rwa [hid, List.map_id, List.map_id] at h₁
  have hlt : ∀ (y : NFIdx (shL t m d) u'), ∀ p ∈ y.1.1, p < m := fun y p hp' => by
    have := y.2.2.1 p hp'; rwa [length_shL' hN] at this
  have hf₁ : ∀ (y : NFIdx (shL t m d) u') (z : NFIdx (shR t m d) v'),
      (z.1.1.map (m + ·) ++ y.1.1).filter (fun p => decide (p < m)) = y.1.1 := by
    intro y z
    rw [List.filter_append, List.filter_eq_nil_iff.mpr (by simp), List.filter_eq_self.mpr
      (fun p hp' => by simpa using hlt y p hp'), List.nil_append]
  have hf₂ : ∀ (y : NFIdx (shL t m d) u') (z : NFIdx (shR t m d) v'),
      ((z.1.1.map (m + ·) ++ y.1.1).filter (fun p => !decide (p < m))).map (· - m) = z.1.1 := by
    intro y z
    rw [List.filter_append, List.filter_eq_self.mpr (by simp),
      List.filter_eq_nil_iff.mpr (fun p hp' => by simpa using hlt y p hp'), List.append_nil,
      List.map_map]
    conv_rhs => rw [← List.map_id z.1.1]
    exact List.map_congr_left fun p _ => by simp
  have hi : i = i' := Subtype.ext (Prod.ext
    ((hf₁ i j ▸ hf₁ i' j' ▸ hp.filter _).eq_of_pairwise' i.2.1 i'.2.1) hw₁)
  have hj : j = j' := Subtype.ext (Prod.ext
    ((hf₂ i j ▸ hf₂ i' j' ▸ (hp.filter _).map _).eq_of_pairwise' j.2.1 j'.2.1) hw₂)
  subst hi hj
  rfl

theorem ShIdx.lead_surjective : Function.Surjective (ShIdx.lead (hN := hN)) := by
  rintro ⟨⟨l, w⟩, hs, hl, hc⟩
  obtain ⟨⟨a, b, d⟩, hw⟩ := (parabolicEquiv hN).surjective w
  simp only [parabolicEquiv_apply] at hw
  set a' := (castPerm (length_shL' hN d.1)).symm a
  set b' := (castPerm (length_shR' hN d.1)).symm b
  have hab : blockPerm hN (castPerm (length_shL' hN d.1) a') (castPerm (length_shR' hN d.1) b') *
      d.1 = w := by simpa [a', b'] using hw
  -- the tops of the two halves
  have htop : tgt (shL t u'.length d.1) (cw (canWord _ a')) ++
      tgt (shR t u'.length d.1) (cw (canWord _ b')) = u' ++ v' := by
    rw [← tgt_shWord, ← NFIdx.tgt_cw ⟨(l, w), hs, hl, hc⟩]
    refine tgt_cw_eq (shWord_spec d a' b').1.1 (validWord_canWord _ _) ?_ rfl
    rw [(shWord_spec d a' b').2, hab, wordProd_canWord]
  obtain ⟨hu, hv⟩ := List.append_inj htop (by rw [length_tgt, length_shL' hN])
  set L₀ := l.map (Realization.extN t.length d.1)
  set la := (L₀.filter fun p => decide (p < u'.length)).insertionSort (· ≤ ·)
  set lb := ((L₀.filter fun p => !decide (p < u'.length)).map (· - u'.length)).insertionSort
    (· ≤ ·)
  have hL₀ : ∀ p ∈ L₀, p < t.length := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [Realization.extN_apply_lt _ (hl q hq)]; exact Fin.is_lt _
  let i : NFIdx (shL t u'.length d.1) u' := ⟨(la, a'), List.pairwise_insertionSort _ _,
    fun p hp => by
      rw [length_shL' hN]
      simpa [la] using (List.mem_filter.mp ((List.mem_insertionSort _).mp hp)).2, by
      have e : tgt (shL t u'.length d.1) (la.map PG.dot ++ cw (canWord _ a')) = u' := by
        rw [tgt_append, tgt_map_dot, hu]
      have := sChain_pl (shL t u'.length d.1) (la.map PG.dot ++ cw (canWord _ a'))
      rwa [e] at this⟩
  let j : NFIdx (shR t u'.length d.1) v' := ⟨(lb, b'), List.pairwise_insertionSort _ _,
    fun p hp => by
      rw [length_shR]
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((List.mem_insertionSort _).mp hp)
      have h₁ := List.mem_filter.mp hq
      have := hL₀ q h₁.1
      simp at h₁; omega, by
      have e : tgt (shR t u'.length d.1) (lb.map PG.dot ++ cw (canWord _ b')) = v' := by
        rw [tgt_append, tgt_map_dot, hv]
      have := sChain_pl (shR t u'.length d.1) (lb.map PG.dot ++ cw (canWord _ b'))
      rwa [e] at this⟩
  refine ⟨⟨d, i, j⟩, Subtype.ext (Prod.ext ?_ hab)⟩
  -- the dots: both sides are sorted, and they agree up to order
  refine List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _) hs ?_
  refine (List.perm_insertionSort _ _).trans ?_
  have hp : List.Perm (lb.map (u'.length + ·) ++ la) L₀ := by
    refine List.Perm.trans ?_ (List.filter_append_perm (fun p => decide (p < u'.length)) L₀)
    refine List.perm_append_comm.trans (List.Perm.append (List.perm_insertionSort _ _) ?_)
    refine ((List.perm_insertionSort _ _).map _).trans ?_
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (L₀.filter _)]
    refine (List.map_congr_left fun p hp => ?_).subst (motive := fun x => List.Perm _ x)
      (List.Perm.refl _)
    have := (List.mem_filter.mp hp).2
    simp at this ⊢; omega
  have hid : Realization.extN t.length d.1⁻¹ ∘ Realization.extN t.length d.1 = id := by
    ext p; simp [map_inv]
  have := hp.map (Realization.extN t.length d.1⁻¹)
  rwa [List.map_map, hid, List.map_id] at this

end ShuffleIdx

/-! ## The shuffle elements -/

section ShuffleElt

variable {t u' v' : List I} {hN : u'.length + v'.length = t.length}

variable (D Sc) in
/-- `ψ_d : t → d(t)`, the crossings of the canonical reduced word of `d`, with the top word
split after `m` letters. -/
def shPsi (m : ℕ) (d : Equiv.Perm (Fin t.length)) :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D (shL t m d ++ shR t m d)) :=
  cl D Sc t _ (cw (canWord t.length d)) (by rw [shL_append_shR]; exact sChain_pl _ _)

variable (D Sc) in
/-- The shuffle basis element `(a ⊗ b) ψ_d` of an index: `ψ_d` followed by the tensor product
of the normal forms `a : d(t)' → u'` and `b : d(t)'' → v'`. -/
def shElt (x : ShIdx hN) : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D (u' ++ v')) :=
  shPsi D Sc u'.length x.1.1 ≫ ((pres D Sc).obj (ob D (shL t u'.length x.1.1)) ◁ x.2.2.nf) ≫
    (x.2.1.nf ▷ (pres D Sc).obj (ob D v'))

theorem nf_whiskerRight {a a' : List I} (i : NFIdx a a') (r : List I) :
    i.nf (D := D) (Sc := Sc) ▷ (pres D Sc).obj (ob D r) =
      cl D Sc (a ++ r) (a' ++ r) (i.1.1.map PG.dot ++ cw (canWord _ i.1.2)) (by
        rw [pl_append_right r (fits_append (fits_dots i.2.2.1) (fits_cw (validWord_canWord _ _)))]
        simpa using sChain_wh i.2.2.2 [] r) :=
  cl_whiskerRight D Sc _ _ r (fits_append (fits_dots i.2.2.1) (fits_cw (validWord_canWord _ _)))

theorem whiskerLeft_nf (l : List I) {b b' : List I} (j : NFIdx b b') :
    (pres D Sc).obj (ob D l) ◁ j.nf (D := D) (Sc := Sc) =
      cl D Sc (l ++ b) (l ++ b') ((j.1.1.map PG.dot ++ cw (canWord _ j.1.2)).map
        (PG.shift l.length)) (by rw [pl_shift]; simpa using sChain_wh j.2.2.2 l []) :=
  cl_whiskerLeft D Sc l _ _

/-- The generators of a shuffle basis element. -/
def ShIdx.gens (x : ShIdx hN) : List PG :=
  cw (canWord t.length x.1.1) ++ (x.2.2.1.1.map (u'.length + ·)).map PG.dot ++
    cw (shiftWord u'.length (canWord _ x.2.2.1.2)) ++ x.2.1.1.1.map PG.dot ++
    cw (canWord _ x.2.1.1.2)

theorem shElt_eq_cl (x : ShIdx hN) :
    ∃ h, shElt D Sc x = cl D Sc t (u' ++ v') x.gens h := by
  have e : cw (canWord t.length x.1.1) ++
      ((x.2.2.1.1.map PG.dot ++ cw (canWord _ x.2.2.1.2)).map
        (PG.shift (shL t u'.length x.1.1).length) ++
        (x.2.1.1.1.map PG.dot ++ cw (canWord _ x.2.1.1.2))) = x.gens := by
    simp only [ShIdx.gens, List.map_append, dots_map_shift, cw_map_shift,
      length_shL' hN, List.append_assoc]
  rw [shElt, nf_whiskerRight, whiskerLeft_nf, shPsi, cl_comp, cl_comp]
  generalize_proofs hG
  exact ⟨e ▸ hG, cl_eq_cl e hG _⟩

/-- **Leading term.** A shuffle basis element `(x^a ψ_{w₁} ⊗ x^b ψ_{w₂}) ψ_d` agrees, up to a unit
and words with fewer crossings, with the normal form `x^{d⁻¹(a, b)} ψ_{(w₁ × w₂) d}`. -/
theorem shElt_approx (x : ShIdx hN) :
    Approx D Sc (length t.length x.perm) (shElt D Sc x) x.lead.nf := by
  obtain ⟨h, he⟩ := shElt_eq_cl (D := D) (Sc := Sc) x
  rw [he]
  have hlen : x.word.length = length t.length x.perm := by
    have := x.word_spec.1.2; rwa [x.word_spec.2] at this
  have hwl : x.word.length = (canWord _ x.2.1.1.2).length + (canWord _ x.2.2.1.2).length +
      (canWord t.length x.1.1).length := by
    simp [ShIdx.word, shWord]; omega
  have hla : ∀ p ∈ x.2.1.1.1, p < u'.length := fun p hp => by
    have := x.2.1.2.2.1 p hp; rwa [length_shL' hN] at this
  have hlb : ∀ p ∈ x.2.2.1.1, p < v'.length := fun p hp => by
    have := x.2.2.2.2.1 p hp; rwa [length_shR' hN] at this
  -- move the dots of the first factor below the crossings of the second
  have hvA : ValidWord t.length (shiftWord u'.length (canWord _ x.2.2.1.2)) :=
    ValidWord.shiftWord hN ((validWord_canWord _ _).of_le (by rw [length_shR' hN]))
  obtain ⟨h₁, hA⟩ := dots_down (D := D) (Sc := Sc)
    (cw (canWord t.length x.1.1) ++ (x.2.2.1.1.map (u'.length + ·)).map PG.dot) rfl _ hvA
    x.2.1.1.1 (fun p hp => by have := hla p hp; omega) (cw (canWord _ x.2.1.1.2)) h
  have hf₂ : x.2.1.1.1.map (Realization.extN t.length
      (wordProd t.length (shiftWord u'.length (canWord _ x.2.2.1.2)))⁻¹) = x.2.1.1.1 := by
    conv_rhs => rw [← List.map_id x.2.1.1.1]
    refine List.map_congr_left fun p hp => extN_wordProd_inv_of_lt hvA ?_ (hla p hp)
    intro a ha
    simp only [shiftWord, List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    omega
  -- move all dots below `ψ_d`
  have e₂ : cw (canWord t.length x.1.1) ++ (x.2.2.1.1.map (u'.length + ·)).map PG.dot ++
      (x.2.1.1.1.map (Realization.extN t.length
        (wordProd t.length (shiftWord u'.length (canWord _ x.2.2.1.2)))⁻¹)).map PG.dot ++
      cw (shiftWord u'.length (canWord _ x.2.2.1.2)) ++ cw (canWord _ x.2.1.1.2) =
      [] ++ cw (canWord t.length x.1.1) ++
        (x.2.2.1.1.map (u'.length + ·) ++ x.2.1.1.1).map PG.dot ++
        (cw (shiftWord u'.length (canWord _ x.2.2.1.2)) ++ cw (canWord _ x.2.1.1.2)) := by
    rw [hf₂]; simp
  obtain ⟨h₂, hB⟩ := dots_down (D := D) (Sc := Sc) [] rfl _ (validWord_canWord _ x.1.1)
    (x.2.2.1.1.map (u'.length + ·) ++ x.2.1.1.1) (fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; have := hlb q hq; omega
      · have := hla p hp; omega) _ (e₂ ▸ h₁)
  -- sort the dots
  have e₃ : [] ++ ((x.2.2.1.1.map (u'.length + ·) ++ x.2.1.1.1).map
      (Realization.extN t.length (wordProd t.length (canWord t.length x.1.1))⁻¹)).map PG.dot ++
      cw (canWord t.length x.1.1) ++
      (cw (shiftWord u'.length (canWord _ x.2.2.1.2)) ++ cw (canWord _ x.2.1.1.2)) =
      [] ++ x.dots.map PG.dot ++ cw x.word := by
    simp [ShIdx.dots, ShIdx.word, shWord, cw_append]
  obtain ⟨c, hc, h₃, hC⟩ := dots_perm (D := D) (Sc := Sc) [] (cw x.word)
    (List.perm_insertionSort (· ≤ ·) x.dots).symm x.dots_lt (e₃ ▸ h₂)
  -- straighten the crossings
  have e₄ : [] ++ (x.dots.insertionSort (· ≤ ·)).map PG.dot ++ cw x.word =
      (x.dots.insertionSort (· ≤ ·)).map PG.dot ++ cw x.word := by simp
  have hb : BraidEquiv x.word (canWord t.length x.perm) :=
    braidEquiv_of_isReduced x.word_spec.1 (isReduced_canWord _ _)
      (by rw [x.word_spec.2, wordProd_canWord])
  have hD := braid_move (D := D) (Sc := Sc) ((x.dots.insertionSort (· ≤ ·)).map PG.dot) rfl hb
    x.word_spec.1.1 (e₄ ▸ h₃) x.lead.2.2.2
  rw [cl_eq_cl e₂ h₁ (e₂ ▸ h₁)] at hA
  rw [cl_eq_cl e₃ h₂ (e₃ ▸ h₂), hC] at hB
  rw [cl_eq_cl e₄ h₃ (e₄ ▸ h₃)] at hB
  simp only [crossCount_append, crossCount_dots, crossCount_cw, crossCount_nil, length_shiftWord,
    zero_add, add_zero] at hA hB hD
  refine (hA.mono (by omega)).trans ((hB.mono (by omega)).trans ?_)
  refine Approx.trans ⟨c, hc, by simp⟩ (hD.mono (by omega))

end ShuffleElt

/-! ## The shuffle basis -/

section ShuffleBasisSec

variable {t u' v' : List I} (hN : u'.length + v'.length = t.length)

/-- Shuffle basis indices correspond to normal forms through their leading terms. -/
def ShIdx.leadEquiv : ShIdx hN ≃ NFIdx t (u' ++ v') :=
  Equiv.ofBijective _ ⟨ShIdx.lead_injective, ShIdx.lead_surjective⟩

@[simp] theorem ShIdx.leadEquiv_apply (x : ShIdx hN) : ShIdx.leadEquiv hN x = x.lead := rfl

variable {hN}

theorem exists_unit_shElt (n : NFIdx t (u' ++ v')) :
    ∃ c : k, IsUnit c ∧ shElt D Sc ((ShIdx.leadEquiv hN).symm n) - c • basisNF D Sc t _ n ∈
      Submodule.span k (basisNF D Sc t (u' ++ v') ''
        {i | length t.length i.1.2 < length t.length n.1.2}) := by
  set x := (ShIdx.leadEquiv hN).symm n
  have hx : x.lead = n := (ShIdx.leadEquiv hN).apply_symm_apply n
  obtain ⟨c, hc, hmem⟩ := shElt_approx (D := D) (Sc := Sc) x
  refine ⟨c, hc, ?_⟩
  rw [basisNF_apply, ← hx]
  exact low_le_span_nf D Sc t _ _ hmem

variable (D Sc hN) in
/-- **Hill–Wang, arXiv:1202.2769v2, Proposition 6.4** (for the quiver Hecke superalgebras of
Brundan–Ellis, arXiv:1701.04133v2, §11), in the categorical form: for words `t`, `u'`, `v'` with
`|u'| + |v'| = |t|`, the elements `(a ⊗ b) ψ_d`, for `d` a minimal length representative of a
coset `(S_m × S_n) d` and `a`, `b` normal forms from the two halves of the top word of `ψ_d` to
`u'` and `v'`, form a basis of `Hom(t, u'v')`. -/
def shuffleBasis :
    Module.Basis (ShIdx hN) k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D (u' ++ v'))) :=
  (basisOfTriangular (basisNF D Sc t (u' ++ v')) (fun i => length t.length i.1.2)
    (b := fun n => shElt D Sc ((ShIdx.leadEquiv hN).symm n))
    (fun n => (exists_unit_shElt (D := D) (Sc := Sc) n).choose_spec.1)
    (fun n => (exists_unit_shElt (D := D) (Sc := Sc) n).choose_spec.2)).reindex
    (ShIdx.leadEquiv hN).symm

@[simp] theorem shuffleBasis_apply (x : ShIdx hN) : shuffleBasis D Sc hN x = shElt D Sc x := by
  simp only [shuffleBasis, Module.Basis.reindex_apply, Equiv.symm_symm, basisOfTriangular_apply]
  exact congrArg _ ((ShIdx.leadEquiv hN).symm_apply_apply x)

end ShuffleBasisSec

end OddMath.QuiverHecke
