/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Straighten
import Categorification.TypeA.Matsumoto

/-!
# Crossing words in `H`

For a word `σ` in the adjacent transpositions (`Categorification.TypeA`), `cw σ` is the
sequence of crossings representing `s_{σ₀} ⋯ s_{σ_{k-1}}`: the last letter is the bottom
crossing. On a word `t` of length `n` the top word is `t ∘ (wordProd n σ)⁻¹`
(`tgt_cw_getElem`), so braid-equivalent words have the same top word.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open SKM (zsign)
universe u v w
variable {I : Type u}

@[simp] theorem length_act (g : PG) (t : List I) : (g.act t).length = t.length := by
  cases g with
  | dot p => rfl
  | cross a =>
    simp only [PG.act]
    split
    · next x y r h =>
      have := congrArg List.length h
      simp only [List.length_drop, List.length_cons] at this
      simp; omega
    · rfl

@[simp] theorem length_tgt (t : List I) (gs : List PG) : (tgt t gs).length = t.length := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => simp [ih]

theorem act_cross_getElem {t : List I} {a : ℕ} (ha : a + 1 < t.length) (p : ℕ)
    (hp : p < ((PG.cross a).act t).length) :
    ((PG.cross a).act t)[p] = t[swapNat a p]'(by
      simp at hp; unfold swapNat; split_ifs <;> omega) := by
  obtain ⟨x, y, hx⟩ : ∃ x y, t.drop a = x :: y :: t.drop (a + 2) := by
    refine ⟨t[a], t[a + 1], ?_⟩
    rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]
  have hxa : t[a] = x := by
    have := List.getElem_of_eq hx (i := 0) (by simp; omega); simpa using this
  have hya : t[a + 1] = y := by
    have := List.getElem_of_eq hx (i := 1) (by simp; omega); simpa using this
  have hl : (t.take a).length = a := by simp; omega
  simp only [length_act] at hp
  have e : (PG.cross a).act t = t.take a ++ y :: x :: t.drop (a + 2) := by
    simp only [PG.act, hx]
  simp only [List.getElem_of_eq e]
  rcases swapNat_cases a p with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · subst h1
    simp only [h2, hya]
    rw [List.getElem_append_right (by omega)]
    simp [hl]
  · subst h1
    simp only [h2, hxa]
    rw [List.getElem_append_right (by omega)]
    simp [hl]
  · simp only [h3]
    by_cases hpa : p < a
    · rw [List.getElem_append_left (by omega)]; simp
    · rw [List.getElem_append_right (by omega)]
      have : p - (List.take a t).length = (p - a - 2) + 2 := by omega
      simp only [this, List.getElem_cons_succ, List.getElem_drop]
      congr 1; omega

/-- The crossings of a word in the adjacent transpositions, bottom first. -/
def cw (σ : List ℕ) : List PG := σ.reverse.map PG.cross

@[simp] theorem cw_nil : cw [] = [] := rfl
theorem cw_cons (a : ℕ) (σ : List ℕ) : cw (a :: σ) = cw σ ++ [PG.cross a] := by
  simp [cw]
theorem cw_append (σ τ : List ℕ) : cw (σ ++ τ) = cw τ ++ cw σ := by simp [cw]

@[simp] theorem crossCount_cw (σ : List ℕ) : crossCount (cw σ) = σ.length := by
  have : PG.isCross ∘ PG.cross = fun _ => 1 := rfl
  simp [cw, crossCount, this]

theorem tgt_cw_getElem {n : ℕ} {σ : List ℕ} (hv : ValidWord n σ) {t : List I}
    (ht : t.length = n) (q : Fin n) :
    (tgt t (cw σ))[(q : ℕ)]'(by simp [ht]) = t[((wordProd n σ)⁻¹ q : ℕ)]'(by simp [ht]) := by
  induction σ generalizing q with
  | nil => simp
  | cons a σ ih =>
    have ha : a + 1 < n := hv a (by simp)
    have e : tgt t (cw (a :: σ)) = (PG.cross a).act (tgt t (cw σ)) := by
      simp [cw_cons, tgt_append]
    simp only [List.getElem_of_eq e]
    rw [act_cross_getElem (by simp; omega)]
    have hq : swapNat a q < n := by unfold swapNat; split_ifs <;> omega
    have := ih (fun x hx => hv x (by simp [hx])) ⟨swapNat a q, hq⟩
    simp only at this
    rw [this]
    simp only [wordProd_cons, mul_inv_rev, sadj_inv, Equiv.Perm.mul_apply]
    congr 3
    ext; rw [sadj_val_of_lt ha]

/-- Words with the same product have the same top word. -/
theorem tgt_cw_eq {n : ℕ} {σ σ' : List ℕ} (hv : ValidWord n σ) (hv' : ValidWord n σ')
    (he : wordProd n σ = wordProd n σ') {t : List I} (ht : t.length = n) :
    tgt t (cw σ) = tgt t (cw σ') := by
  refine List.ext_getElem (by simp) fun p h₁ h₂ => ?_
  have hp : p < n := by simp at h₁; omega
  rw [tgt_cw_getElem hv ht ⟨p, hp⟩, tgt_cw_getElem hv' ht ⟨p, hp⟩, he]

/-! ## Agreement up to a unit and fewer crossings -/

variable {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- `x` agrees with a unit multiple of `y` up to words with fewer than `n` crossings. -/
def Approx {t t' : List I} (n : ℕ)
    (x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) : Prop :=
  ∃ c : k, IsUnit c ∧ x - c • y ∈ Low D Sc t t' n

variable {D Sc}

theorem Approx.refl {t t' : List I} (n : ℕ) (x : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    Approx D Sc n x x :=
  ⟨1, isUnit_one, by simp⟩

theorem Approx.symm {t t' : List I} {n : ℕ}
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')} (h : Approx D Sc n x y) :
    Approx D Sc n y x := by
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨u, rfl⟩ := hc
  refine ⟨↑u⁻¹, Units.isUnit _, ?_⟩
  have := Submodule.smul_mem _ (-(↑u⁻¹ : k)) h
  convert this using 1
  rw [smul_sub, smul_smul]
  simp [sub_eq_add_neg, add_comm]

theorem Approx.trans {t t' : List I} {n : ℕ}
    {x y z : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')} (h₁ : Approx D Sc n x y)
    (h₂ : Approx D Sc n y z) : Approx D Sc n x z := by
  obtain ⟨c, hc, h₁⟩ := h₁
  obtain ⟨d, hd, h₂⟩ := h₂
  refine ⟨c * d, hc.mul hd, ?_⟩
  have := Submodule.add_mem _ h₁ (Submodule.smul_mem _ c h₂)
  convert this using 1
  rw [smul_sub, smul_smul]; abel

theorem Approx.mono {t t' : List I} {m n : ℕ} (hmn : m ≤ n)
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')} (h : Approx D Sc m x y) :
    Approx D Sc n x y := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, low_mono D Sc hmn h⟩

theorem approx_of_filt {t t' : List I} {j n : ℕ} (hjn : j < n) (c : k) (hc : IsUnit c)
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (h : x - c • y ∈ Filt D Sc t t' j) : Approx D Sc n x y :=
  ⟨c, hc, filt_le_low D Sc hjn h⟩

theorem cl_eq_of_eq {t t' : List I} {gs hs : List PG} (e : gs = hs)
    (h : SChain t (pl t gs) t') : cl D Sc t t' gs h = cl D Sc t t' hs (e ▸ h) := by
  subst e; rfl

theorem sChain_of_tgt {t t' : List I} {gs hs : List PG} (h : SChain t (pl t gs) t')
    (e : tgt t gs = tgt t hs) : SChain t (pl t hs) t' := by
  have := sChain_pl t hs
  rwa [← e, tgt_eq h] at this

theorem sChain_of_braid {t t' : List I} (P : List PG) {n : ℕ} {σ σ' : List ℕ}
    (hb : BraidEquiv σ σ') (hv : ValidWord n σ) (hn : t.length = n)
    (h : SChain t (pl t (P ++ cw σ)) t') : SChain t (pl t (P ++ cw σ')) t' :=
  sChain_of_tgt h (by
    rw [tgt_append, tgt_append, tgt_cw_eq hv (hb.validWord_iff.mp hv) (hb.wordProd_eq hv)
      (by simp [hn])])

/-- One braid move, in context. -/
theorem approx_step {t t' : List I} (P : List PG) {n : ℕ} {σ σ' : List ℕ}
    (hs : BraidStep σ σ') (hv : ValidWord n σ) (hn : t.length = n)
    (h : SChain t (pl t (P ++ cw σ)) t') (h' : SChain t (pl t (P ++ cw σ')) t') :
    Approx D Sc (crossCount P + σ.length) (cl D Sc t t' (P ++ cw σ) h)
      (cl D Sc t t' (P ++ cw σ') h') := by
  cases hs with
  | comm α β hab =>
    rename_i a b
    have hb : b + 1 < n := hv b (by simp)
    set Q := P ++ cw β
    have e₁ : P ++ cw (α ++ [a, b] ++ β) = Q ++ [PG.cross b, PG.cross a] ++ cw α := by
      simp [Q, cw]
    have e₂ : P ++ cw (α ++ [b, a] ++ β) = Q ++ [PG.cross a, PG.cross b] ++ cw α := by
      simp [Q, cw]
    rw [cl_eq_of_eq e₁, cl_eq_of_eq e₂]
    set t₁ := tgt t Q
    have hl : t₁.length = n := by simp [t₁, hn]
    have hM : SChain t₁ (pl t₁ [PG.cross b, PG.cross a]) (tgt t₁ [PG.cross b, PG.cross a]) :=
      sChain_pl _ _
    have hM' : SChain t₁ (pl t₁ [PG.cross a, PG.cross b]) (tgt t₁ [PG.cross b, PG.cross a]) :=
      sChain_of_tgt (sChain_pl _ _) (by
        have := tgt_cw_eq (σ := [b, a]) (σ' := [a, b]) (n := n)
          (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> omega)
          (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> omega)
          (by simp [sadj_comm n (Or.inr hab)]) hl
        simpa [cw] using this.symm)
    have hR : SChain (tgt t₁ [PG.cross b, PG.cross a])
        (pl (tgt t₁ [PG.cross b, PG.cross a]) (cw α)) t' := by
      have key : tgt t (Q ++ [PG.cross b, PG.cross a] ++ cw α) = t' := by
        rw [← e₁]; exact tgt_eq h
      have : tgt (tgt t₁ [PG.cross b, PG.cross a]) (cw α) = t' := by
        rw [← key]; simp only [t₁, tgt_append]
      exact this ▸ sChain_pl _ _
    obtain ⟨c, hc, hsw⟩ := far_swap D Sc (t₁ := t₁) (PG.cross a) (PG.cross b)
      (by simp [PG.pos, PG.width]; omega) (by simp [PG.pos, PG.width]; omega) hM' hM
    have hmove : cl D Sc t₁ _ [PG.cross b, PG.cross a] hM -
        c • cl D Sc t₁ _ [PG.cross a, PG.cross b] hM' ∈ Filt D Sc t₁ _ 0 := by
      rw [hsw, smul_smul, hc, one_smul, sub_self]; exact Submodule.zero_mem _
    refine approx_of_filt ?_ c (Units.mk c c hc hc).isUnit
      (move_ctx D Sc Q _ _ (cw α) c (sChain_pl t Q) hR hM hM' hmove _ _)
    simp [Q]; omega
  | braid α β a =>
    have ha : a + 1 + 1 < n := hv (a + 1) (by simp)
    set Q := P ++ cw β
    have e₁ : P ++ cw (α ++ [a, a + 1, a] ++ β) =
        Q ++ [PG.cross a, PG.cross (a + 1), PG.cross a] ++ cw α := by
      simp [Q, cw]
    have e₂ : P ++ cw (α ++ [a + 1, a, a + 1] ++ β) =
        Q ++ [PG.cross (a + 1), PG.cross a, PG.cross (a + 1)] ++ cw α := by
      simp [Q, cw]
    rw [cl_eq_of_eq e₁, cl_eq_of_eq e₂]
    set t₁ := tgt t Q
    have hl : t₁.length = n := by simp [t₁, hn]
    set M := [PG.cross a, PG.cross (a + 1), PG.cross a]
    set M' := [PG.cross (a + 1), PG.cross a, PG.cross (a + 1)]
    have hM : SChain t₁ (pl t₁ M) (tgt t₁ M) := sChain_pl _ _
    have hM' : SChain t₁ (pl t₁ M') (tgt t₁ M) :=
      sChain_of_tgt (sChain_pl _ _) (by
        have := tgt_cw_eq (σ := [a + 1, a, a + 1]) (σ' := [a, a + 1, a]) (n := n)
          (by intro x hx; simp at hx; omega) (by intro x hx; simp at hx; omega)
          (by simp only [wordProd_cons, wordProd_nil, mul_one, ← mul_assoc]
              exact (sadj_braid (by omega)).symm) hl
        simpa [cw, M, M'] using this.symm)
    have hR : SChain (tgt t₁ M) (pl (tgt t₁ M) (cw α)) t' := by
      have key : tgt t (Q ++ M ++ cw α) = t' := by
        rw [← e₁]; exact tgt_eq h
      have : tgt (tgt t₁ M) (cw α) = t' := by
        rw [← key]; simp only [t₁, tgt_append]
      exact this ▸ sChain_pl _ _
    have hmove := braid_at D Sc (t₁ := t₁) (a := a) (by omega) hM hM'
    rw [← one_smul k (cl D Sc t₁ _ M' hM')] at hmove
    refine approx_of_filt ?_ 1 isUnit_one
      (move_ctx D Sc Q M M' (cw α) 1 (sChain_pl t Q) hR hM hM' hmove _ _)
    simp [Q]; omega

/-- Braid-equivalent words of crossings agree up to a unit and words with fewer crossings. -/
theorem braid_move {t t' : List I} (P : List PG) {n : ℕ} (hn : t.length = n) {σ σ' : List ℕ}
    (hb : BraidEquiv σ σ') (hv : ValidWord n σ)
    (h : SChain t (pl t (P ++ cw σ)) t') (h' : SChain t (pl t (P ++ cw σ')) t') :
    Approx D Sc (crossCount P + σ.length) (cl D Sc t t' (P ++ cw σ) h)
      (cl D Sc t t' (P ++ cw σ') h') := by
  induction hb with
  | rel σ σ' hs => exact approx_step P hs hv hn h h'
  | refl => exact Approx.refl _ _
  | symm σ σ' hb ih =>
    have hv' : ValidWord n σ := (BraidEquiv.validWord_iff hb).mpr hv
    have := (ih hv' h' h).symm
    rwa [BraidEquiv.length_eq hb] at this
  | trans σ σ'' σ' hb₁ hb₂ ih₁ ih₂ =>
    have hv'' : ValidWord n σ'' := (BraidEquiv.validWord_iff hb₁).mp hv
    have h'' := sChain_of_braid P hb₁ hv hn h
    have := ih₂ hv'' h'' h'
    rw [← BraidEquiv.length_eq hb₁] at this
    exact (ih₁ hv h h'').trans this

/-! ## Moving dots down -/

theorem tgt_dot_cross (t : List I) (p a : ℕ) :
    tgt t [PG.dot p, PG.cross a] = tgt t [PG.cross a, PG.dot p] := rfl

theorem tgt_dot_cross' (t : List I) (p q a : ℕ) :
    tgt t [PG.dot p, PG.cross a] = tgt t [PG.dot q, PG.cross a] := rfl

/-- A dot directly above a crossing `a` moves below it, to the strand `s_a(p)`. -/
theorem cross_dot_move {t₁ t₂ : List I} {a p : ℕ} (ha : a + 1 < t₁.length) (hp : p < t₁.length)
    (h₁ : SChain t₁ (pl t₁ [PG.cross a, PG.dot p]) t₂) :
    ∃ c : k, IsUnit c ∧ ∃ h₂ : SChain t₁ (pl t₁ [PG.dot (swapNat a p), PG.cross a]) t₂,
      cl D Sc t₁ t₂ [PG.cross a, PG.dot p] h₁ -
        c • cl D Sc t₁ t₂ [PG.dot (swapNat a p), PG.cross a] h₂ ∈ Filt D Sc t₁ t₂ 0 := by
  have hs : ∀ q, SChain t₁ (pl t₁ [PG.dot q, PG.cross a]) t₂ := fun q =>
    sChain_of_tgt h₁ (tgt_dot_cross t₁ q a).symm
  by_cases hpa : p = a
  · subst hpa
    obtain ⟨c, hc, hm⟩ := slide_right_at D Sc ha h₁ (hs (p + 1))
    rw [show swapNat p p = p + 1 by simp [swapNat]]
    exact ⟨c, (Units.mk c c hc hc).isUnit, hs _, hm⟩
  by_cases hpa' : p = a + 1
  · subst hpa'
    obtain ⟨c, hc, hm⟩ := slide_left_at D Sc ha (hs a) h₁
    rw [show swapNat a (a + 1) = a by simp [swapNat]]
    refine ⟨c, (Units.mk c c hc hc).isUnit, hs _, ?_⟩
    have := Submodule.smul_mem _ (-c) hm
    convert this using 1
    rw [smul_sub, smul_smul, neg_mul, hc]
    simp [sub_eq_add_neg, add_comm]
  have hsw : swapNat a p = p := by simp [swapNat, hpa, hpa']
  rw [hsw]
  by_cases hlt : p < a
  · obtain ⟨c, hc, hsw⟩ := far_swap D Sc (PG.dot p) (PG.cross a)
      (by simp [PG.pos, PG.width]; omega) (by simp [PG.pos, PG.width]; omega) (hs p) h₁
    refine ⟨c, (Units.mk c c hc hc).isUnit, hs _, ?_⟩
    rw [hsw, smul_smul, hc, one_smul, sub_self]; exact Submodule.zero_mem _
  · obtain ⟨c, hc, hsw⟩ := far_swap D Sc (PG.cross a) (PG.dot p)
      (by simp [PG.pos, PG.width]; omega) (by simp [PG.pos, PG.width]; omega) h₁ (hs p)
    refine ⟨c, (Units.mk c c hc hc).isUnit, hs _, ?_⟩
    rw [hsw, sub_self]; exact Submodule.zero_mem _

/-- A local move in context, as agreement up to a unit and fewer crossings. -/
theorem approx_ctx {t t' : List I} (Q M M' R : List PG) (c : k) (hc : IsUnit c) {j : ℕ}
    (h : SChain t (pl t (Q ++ M ++ R)) t')
    (hM : SChain (tgt t Q) (pl (tgt t Q) M) (tgt (tgt t Q) M))
    (hM' : SChain (tgt t Q) (pl (tgt t Q) M') (tgt (tgt t Q) M))
    (hmove : cl D Sc _ _ M hM - c • cl D Sc _ _ M' hM' ∈ Filt D Sc _ _ j) {N : ℕ}
    (hN : crossCount Q + j + crossCount R < N) :
    ∃ h' : SChain t (pl t (Q ++ M' ++ R)) t',
      Approx D Sc N (cl D Sc t t' (Q ++ M ++ R) h) (cl D Sc t t' (Q ++ M' ++ R) h') := by
  have hR : SChain (tgt (tgt t Q) M) (pl (tgt (tgt t Q) M) R) t' := by
    have : tgt (tgt (tgt t Q) M) R = t' := by rw [← tgt_append, ← tgt_append]; exact tgt_eq (by simpa only [List.append_assoc] using h)
    exact this ▸ sChain_pl _ _
  have h' : SChain t (pl t (Q ++ M' ++ R)) t' :=
    sChain_append_of (sChain_append_of (sChain_pl t Q) hM') hR
  exact ⟨h', approx_of_filt hN c hc
    (move_ctx D Sc Q M M' R c (sChain_pl t Q) hR hM hM' hmove h h')⟩

theorem cl_eq_cl {t t' : List I} {gs hs : List PG} (e : gs = hs) (h : SChain t (pl t gs) t')
    (h' : SChain t (pl t hs) t') : cl D Sc t t' gs h = cl D Sc t t' hs h' := by
  subst e; rfl

/-- A dot on strand `p` above the crossings of a word `σ` moves below them, to the strand
`w⁻¹(p)` for `w` the product of `σ`, up to a unit and fewer crossings. -/
theorem dot_down {t t' : List I} (P : List PG) {n : ℕ} (hn : t.length = n) (σ : List ℕ)
    (hv : ValidWord n σ) (p : ℕ) (hp : p < n) (R : List PG)
    (h : SChain t (pl t (P ++ cw σ ++ [PG.dot p] ++ R)) t') :
    ∃ h' : SChain t (pl t (P ++ [PG.dot ((wordProd n σ)⁻¹ ⟨p, hp⟩)] ++ cw σ ++ R)) t',
      Approx D Sc (crossCount P + σ.length + crossCount R) (cl D Sc t t' _ h)
        (cl D Sc t t' _ h') := by
  induction σ generalizing p R with
  | nil =>
    have e : P ++ cw [] ++ [PG.dot p] ++ R =
        P ++ [PG.dot ((wordProd n [])⁻¹ ⟨p, hp⟩)] ++ cw [] ++ R := by simp
    exact ⟨e ▸ h, by rw [cl_eq_cl e h (e ▸ h)]; exact Approx.refl _ _⟩
  | cons a σ ih =>
    have ha : a + 1 < n := hv a (by simp)
    set Q := P ++ cw σ
    have e₁ : P ++ cw (a :: σ) ++ [PG.dot p] ++ R = Q ++ [PG.cross a, PG.dot p] ++ R := by
      simp [Q, cw_cons]
    have hl : (tgt t Q).length = n := by simp [hn]
    have hM : SChain (tgt t Q) (pl (tgt t Q) [PG.cross a, PG.dot p])
        (tgt (tgt t Q) [PG.cross a, PG.dot p]) := sChain_pl _ _
    obtain ⟨c, hc, h₂, hm⟩ :=
      cross_dot_move (D := D) (Sc := Sc) (by omega) (by omega) hM
    obtain ⟨h₃, hA⟩ := approx_ctx Q _ _ R c hc (e₁ ▸ h) hM h₂ hm
      (N := crossCount P + (a :: σ).length + crossCount R) (by simp [Q])
    have hp' : swapNat a p < n := by unfold swapNat; split_ifs <;> omega
    have e₂ : Q ++ [PG.dot (swapNat a p), PG.cross a] ++ R =
        P ++ cw σ ++ [PG.dot (swapNat a p)] ++ ([PG.cross a] ++ R) := by
      simp [Q]
    obtain ⟨h₄, hB⟩ :=
      ih (fun x hx => hv x (by simp [hx])) (swapNat a p) hp' ([PG.cross a] ++ R) (e₂ ▸ h₃)
    have hq : (((wordProd n σ)⁻¹ ⟨swapNat a p, hp'⟩ : Fin n) : ℕ) =
        (((wordProd n (a :: σ))⁻¹ ⟨p, hp⟩ : Fin n) : ℕ) := by
      rw [wordProd_cons, mul_inv_rev, sadj_inv, Equiv.Perm.mul_apply]
      congr 2
      ext; rw [sadj_val_of_lt ha]
    have e₃ : P ++ [PG.dot ((wordProd n σ)⁻¹ ⟨swapNat a p, hp'⟩)] ++ cw σ ++ ([PG.cross a] ++ R) =
        P ++ [PG.dot ((wordProd n (a :: σ))⁻¹ ⟨p, hp⟩)] ++ cw (a :: σ) ++ R := by
      rw [← hq]; simp [cw_cons]
    refine ⟨e₃ ▸ h₄, ?_⟩
    rw [cl_eq_cl e₁ h (e₁ ▸ h), ← cl_eq_cl e₃ h₄ (e₃ ▸ h₄)]
    rw [cl_eq_cl e₂ h₃ (e₂ ▸ h₃)] at hA
    exact hA.trans (Approx.mono (by simp [PG.isCross]; omega) hB)

/-- An exact local move in context. -/
theorem eq_ctx {t t₁ t₂ t' : List I} (Q M M' R : List PG) (c : k)
    (hQ : SChain t (pl t Q) t₁) (hR : SChain t₂ (pl t₂ R) t')
    (hM : SChain t₁ (pl t₁ M) t₂) (hM' : SChain t₁ (pl t₁ M') t₂)
    (hmove : cl D Sc t₁ t₂ M hM = c • cl D Sc t₁ t₂ M' hM')
    (h : SChain t (pl t (Q ++ M ++ R)) t') (h' : SChain t (pl t (Q ++ M' ++ R)) t') :
    cl D Sc t t' (Q ++ M ++ R) h = c • cl D Sc t t' (Q ++ M' ++ R) h' := by
  have e₁ : cl D Sc t t' (Q ++ M ++ R) h =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M hM ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  have e₂ : cl D Sc t t' (Q ++ M' ++ R) h' =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M' hM' ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  rw [e₁, e₂, hmove, Linear.smul_comp, Linear.comp_smul]

/-- Dots on distinct strands commute up to a unit; so a list of dots may be permuted. -/
theorem dots_perm {t t' : List I} (P R : List PG) {l l' : List ℕ} (hp : l.Perm l')
    (hl : ∀ x ∈ l, x < t.length) (h : SChain t (pl t (P ++ l.map PG.dot ++ R)) t') :
    ∃ c : k, IsUnit c ∧ ∃ h' : SChain t (pl t (P ++ l'.map PG.dot ++ R)) t',
      cl D Sc t t' _ h = c • cl D Sc t t' _ h' := by
  induction hp generalizing P with
  | nil => exact ⟨1, isUnit_one, h, by simp⟩
  | cons x hp ih =>
    rename_i l₁ l₂
    have e₁ : P ++ (x :: l₁).map PG.dot ++ R = (P ++ [PG.dot x]) ++ l₁.map PG.dot ++ R := by simp
    have e₂ : P ++ (x :: l₂).map PG.dot ++ R = (P ++ [PG.dot x]) ++ l₂.map PG.dot ++ R := by simp
    obtain ⟨c, hc, h', he⟩ := ih (P ++ [PG.dot x]) (fun y hy => hl y (by simp [hy])) (e₁ ▸ h)
    refine ⟨c, hc, e₂ ▸ h', ?_⟩
    rw [cl_eq_cl e₁ h (e₁ ▸ h), he, cl_eq_cl e₂ (e₂ ▸ h') h']
  | swap x y l₁ =>
    have hx : x < t.length := hl x (by simp)
    have hy : y < t.length := hl y (by simp)
    have e₁ : P ++ (y :: x :: l₁).map PG.dot ++ R =
        P ++ [PG.dot y, PG.dot x] ++ (l₁.map PG.dot ++ R) := by simp
    have e₂ : P ++ (x :: y :: l₁).map PG.dot ++ R =
        P ++ [PG.dot x, PG.dot y] ++ (l₁.map PG.dot ++ R) := by simp
    set u := tgt t P
    have hu : u.length = t.length := by simp [u]
    have hM : SChain u (pl u [PG.dot y, PG.dot x]) u := by
      simpa [u, PG.act] using sChain_pl u [PG.dot y, PG.dot x]
    have hM' : SChain u (pl u [PG.dot x, PG.dot y]) u := by
      simpa [u, PG.act] using sChain_pl u [PG.dot x, PG.dot y]
    have hR : SChain u (pl u (l₁.map PG.dot ++ R)) t' := by
      have : tgt u (l₁.map PG.dot ++ R) = t' := by
        have := tgt_eq h
        simp only [tgt_append] at this ⊢
        simpa [u, PG.act] using this
      exact this ▸ sChain_pl _ _
    have h' : SChain t (pl t (P ++ (x :: y :: l₁).map PG.dot ++ R)) t' :=
      e₂ ▸ sChain_append_of (sChain_append_of (sChain_pl t P) hM') hR
    obtain ⟨c, hc, hmove⟩ : ∃ c : k, IsUnit c ∧
        cl D Sc u u [PG.dot y, PG.dot x] hM = c • cl D Sc u u [PG.dot x, PG.dot y] hM' := by
      rcases lt_trichotomy x y with hxy | rfl | hxy
      · obtain ⟨c, hc, hsw⟩ := far_swap D Sc (PG.dot x) (PG.dot y)
          (by simp [PG.pos, PG.width]; omega) (by simp [PG.pos, PG.width]; omega) hM' hM
        refine ⟨c, (Units.mk c c hc hc).isUnit, ?_⟩
        rw [hsw, smul_smul, hc, one_smul]
      · exact ⟨1, isUnit_one, by simp⟩
      · obtain ⟨c, hc, hsw⟩ := far_swap D Sc (PG.dot y) (PG.dot x)
          (by simp [PG.pos, PG.width]; omega) (by simp [PG.pos, PG.width]; omega) hM hM'
        exact ⟨c, (Units.mk c c hc hc).isUnit, hsw⟩
    refine ⟨c, hc, h', ?_⟩
    rw [cl_eq_cl e₁ h (e₁ ▸ h), cl_eq_cl e₂ h' (e₂ ▸ h')]
    exact eq_ctx P _ _ _ c (sChain_pl t P) hR hM hM' hmove _ _
  | trans h₁₂ h₂₃ ih₁ ih₂ =>
    obtain ⟨c, hc, h', he⟩ := ih₁ P hl h
    obtain ⟨d, hd, h'', he'⟩ := ih₂ P (fun y hy => hl y ((h₁₂.mem_iff).mpr hy)) h'
    exact ⟨c * d, hc.mul hd, h'', by rw [he, he', smul_smul]⟩

/-- If `x` agrees with `y` up to a unit and words with fewer than `N` crossings, which lie in
`M`, then `y ∈ M` gives `x ∈ M`. -/
theorem Approx.mem {t t' : List I} {N : ℕ}
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')} (h : Approx D Sc N x y)
    {M : Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))}
    (hM : Low D Sc t t' N ≤ M) (hy : y ∈ M) : x ∈ M := by
  obtain ⟨c, -, h⟩ := h
  have := M.add_mem (hM h) (M.smul_mem c hy)
  simpa using this

theorem length_of_sChain {t t' : List I} {gs : List PG} (h : SChain t (pl t gs) t') :
    t'.length = t.length := by
  rw [← tgt_eq h]; simp

theorem sChain_suffix {t t' : List I} {Q M R : List PG} (h : SChain t (pl t (Q ++ M ++ R)) t') :
    SChain (tgt (tgt t Q) M) (pl (tgt (tgt t Q) M) R) t' := by
  have : tgt (tgt (tgt t Q) M) R = t' := by
    rw [← tgt_append, ← tgt_append]; exact tgt_eq (by simpa only [List.append_assoc] using h)
  exact this ▸ sChain_pl _ _

@[simp] theorem crossCount_dots (l : List ℕ) : crossCount (l.map PG.dot) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [PG.isCross] using ih

/-- A generator which does not fit on the word is dropped. -/
theorem ld_eq_nil {g : PG} {t : List I} (hg : t.length < g.pos + g.width) : g.ld t = [] := by
  cases g with
  | dot p =>
    simp only [PG.ld]
    split
    · next x r hd =>
      have := congrArg List.length hd
      simp [PG.pos, PG.width] at this hg; omega
    · rfl
  | cross a =>
    simp only [PG.ld]
    split
    · next x y r hd =>
      have := congrArg List.length hd
      simp [PG.pos, PG.width] at this hg; omega
    · rfl

/-- A word of crossings with two equal adjacent letters has, modulo (1.7), fewer crossings. -/
theorem cl_mem_filt_of_hasRepeat {t t' : List I} (P R : List PG) {n : ℕ} (hn : t.length = n)
    {σ : List ℕ} (hv : ValidWord n σ) (hr : HasRepeat σ)
    (h : SChain t (pl t (P ++ cw σ ++ R)) t') :
    cl D Sc t t' _ h ∈ Filt D Sc t t' (crossCount P + (σ.length - 2) + crossCount R) := by
  obtain ⟨α, β, b, rfl⟩ := hr
  have hb : b + 1 < n := hv b (by simp)
  have e : P ++ cw (α ++ [b, b] ++ β) ++ R =
      (P ++ cw β) ++ [PG.cross b, PG.cross b] ++ (cw α ++ R) := by simp [cw]
  rw [cl_eq_cl e h (e ▸ h)]
  set Q := P ++ cw β
  have hM : SChain (tgt t Q) (pl (tgt t Q) [PG.cross b, PG.cross b])
      (tgt (tgt t Q) [PG.cross b, PG.cross b]) := sChain_pl _ _
  have hR := sChain_suffix (e ▸ h)
  have key : cl D Sc t t' (Q ++ [PG.cross b, PG.cross b] ++ (cw α ++ R)) (e ▸ h) =
      cl D Sc t _ Q (sChain_pl t Q) ≫ cl D Sc _ _ _ hM ≫ cl D Sc _ t' _ hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  rw [key]
  refine filt_mono D Sc ?_ (comp_filt_comp D Sc Q _ _ hR
    (cross_cross_at D Sc (by simp [hn]; omega) hM))
  simp [Q]; omega

/-! ## The spanning theorem -/

variable (D Sc) in
/-- The span of the normal forms `x^u ψ_w` (dots on the strands `l`, in increasing order, below
the crossings of the canonical reduced word of `w`) with `ℓ(w) ≤ m`. -/
def NF (t t' : List I) (m : ℕ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
    ∃ w : Equiv.Perm (Fin t.length), length t.length w ≤ m ∧
      ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (canWord t.length w)) h = f}

theorem nf_mono {t t' : List I} {m m' : ℕ} (hm : m ≤ m') : NF D Sc t t' m ≤ NF D Sc t t' m' :=
  Submodule.span_mono fun _ ⟨l, hs, hl, w, hw, h, e⟩ => ⟨l, hs, hl, w, hw.trans hm, h, e⟩

theorem span_comp_mem {t t₀ t' : List I}
    {S : Set ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t₀))}
    {M : Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))}
    (g : (pres D Sc).obj (ob D t₀) ⟶ (pres D Sc).obj (ob D t')) (hS : ∀ s ∈ S, s ≫ g ∈ M)
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t₀)} (hf : f ∈ Submodule.span k S) :
    f ≫ g ∈ M := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact M.add_mem hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact M.smul_mem a hx

/-- Normal forms followed by a dot. -/
theorem nf_comp_dot {t t₀ t' : List I} {m : ℕ} (hlow : Low D Sc t t' m ≤ NF D Sc t t' m)
    {p : ℕ} (hp : p < t₀.length) (hg : SChain t₀ (pl t₀ [PG.dot p]) t')
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t₀)} (hf : f ∈ NF D Sc t t₀ m) :
    f ≫ cl D Sc t₀ t' [PG.dot p] hg ∈ NF D Sc t t' m := by
  obtain rfl : t₀ = t' := tgt_eq hg
  refine span_comp_mem _ (fun s hs => ?_) hf
  obtain ⟨l, hs, hl, w, hw, h, rfl⟩ := hs
  rw [cl_comp]
  set σ := canWord t.length w
  have hp' : p < t.length := by rw [← length_of_sChain h]; exact hp
  have e : l.map PG.dot ++ cw σ ++ [PG.dot p] = l.map PG.dot ++ cw σ ++ [PG.dot p] ++ [] := by
    simp
  rw [cl_eq_cl e _ (e ▸ sChain_append_of h hg)]
  obtain ⟨h', hA⟩ := dot_down (D := D) (Sc := Sc) (l.map PG.dot) rfl σ
    (validWord_canWord t.length w) p hp' [] (e ▸ sChain_append_of h hg)
  set q : ℕ := (((wordProd t.length σ)⁻¹ ⟨p, hp'⟩ : Fin t.length) : ℕ)
  have hq : q < t.length := Fin.is_lt _
  have e' : l.map PG.dot ++ [PG.dot q] ++ cw σ ++ [] = [] ++ (l ++ [q]).map PG.dot ++ cw σ := by
    simp
  have hl' : ∀ x ∈ l ++ [q], x < t.length := by
    intro x hx; simp at hx; rcases hx with hx | rfl; exacts [hl x hx, hq]
  obtain ⟨c, hc, h'', he⟩ := dots_perm (D := D) (Sc := Sc) [] (cw σ)
    ((List.perm_append_singleton q l).trans (List.perm_orderedInsert (· ≤ ·) q l).symm) hl'
    (e' ▸ h')
  rw [cl_eq_cl e' h' (e' ▸ h'), he] at hA
  refine hA.mem ((low_mono D Sc (by simp [σ, length_canWord]; omega)).trans hlow)
    (Submodule.smul_mem _ c (Submodule.subset_span ?_))
  refine ⟨_, hs.orderedInsert q l, fun x hx => ?_, w, hw, by simpa using h'', rfl⟩
  rcases (List.mem_orderedInsert (· ≤ ·)).mp hx with rfl | hx
  exacts [hq, hl x hx]

/-- Normal forms followed by a crossing. -/
theorem nf_comp_cross {t t₀ t' : List I} {m : ℕ}
    (hlow : Low D Sc t t' (m + 1) ≤ NF D Sc t t' (m + 1))
    {a : ℕ} (ha : a + 1 < t₀.length) (hg : SChain t₀ (pl t₀ [PG.cross a]) t')
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t₀)} (hf : f ∈ NF D Sc t t₀ m) :
    f ≫ cl D Sc t₀ t' [PG.cross a] hg ∈ NF D Sc t t' (m + 1) := by
  refine span_comp_mem _ (fun s hs => ?_) hf
  obtain ⟨l, hs, hl, w, hw, h, rfl⟩ := hs
  rw [cl_comp]
  set σ := canWord t.length w
  have ha' : a + 1 < t.length := by rw [← length_of_sChain h]; exact ha
  have hv : ValidWord t.length (a :: σ) := by
    intro x hx; simp at hx; rcases hx with rfl | hx
    exacts [ha', validWord_canWord t.length w x hx]
  have hσ : σ.length = length t.length w := length_canWord t.length w
  have e : l.map PG.dot ++ cw σ ++ [PG.cross a] = l.map PG.dot ++ cw (a :: σ) := by
    simp [cw_cons]
  rw [cl_eq_cl e _ (e ▸ sChain_append_of h hg)]
  set h₀ := e ▸ sChain_append_of h hg
  have hlow' : Low D Sc t t' (crossCount (l.map PG.dot) + (a :: σ).length) ≤ NF D Sc t t' (m + 1) :=
    (low_mono D Sc (by simp; omega)).trans hlow
  by_cases hr : IsReduced t.length (a :: σ)
  · set σ' := canWord t.length (sadj t.length a * w)
    have hb : BraidEquiv (a :: σ) σ' :=
      braidEquiv_of_isReduced hr (isReduced_canWord t.length _) (by simp [σ, σ'])
    have h' := sChain_of_braid (l.map PG.dot) hb hv rfl h₀
    refine (braid_move (D := D) (Sc := Sc) (l.map PG.dot) rfl hb hv h₀ h').mem hlow'
      (Submodule.subset_span ⟨l, hs, hl, sadj t.length a * w, ?_, h', rfl⟩)
    have h2 : wordProd t.length (a :: σ) = sadj t.length a * w := by simp [σ]
    have := hr.2
    rw [h2, List.length_cons] at this
    omega
  · obtain ⟨σ', hb, hrep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hv hr
    have h' := sChain_of_braid (l.map PG.dot) hb hv rfl h₀
    refine (braid_move (D := D) (Sc := Sc) (l.map PG.dot) rfl hb hv h₀ h').mem hlow' (hlow' ?_)
    have e₂ : l.map PG.dot ++ cw σ' = l.map PG.dot ++ cw σ' ++ [] := by simp
    rw [cl_eq_cl e₂ h' (e₂ ▸ h')]
    refine filt_le_low D Sc ?_ (cl_mem_filt_of_hasRepeat (l.map PG.dot) [] rfl
      (hb.validWord_iff.mp hv) hrep (e₂ ▸ h'))
    have := hb.length_eq
    simp at this ⊢; omega

theorem nil_mem_nf {t t' : List I} (h : SChain t (pl t []) t') (m : ℕ) :
    cl D Sc t t' [] h ∈ NF D Sc t t' m := by
  have hc : canWord t.length 1 = [] :=
    List.eq_nil_of_length_eq_zero (by rw [length_canWord, length_eq_zero_iff])
  have e : ([] : List PG) = ([] : List ℕ).map PG.dot ++ cw (canWord t.length 1) := by simp [hc]
  refine Submodule.subset_span ⟨[], List.Pairwise.nil, by simp, 1, ?_, e ▸ h, ?_⟩
  · simp [length_eq_zero_iff.mpr rfl]
  · exact (cl_eq_cl e h _).symm

theorem cl_mem_nf {t : List I} {m : ℕ} (hlow : ∀ t', Low D Sc t t' m ≤ NF D Sc t t' m)
    (hprev : ∀ j < m, ∀ t', Filt D Sc t t' j ≤ NF D Sc t t' j) (gs : List PG) :
    ∀ {t'} (h : SChain t (pl t gs) t'), crossCount gs ≤ m → cl D Sc t t' gs h ∈ NF D Sc t t' m := by
  induction gs using List.reverseRecOn with
  | nil => intro t' h _; exact nil_mem_nf h m
  | append_singleton gs g ih =>
    intro t' h hc
    simp only [crossCount_append, crossCount_cons, crossCount_nil, add_zero] at hc
    by_cases hfit : g.pos + g.width ≤ (tgt t gs).length
    · rw [cl_append]
      cases g with
      | dot p =>
        exact nf_comp_dot (hlow t') (by simp [PG.pos, PG.width] at hfit ⊢; omega) _
          (ih (sChain_pl t gs) (by simp [PG.isCross] at hc ⊢; omega))
      | cross a =>
        simp only [PG.isCross] at hc
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact nf_comp_cross (hlow t') (by simp [PG.pos, PG.width] at hfit ⊢; omega) _
          (hprev m' (by omega) _ (cl_mem_filt D Sc _ (by omega)))
    · have e : pl t (gs ++ [g]) = pl t gs := by
        rw [pl_append]; simp [ld_eq_nil (show (tgt t gs).length < g.pos + g.width by omega)]
      have h' : SChain t (pl t gs) t' := e ▸ h
      rw [cl_congr D Sc h h' (by rw [e])]
      exact ih h' (by omega)

variable (D Sc) in
/-- Words with at most `m` crossings lie in the span of normal forms with `ℓ(w) ≤ m`. -/
theorem filt_le_nf (t : List I) (m : ℕ) (t' : List I) : Filt D Sc t t' m ≤ NF D Sc t t' m := by
  induction m using Nat.strong_induction_on generalizing t' with
  | _ m ihm =>
    have hlow : ∀ t', Low D Sc t t' m ≤ NF D Sc t t' m := by
      intro t'
      rcases m with _ | j
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨gs, h, hc, rfl⟩
        exact absurd hc (Nat.not_lt_zero _)
      · exact (low_le_filt D Sc j).trans ((ihm j (by omega) t').trans (nf_mono (by omega)))
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨gs, h, hc, rfl⟩
    exact cl_mem_nf hlow (fun j hj t' => ihm j hj t') gs h hc

theorem exists_mkD {t t' : List I} (d : ob D t ⟶ ob D t') :
    ∃ ls, ∃ h : SChain t ls t', d = mkD D ls h := by
  obtain ⟨ls, hc⟩ := d
  induction ls generalizing t with
  | nil =>
    have : t = t' := congrArg Obj.word hc
    subst this
    exact ⟨[], rfl, rfl⟩
  | cons L ls ih =>
    obtain ⟨st, l, g, r⟩ := L
    cases st
    obtain ⟨-, hd, hc⟩ := hc
    obtain ⟨ms, hm, e⟩ := ih hc
    refine ⟨(l, g, r) :: ms, ⟨(congrArg Obj.word hd).symm, hm⟩, ?_⟩
    apply Diagram.ext
    have := congrArg Diagram.layers e
    simp only [layers_mkD, layList, List.map_cons] at this ⊢
    rw [← this]
    rfl

variable (D Sc) in
/-- **Spanning.** Every morphism `t → t'` of the quiver Hecke supercategory `H` is a linear
combination of the normal forms `x^u ψ_w`: dots on the strands `l` (in increasing order) below the
crossings of the canonical reduced word of a permutation `w` (Brundan–Ellis,
arXiv:1701.04133v2, §11; Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Corollary 3.15). -/
theorem span_normalForms (t t' : List I) :
    Submodule.span k {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') |
      ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
        ∃ w : Equiv.Perm (Fin t.length),
          ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (canWord t.length w)) h = f} = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun f => ?_
  induction f using (pres D Sc).hom_induction with
  | diag d =>
    obtain ⟨ls, h, rfl⟩ := exists_mkD d
    rw [diag_mkD_eq_cl D Sc ls h _ (exists_pl h)]
    have := filt_le_nf D Sc t _ t'
      (cl_mem_filt D Sc (gs := ls.map LayerData.pg) ((exists_pl h).symm ▸ h) le_rfl)
    exact Submodule.span_mono (by rintro _ ⟨l, hs, hl, w, -, h, e⟩; exact ⟨l, hs, hl, w, h, e⟩) this
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | smul r f hf => exact Submodule.smul_mem _ r hf

end OddMath.QuiverHecke
