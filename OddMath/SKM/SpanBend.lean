/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanBubbleOut
import OddMath.SKM.SpanCapCup

/-!
# Bending: from two-sided to one-sided spanning sets

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. KL III reduce the spanning statement for
`HOM(E_s 1_λ, E_t 1_λ)` to the one-sided case `HOM(1_λ, E_{s* t} 1_λ)` by bending the lower
endpoints up with nested cups (biadjointness, KL III §3.1.1 and §2.2: attaching U-turns gives a
bijection of the pairings). This file is the super analogue, with the exact signs.

## Words and blocks

`dualW w = s*` is the reversed word of the dual letters (`flipL`). For a word `w`:

* `cupA w : 1 → w w*`: nested cups, the cup of the first letter outermost;
* `capA w : w* w → 1`: nested caps, the cap of the first letter innermost.

The cup of a letter `l` is `xCupL l`: the rightward cup `η` for `l = Fᵢ` and the leftward cup
`η'` for `l = Eᵢ`; the cap is `xCapL l` (`ε`, resp. `ε'`). Here `η` and `ε` are even and `η'`,
`ε'` have parity `|i, λ| = |i|(⟨hᵢ,λ⟩ + 1)` (`etaP_mem`, `epsP_mem`). Since `|i| dᵢⱼ` is even,
`|i, λ|` does not depend on `λ` within a coset of the root lattice (`ipar_wt`), so all parities
below are taken at the weight `μ` of the rightmost region.

## Where the signs come from

* `xpar μ L`: the parity of an extended diagram (`xev_mem_homPar`); the super interchange law with
  its exact sign (`xev_interchange_exact`, `xev_ichg_exact`).
* `zigR_exact`: the zigzag with the cup on the right is the identity for both orientations
  ((1.10), (6.6) second relation); `zigL_exact`: the zigzag with the cup on the left is the identity
  for `Fᵢ` and `(-1)^{|i,λ|}` for `Eᵢ` ((1.10), (6.6) first relation).
* Block zigzags (`zigB_block`, `zigA_block`): straightening the nested zigzags needs interchanges of
  the cap of one letter with the cups of the inner letters. With `cupPar μ l` the parity of the cup
  of `l`, `cupsPar μ w = ∑ cupPar` and `pairPar μ w = ∑_{a < b} cupPar(w_a) cupPar(w_b)`:
  `zigB = (-1)^{pairPar w}` and `zigA = (-1)^{pairPar w + cupsPar w}`.

## Bending

* `bendF μ s t : HOM(E_s 1_μ, E_t 1_μ) → HOM(1_μ, E_{s* t} 1_μ)`: nested cups `cupA s*` on the
  left, then `f` on the right;
* `bendG μ s t : HOM(1_μ, E_{s* t} 1_μ) → HOM(E_s 1_μ, E_t 1_μ)`: `g` to the right of `s`, then the
  nested caps `capA s*` on the left.

They shift the parity by `cupsPar μ s*` (`bendF_mem_homPar`, `bendG_mem_homPar`), preserve crossing
counts (`bendF_mem_leL`, `bendG_mem_leL`), and are mutually inverse up to explicit signs depending
on the parity:

* `bendG_bendF`: for `f` of parity `p`, `bendG (bendF f) = (-1)^{pairPar s* + cupsPar s* · p} f`;
* `bendF_bendG`: for `g` of parity `q`,
  `bendF (bendG g) = (-1)^{cupsPar s* · q + pairPar s* + cupsPar s*} g`.

## Transport of spanning sets

* `span_image_bendG_eq_top`, `span_image_bendF_eq_top`: spanning sets transport both ways;
* `diagBubSpan μ s t 𝒞`: the span of the diagrams `C ∈ 𝒞` followed by a product of bubbles in the
  rightmost region; `bendL s t C` is the two-sided bent form of a one-sided diagram `C`
  (`C` to the right of `s`, then `capA s*`);
* `bendG_diagBubSpan_le`, `diagBubSpan_bendL_eq_top`: if the diagrams of `𝒞` with bubbles on the
  right span `HOM(1_μ, E_{s* t} 1_μ)`, then the bent diagrams `bendL s t C` with bubbles on the
  right span `HOM(E_s 1_μ, E_t 1_μ)`; `mem_diagBubSpan_bendL_of_bendF_mem` is the version for one
  homogeneous 2-morphism.

The statements are independent of the choice of the one-sided family `𝒞`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Dual words -/

/-- The dual word `w* `: the dual letters of `w` in the reverse order. -/
def dualW (w : List (Letter I)) : List (Letter I) := (w.map flipL).reverse

@[simp] theorem dualW_nil : dualW ([] : List (Letter I)) = [] := rfl

@[simp] theorem dualW_cons (l : Letter I) (w : List (Letter I)) :
    dualW (l :: w) = dualW w ++ [flipL l] := by
  simp [dualW]

theorem dualW_append (a b : List (Letter I)) : dualW (a ++ b) = dualW b ++ dualW a := by
  simp [dualW]

@[simp] theorem dualW_dualW (w : List (Letter I)) : dualW (dualW w) = w := by
  simp [dualW, List.map_reverse, List.map_map, Function.comp_def]

/-! ## Parities of leftward cups and caps -/

theorem ipar_add_alpha (i j : I) (μ : X) :
    ipar D i (D.α j + μ) = ipar D i μ := by
  have := ipar_wt_upj (D := D) i j μ
  simpa [wt, sh] using this

/-- **The parity `|i, λ|` of `η'` and `ε'` is constant on cosets of the root lattice.** -/
theorem ipar_wt (i : I) (μ : X) : ∀ w : List (Letter I), ipar D i (wt D μ w) = ipar D i μ
  | [] => rfl
  | l :: w => by
    obtain ⟨_ | _, j⟩ := l
    · have h := ipar_add_alpha (D := D) i j (-D.α j + wt D μ w)
      rw [add_neg_cancel_left] at h
      simpa [wt, sh, ipar_wt i μ w] using h.symm
    · simpa [wt, sh, ipar_wt i μ w] using ipar_add_alpha (D := D) i j (wt D μ w)

variable (D) in
/-- The parity of the cup `xCupL l` (and of the cap `xCapL l`) in the region `μ`: `|i, μ|` for
`l = Eᵢ` (`η'`, `ε'`), `0` for `l = Fᵢ` (`η`, `ε`). -/
def cupPar (μ : X) (l : Letter I) : ZMod 2 := if l.1 then ipar D l.2 μ else 0

variable (D) in
/-- The parity of the nested cups (or caps) of a word: `∑_a cupPar(w_a)`. -/
def cupsPar (μ : X) (w : List (Letter I)) : ZMod 2 := (w.map (cupPar D μ)).sum

variable (D) in
/-- The sign exponent of the block zigzags: `∑_{a < b} cupPar(w_a) cupPar(w_b)`. -/
def pairPar (μ : X) : List (Letter I) → ZMod 2
  | [] => 0
  | l :: w => cupPar D μ l * cupsPar D μ w + pairPar μ w

@[simp] theorem cupsPar_nil (μ : X) : cupsPar D μ ([] : List (Letter I)) = 0 := rfl

@[simp] theorem cupsPar_cons (μ : X) (l : Letter I) (w : List (Letter I)) :
    cupsPar D μ (l :: w) = cupPar D μ l + cupsPar D μ w := by
  simp [cupsPar]

@[simp] theorem pairPar_nil (μ : X) : pairPar D μ ([] : List (Letter I)) = 0 := rfl

@[simp] theorem pairPar_cons (μ : X) (l : Letter I) (w : List (Letter I)) :
    pairPar D μ (l :: w) = cupPar D μ l * cupsPar D μ w + pairPar D μ w := rfl

theorem cupPar_wt (μ : X) (u : List (Letter I)) (l : Letter I) :
    cupPar D (wt D μ u) l = cupPar D μ l := by
  simp only [cupPar, ipar_wt]

theorem cupsPar_wt (μ : X) (u w : List (Letter I)) : cupsPar D (wt D μ u) w = cupsPar D μ w := by
  have h : cupPar D (wt D μ u) = cupPar D μ := funext (cupPar_wt μ u)
  rw [cupsPar, cupsPar, h]

theorem pairPar_wt (μ : X) (u : List (Letter I)) :
    ∀ w : List (Letter I), pairPar D (wt D μ u) w = pairPar D μ w
  | [] => rfl
  | l :: w => by rw [pairPar_cons, pairPar_cons, cupPar_wt, cupsPar_wt, pairPar_wt μ u w]

/-! ## The parity of an extended diagram -/

variable (D) in
/-- The parity of an extended layer, in a diagram with rightmost region `ν`. -/
def xlpar (ν : X) : XLayer I → ZMod 2
  | (_, .gen g, _) => g.parity D
  | (_, .lcup i, _) => ipar D i ν
  | (_, .lcap i, _) => ipar D i ν

variable (D) in
/-- The parity of an extended diagram with rightmost region `ν`. -/
def xpar (ν : X) (L : List (XLayer I)) : ZMod 2 := (L.map (xlpar D ν)).sum

@[simp] theorem xpar_nil (ν : X) : xpar D ν ([] : List (XLayer I)) = 0 := rfl

@[simp] theorem xpar_cons (ν : X) (x : XLayer I) (L : List (XLayer I)) :
    xpar D ν (x :: L) = xlpar D ν x + xpar D ν L := by
  simp [xpar]

theorem xpar_append (ν : X) (L M : List (XLayer I)) :
    xpar D ν (L ++ M) = xpar D ν L + xpar D ν M := by
  simp [xpar]

theorem xlpar_wt (ν : X) (u : List (Letter I)) (x : XLayer I) :
    xlpar D (wt D ν u) x = xlpar D ν x := by
  obtain ⟨a, g, b⟩ := x
  cases g <;> simp [xlpar, ipar_wt]

theorem xpar_wt (ν : X) (u : List (Letter I)) (L : List (XLayer I)) :
    xpar D (wt D ν u) L = xpar D ν L := by
  have h : xlpar D (wt D ν u) = xlpar D ν := funext (xlpar_wt ν u)
  rw [xpar, xpar, h]

@[simp] theorem xpar_map_xwhL (ν : X) (u v : List (Letter I)) (L : List (XLayer I)) :
    xpar D ν (L.map (xwhL u v)) = xpar D ν L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨a, g, b⟩ := x
    rw [List.map_cons, xpar_cons, xpar_cons, ih]
    cases g <;> rfl

@[simp] theorem xpar_map_ofL (ν : X) (L : List (LayerData I)) :
    xpar D ν (L.map ofL) = parsum D L := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [List.map_cons, xpar_cons, ih, parsum_cons]; rfl

theorem xlay_mem_homPar (ν : X) (x : XLayer I) :
    xlay cs ν x ∈ homPar D Sc ν (x.1 ++ x.2.1.dom ++ x.2.2) (x.1 ++ x.2.1.cod ++ x.2.2)
      (xlpar D ν x) := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | gen g =>
    have h := cl_mem_homPar' (D := D) (Sc := Sc) ν (a ++ g.dom ++ b) (a ++ g.cod ++ b) [(a, g, b)]
    show cl D Sc ν (a ++ g.dom ++ b) (a ++ g.cod ++ b) [(a, g, b)] ∈
      homPar D Sc ν (a ++ g.dom ++ b) (a ++ g.cod ++ b) (g.parity D)
    simpa using h
  | lcup i =>
    have h := plcL_mem ν a b (etaP_mem cs i (wt D ν b))
    rw [ipar_wt] at h
    exact h
  | lcap i =>
    have h := plcL_mem ν a b (epsP_mem cs i (wt D ν b))
    rw [ipar_wt] at h
    exact h

/-- **An extended diagram is homogeneous of parity `xpar`.** -/
theorem xev_mem_homPar (ν : X) (s t : List (Letter I)) (L : List (XLayer I)) :
    xev cs ν s t L ∈ homPar D Sc ν s t (xpar D ν L) := by
  induction L generalizing s with
  | nil => rw [xev_nil]; simpa using cl_mem_homPar' (D := D) (Sc := Sc) ν s t []
  | cons x L ih =>
    have h := comp_mem_homPar (cl_mem_homPar' (D := D) (Sc := Sc) ν s _ [])
      (comp_mem_homPar (xlay_mem_homPar cs ν x) (ih (x.1 ++ x.2.1.cod ++ x.2.2)))
    rw [parsum_nil, zero_add, ← xpar_cons] at h
    exact h

/-! ## The super interchange law with its exact sign -/

/-- **Super interchange of two extended blocks, with the exact sign** `(-1)^{|A||B|}`. -/
theorem xev_interchange_exact (ν : X) {s s' t t' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain s A s') (hB : XChain t B t') :
    xev cs ν (s ++ t) (s' ++ t') (A.map (xwhL [] t) ++ B.map (xwhL s' [])) =
      zsign k (xpar D ν A * xpar D ν B) •
        xev cs ν (s ++ t) (s' ++ t') (B.map (xwhL s []) ++ A.map (xwhL [] t')) := by
  have hp := xev_mem_homPar cs (wt D ν t) s s' A
  rw [xpar_wt] at hp
  have hq := xev_mem_homPar cs ν t t' B
  have hw : wt D ν t = wt D ν t' := hB.wt_eq ν
  have E := plcL_interchange_hom (D := D) (Sc := Sc) ν hw hp hq
  have e₁ := plcL_xev cs ν [] t (s := s) (t := s') A
  have e₂ := plcL_xev cs ν [] t' (s := s) (t := s') A
  rw [regionCast_family (f := fun ν => xev cs ν s s' A), e₁, e₂, xev_plcL_right,
    xev_plcL_right] at E
  have hA' : XChain (s ++ t) (A.map (xwhL [] t)) (s' ++ t) := by simpa using hA.whisk [] t
  have hB' : XChain (s ++ t) (B.map (xwhL s [])) (s ++ t') := by simpa using hB.whisk s []
  rw [xev_append cs _ hA', xev_append cs _ hB']
  exact E

/-- **Super interchange of two extended blocks in context, with the exact sign.** -/
theorem xev_ichg_exact (μ : X) {S T : List (Letter I)} (pre post : List (XLayer I))
    (P Q : List (Letter I)) {s s' t t' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain s A s') (hB : XChain t B t') (hpre : XChain S pre (P ++ (s ++ t) ++ Q)) :
    xev cs μ S T (pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post) =
      zsign k (xpar D μ A * xpar D μ B) •
        xev cs μ S T (pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post) := by
  have hp := xev_interchange_exact cs (wt D μ Q) hA hB
  rw [xpar_wt, xpar_wt] at hp
  have hA' : XChain (s ++ t) (A.map (xwhL [] t) ++ B.map (xwhL s' [])) (s' ++ t') :=
    XChain.append (by simpa using hA.whisk [] t) (by simpa using hB.whisk s' [])
  have hB' : XChain (s ++ t) (B.map (xwhL s []) ++ A.map (xwhL [] t')) (s' ++ t') :=
    XChain.append (by simpa using hB.whisk s []) (by simpa using hA.whisk [] t')
  have e₁ : pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post =
      pre ++ (A.map (xwhL [] t) ++ B.map (xwhL s' [])).map (xwhL P Q) ++ post := by
    simp only [List.map_append, map_xwhL_xwhL, List.append_nil, List.nil_append, List.append_assoc]
  have e₂ : pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post =
      pre ++ (B.map (xwhL s []) ++ A.map (xwhL [] t')).map (xwhL P Q) ++ post := by
    simp only [List.map_append, map_xwhL_xwhL, List.append_nil, List.nil_append, List.append_assoc]
  rw [e₁, e₂, xev_ctx cs μ pre post P Q hpre hA', xev_ctx cs μ pre post P Q hpre hB', hp,
    map_smul, Linear.smul_comp, Linear.comp_smul]

/-- The super interchange law in context, the right block first. -/
theorem xev_ichg_exact' (μ : X) {S T : List (Letter I)} (pre post : List (XLayer I))
    (P Q : List (Letter I)) {s s' t t' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain s A s') (hB : XChain t B t') (hpre : XChain S pre (P ++ (s ++ t) ++ Q)) :
    xev cs μ S T (pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post) =
      zsign k (xpar D μ A * xpar D μ B) •
        xev cs μ S T (pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post) := by
  rw [xev_ichg_exact cs μ pre post P Q hA hB hpre, smul_smul, zsign_mul_self', one_smul]

/-- A local relation `Z = c • 1` in context. -/
theorem xev_ctx_smul_id (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I))
    (u v : List (Letter I)) {s : List (Letter I)} {Z : List (XLayer I)} {c : k}
    (hZ : xev cs (wt D μ v) s s Z = c • 𝟙 _) (hpre : XChain s₀ pre (u ++ s ++ v))
    (hZc : XChain s Z s) :
    xev cs μ s₀ t₀ (pre ++ Z.map (xwhL u v) ++ post) = c • xev cs μ s₀ t₀ (pre ++ post) := by
  rw [xev_ctx cs μ pre post u v hpre hZc, hZ, map_smul, ← cl_nil, plcL_cl, List.map_nil,
    Linear.smul_comp, Linear.comp_smul, cl_nil, Category.id_comp, xev_append cs _ hpre]

/-! ## Exact zigzags for one letter -/

@[simp] theorem cupPar_up (μ : X) (i : I) : cupPar D μ (up i) = ipar D i μ := rfl
@[simp] theorem cupPar_dn (μ : X) (i : I) : cupPar D μ (dn i) = 0 := rfl

theorem xpar_xCupL (μ : X) (l : Letter I) : xpar D μ (xCupL l) = cupPar D μ l := by
  obtain ⟨_ | _, i⟩ := l
  · simp [xCupL, xpar, xlpar, cupPar, Shape.parity]
  · simp [xCupL, xpar, xlpar, cupPar]

theorem xpar_xCapL (μ : X) (l : Letter I) : xpar D μ (xCapL l) = cupPar D μ l := by
  obtain ⟨_ | _, i⟩ := l
  · simp [xCapL, xpar, xlpar, cupPar, Shape.parity]
  · simp [xCapL, xpar, xlpar, cupPar]

/-- **The zigzag with the cup on the left, with its exact sign**: on `Fᵢ` (`η`, `ε`) it is the
identity ((1.10)); on `Eᵢ 1_ν` (`η'`, `ε'`) it is `(-1)^{|i,ν|}` ((6.6), first relation). -/
theorem zigL_exact (ν : X) (l : Letter I) :
    xev cs ν [l] [l] ((xCupL l).map (xwhL [] [l]) ++ (xCapL l).map (xwhL [l] [])) =
      zsign k (cupPar D ν l) • 𝟙 _ := by
  obtain ⟨_ | _, i⟩ := l
  · rw [cupPar_dn, zsign_zero, one_smul, show (xCupL (dn i)).map (xwhL [] [dn i]) ++
      (xCapL (dn i)).map (xwhL [dn i] []) =
        [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])].map ofL from rfl, xev_map_ofL,
      cl_zigF, cl_nil]
  · rw [cupPar_up, ← eq_6_6_a cs i ν]
    change xev cs ν [up i] [up i] ([([], .lcup i, [up i])] ++ [([up i], .lcap i, [])]) = _
    rw [xev_append cs _ (show XChain [up i] [([], .lcup i, [up i])] [up i, dn i, up i] from
      ⟨rfl, rfl⟩), show xev cs ν [up i] [up i, dn i, up i] [([], .lcup i, [up i])] = leta cs i ν
        from xev_single cs ν ([], .lcup i, [up i]), show xev cs ν [up i, dn i, up i] [up i]
          [([up i], .lcap i, [])] = reps cs i ν from xev_single cs ν ([up i], .lcap i, [])]

/-- **The zigzag with the cup on the right is the identity** for both orientations ((1.10),
(6.6), second relation). -/
theorem zigR_exact (ν : X) (l : Letter I) :
    xev cs ν [flipL l] [flipL l]
        ((xCupL l).map (xwhL [flipL l] []) ++ (xCapL l).map (xwhL [] [flipL l])) = 𝟙 _ := by
  obtain ⟨_ | _, i⟩ := l
  · change xev cs ν [up i] [up i] ([([up i], Shape.cup i, []), ([], Shape.cap i, [up i])].map ofL) =
      _
    rw [xev_map_ofL, cl_zigE, cl_nil]
    rfl
  · change xev cs ν [dn i] [dn i] ([([dn i], .lcup i, [])] ++ [([], .lcap i, [dn i])]) =
      𝟙 ((pres D Sc).obj (ob D ν [dn i]))
    rw [← eq_6_6_b cs i ν, xev_append cs _ (show XChain [dn i]
      [([dn i], .lcup i, [])] [dn i, up i, dn i] from ⟨rfl, rfl⟩),
      show xev cs ν [dn i] [dn i, up i, dn i] [([dn i], .lcup i, [])] = retaF cs i ν
        from xev_single cs ν ([dn i], .lcup i, []),
      show xev cs ν [dn i, up i, dn i] [dn i] [([], .lcap i, [dn i])] = lepsF cs i ν
        from xev_single cs ν ([], .lcap i, [dn i])]

/-! ## Nested cups and caps -/

/-- Nested cups `1 → w w*`, the cup of the first letter outermost. -/
def cupA : List (Letter I) → List (XLayer I)
  | [] => []
  | l :: w => xCupL l ++ (cupA w).map (xwhL [l] [flipL l])

/-- Nested caps `w* w → 1`, the cap of the first letter innermost (it is applied first). -/
def capA : List (Letter I) → List (XLayer I)
  | [] => []
  | l :: w => (xCapL l).map (xwhL (dualW w) w) ++ capA w

@[simp] theorem cupA_nil : cupA ([] : List (Letter I)) = [] := rfl
@[simp] theorem capA_nil : capA ([] : List (Letter I)) = [] := rfl

theorem xChain_cupA : ∀ w : List (Letter I), XChain [] (cupA w) (w ++ dualW w)
  | [] => rfl
  | l :: w => (xChain_xCupL l).append (by simpa using (xChain_cupA w).whisk [l] [flipL l])

theorem xChain_capA : ∀ w : List (Letter I), XChain (dualW w ++ w) (capA w) []
  | [] => rfl
  | l :: w => XChain.append (by simpa using (xChain_xCapL l).whisk (dualW w) w) (xChain_capA w)

@[simp] theorem xcnt_cupA : ∀ w : List (Letter I), xcnt (cupA w) = 0
  | [] => rfl
  | l :: w => by simp [cupA, xcnt_cupA w]

@[simp] theorem xcnt_capA : ∀ w : List (Letter I), xcnt (capA w) = 0
  | [] => rfl
  | l :: w => by simp [capA, xcnt_capA w]

/-- The nested cups have parity `cupsPar`. -/
theorem xpar_cupA (μ : X) : ∀ w : List (Letter I), xpar D μ (cupA w) = cupsPar D μ w
  | [] => rfl
  | l :: w => by rw [cupA, xpar_append, xpar_map_xwhL, xpar_cupA μ w, xpar_xCupL, cupsPar_cons]

/-- The nested caps have parity `cupsPar`. -/
theorem xpar_capA (μ : X) : ∀ w : List (Letter I), xpar D μ (capA w) = cupsPar D μ w
  | [] => rfl
  | l :: w => by rw [capA, xpar_append, xpar_map_xwhL, xpar_capA μ w, xpar_xCapL, cupsPar_cons]

/-! ## Zigzag relations for blocks -/

theorem xev_nil_eq_id (ν : X) (s : List (Letter I)) : xev cs ν s s [] = 𝟙 _ := by
  rw [xev_nil, cl_nil]

/-- **Zigzag relation for blocks**, cups on the right: nested cups to the right of `w*`, then
nested caps, is `(-1)^{pairPar w}` times the identity of `w*`. The sign comes from moving the cap
of each letter below the cups of the letters after it (super interchange); the zigzags of single
letters with the cup on the right carry no sign (`zigR_exact`). -/
theorem zigB_block (ν : X) : ∀ w : List (Letter I),
    xev cs ν (dualW w) (dualW w)
        ((cupA w).map (xwhL (dualW w) []) ++ (capA w).map (xwhL [] (dualW w))) =
      zsign k (pairPar D ν w) • 𝟙 _
  | [] => by simp [xev_nil_eq_id, zsign_zero]
  | l :: w => by
    have IH := zigB_block (wt D ν [flipL l]) w
    rw [pairPar_wt] at IH
    set P := dualW w with hP
    have e₁ : (cupA (l :: w)).map (xwhL (dualW (l :: w)) []) ++
        (capA (l :: w)).map (xwhL [] (dualW (l :: w))) =
        (xCupL l).map (xwhL (P ++ [flipL l]) []) ++
          (cupA w).map (xwhL (P ++ [flipL l, l]) [flipL l]) ++
          (xCapL l).map (xwhL P (w ++ P ++ [flipL l])) ++
          (capA w).map (xwhL [] (P ++ [flipL l])) := by
      simp [cupA, capA, hP, List.map_map, List.append_assoc]
    have hpre : XChain (dualW (l :: w)) ((xCupL l).map (xwhL (P ++ [flipL l]) []))
        (P ++ ([flipL l, l] ++ []) ++ [flipL l]) := by
      simpa [hP] using (xChain_xCupL l).whisk (P ++ [flipL l]) []
    have E := xev_ichg_exact' cs ν (S := dualW (l :: w)) (T := dualW (l :: w))
      ((xCupL l).map (xwhL (P ++ [flipL l]) [])) ((capA w).map (xwhL [] (P ++ [flipL l])))
      P [flipL l] (xChain_xCapL l) (xChain_cupA w) hpre
    simp only [List.append_nil, List.nil_append, List.append_assoc] at E
    rw [e₁]
    simp only [List.append_assoc]
    rw [E, xpar_xCapL, xpar_cupA]
    -- the zigzag of the letter `l`
    have hZr : XChain [flipL l] ((xCupL l).map (xwhL [flipL l] []) ++
        (xCapL l).map (xwhL [] [flipL l])) [flipL l] :=
      XChain.append (by simpa using (xChain_xCupL l).whisk [flipL l] [])
        (by simpa using (xChain_xCapL l).whisk [] [flipL l])
    have Z1 := xev_ctx_smul_id cs ν (s₀ := dualW (l :: w)) (t₀ := dualW (l :: w)) []
      ((cupA w).map (xwhL P [flipL l]) ++ (capA w).map (xwhL [] (P ++ [flipL l]))) P []
      (c := 1) (by rw [one_smul]; exact zigR_exact cs _ l) (by simp [hP]) hZr
    have hZb : XChain P ((cupA w).map (xwhL P []) ++ (capA w).map (xwhL [] P)) P := by
      have h1 := (xChain_cupA w).whisk P []
      have h2 := (xChain_capA w).whisk [] P
      simp only [List.append_nil, List.nil_append, hP] at h1 h2 ⊢
      exact h1.append (by simpa [List.append_assoc] using h2)
    have Z2 := xev_ctx_smul_id cs ν (s₀ := dualW (l :: w)) (t₀ := dualW (l :: w)) [] [] [] [flipL l]
      IH (by simp [hP]) hZb
    have e₂ : ((xCupL l).map (xwhL (P ++ [flipL l]) []) ++
        ((xCapL l).map (xwhL P [flipL l]) ++
          ((cupA w).map (xwhL P [flipL l]) ++ (capA w).map (xwhL [] (P ++ [flipL l]))))) =
        [] ++ ((xCupL l).map (xwhL [flipL l] []) ++ (xCapL l).map (xwhL [] [flipL l])).map
          (xwhL P []) ++ ((cupA w).map (xwhL P [flipL l]) ++
            (capA w).map (xwhL [] (P ++ [flipL l]))) := by
      simp [List.map_map, List.append_assoc]
    have e₃ : (cupA w).map (xwhL P [flipL l]) ++ (capA w).map (xwhL [] (P ++ [flipL l])) =
        [] ++ ((cupA w).map (xwhL P []) ++ (capA w).map (xwhL [] P)).map (xwhL [] [flipL l]) ++
          [] := by
      simp [List.map_map]
    rw [e₂, Z1, List.nil_append, e₃, Z2, List.append_nil, xev_nil_eq_id, one_smul, smul_smul,
      ← zsign_add, pairPar_cons]

/-- **Zigzag relation for blocks**, cups on the left: nested cups to the left of `w`, then nested
caps, is `(-1)^{pairPar w + cupsPar w}` times the identity of `w`. Besides the interchange signs of
`zigB_block`, each zigzag of a single letter `Eᵢ` with the cup on the left contributes
`(-1)^{|i,λ|}` (`zigL_exact`). -/
theorem zigA_block (ν : X) : ∀ w : List (Letter I),
    xev cs ν w w ((cupA w).map (xwhL [] w) ++ (capA w).map (xwhL w [])) =
      zsign k (pairPar D ν w + cupsPar D ν w) • 𝟙 _
  | [] => by simp [xev_nil_eq_id, zsign_zero]
  | l :: w => by
    have IH := zigA_block ν w
    set P := dualW w with hP
    have e₁ : (cupA (l :: w)).map (xwhL [] (l :: w)) ++ (capA (l :: w)).map (xwhL (l :: w) []) =
        (xCupL l).map (xwhL [] (l :: w)) ++ (cupA w).map (xwhL [l] ([flipL l, l] ++ w)) ++
          (xCapL l).map (xwhL ([l] ++ (w ++ P)) w) ++ (capA w).map (xwhL (l :: w) []) := by
      simp [cupA, capA, hP, List.map_map, List.append_assoc]
    have hpre : XChain (l :: w) ((xCupL l).map (xwhL [] (l :: w)))
        ([l] ++ ([] ++ [flipL l, l]) ++ w) := by
      simpa using (xChain_xCupL l).whisk [] (l :: w)
    have E := xev_ichg_exact cs ν (S := l :: w) (T := l :: w)
      ((xCupL l).map (xwhL [] (l :: w))) ((capA w).map (xwhL (l :: w) []))
      [l] w (xChain_cupA w) (xChain_xCapL l) hpre
    rw [e₁, E, xpar_xCapL, xpar_cupA]
    have hZl : XChain [l] ((xCupL l).map (xwhL [] [l]) ++ (xCapL l).map (xwhL [l] [])) [l] :=
      XChain.append (by simpa using (xChain_xCupL l).whisk [] [l])
        (by simpa using (xChain_xCapL l).whisk [l] [])
    have Z1 := xev_ctx_smul_id cs ν (s₀ := l :: w) (t₀ := l :: w) []
      ((cupA w).map (xwhL [l] ([] ++ w)) ++ (capA w).map (xwhL (l :: w) [])) [] w
      (zigL_exact cs _ l) (by simp) hZl
    rw [cupPar_wt] at Z1
    have hZa : XChain w ((cupA w).map (xwhL [] w) ++ (capA w).map (xwhL w [])) w := by
      have h1 := (xChain_cupA w).whisk [] w
      have h2 := (xChain_capA w).whisk w []
      simp only [List.append_nil, List.nil_append] at h1 h2 ⊢
      exact h1.append (by simpa [List.append_assoc] using h2)
    have Z2 := xev_ctx_smul_id cs ν (s₀ := l :: w) (t₀ := l :: w) [] [] [l] [] IH (by simp) hZa
    have e₂ : (xCupL l).map (xwhL [] (l :: w)) ++ (xCapL l).map (xwhL ([l] ++ []) w) ++
        (cupA w).map (xwhL [l] ([] ++ w)) ++ (capA w).map (xwhL (l :: w) []) =
        [] ++ ((xCupL l).map (xwhL [] [l]) ++ (xCapL l).map (xwhL [l] [])).map (xwhL [] w) ++
          ((cupA w).map (xwhL [l] ([] ++ w)) ++ (capA w).map (xwhL (l :: w) [])) := by
      simp [List.map_map, List.append_assoc]
    have e₃ : (cupA w).map (xwhL [l] ([] ++ w)) ++ (capA w).map (xwhL (l :: w) []) =
        [] ++ ((cupA w).map (xwhL [] w) ++ (capA w).map (xwhL w [])).map (xwhL [l] []) ++ [] := by
      simp [List.map_map]
    rw [e₂, Z1, List.nil_append, e₃, Z2, List.append_nil, xev_nil_eq_id, smul_smul, smul_smul,
      ← zsign_add, ← zsign_add, pairPar_cons, cupsPar_cons]
    congr 2
    ring

/-! ## Bending -/

theorem xChain_cupA_dual (s : List (Letter I)) : XChain [] (cupA (dualW s)) (dualW s ++ s) := by
  simpa using xChain_cupA (dualW s)

theorem xChain_capA_dual (s : List (Letter I)) : XChain (s ++ dualW s) (capA (dualW s)) [] := by
  simpa using xChain_capA (dualW s)

/-- **Bending the lower endpoints up** (nested cups on the left):
`HOM(E_s 1_μ, E_t 1_μ) → HOM(1_μ, E_{s* t} 1_μ)`, `f ↦ (1_{s*} ⊗ f) ∘ cupA s*`. -/
def bendF (μ : X) (s t : List (Letter I)) :
    ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) →ₗ[k]
      ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t))) where
  toFun f := xev cs μ [] (dualW s ++ s ++ []) (cupA (dualW s)) ≫
    plcL D Sc μ (dualW s) [] s t f ≫ xev cs μ (dualW s ++ t ++ []) (dualW s ++ t) []
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- **Bending the lower endpoints back down** (nested caps on the left):
`HOM(1_μ, E_{s* t} 1_μ) → HOM(E_s 1_μ, E_t 1_μ)`, `g ↦ (capA s* ⊗ 1_t) ∘ (1_s ⊗ g)`. -/
def bendG (μ : X) (s t : List (Letter I)) :
    ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t))) →ₗ[k]
      ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) where
  toFun g := xev cs μ s (s ++ [] ++ []) [] ≫ plcL D Sc μ s [] [] (dualW s ++ t) g ≫
    xev cs μ (s ++ (dualW s ++ t) ++ []) t ((capA (dualW s)).map (xwhL [] t))
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Bending an extended diagram. -/
theorem bendF_xev (μ : X) {s t : List (Letter I)} {A : List (XLayer I)} (hA : XChain s A t) :
    bendF cs μ s t (xev cs μ s t A) =
      xev cs μ [] (dualW s ++ t) (cupA (dualW s) ++ A.map (xwhL (dualW s) [])) := by
  have E := xev_ctx cs μ (s₀ := []) (t₀ := dualW s ++ t) (cupA (dualW s)) [] (dualW s) []
    (by simpa using xChain_cupA_dual s) hA
  rw [List.append_nil] at E
  rw [E]
  rfl

/-- Bending back an extended diagram: the two-sided bent form. -/
theorem bendG_xev (μ : X) {s t : List (Letter I)} {B : List (XLayer I)}
    (hB : XChain [] B (dualW s ++ t)) :
    bendG cs μ s t (xev cs μ [] (dualW s ++ t) B) =
      xev cs μ s t (B.map (xwhL s []) ++ (capA (dualW s)).map (xwhL [] t)) := by
  have E := xev_ctx cs μ (s₀ := s) (t₀ := t) [] ((capA (dualW s)).map (xwhL [] t)) s []
    (by simp) hB
  rw [List.nil_append] at E
  rw [E]
  rfl

theorem xChain_bendF {s t : List (Letter I)} {A : List (XLayer I)} (hA : XChain s A t) :
    XChain [] (cupA (dualW s) ++ A.map (xwhL (dualW s) [])) (dualW s ++ t) :=
  (xChain_cupA_dual s).append (by simpa using hA.whisk (dualW s) [])

theorem xChain_bendG {s t : List (Letter I)} {B : List (XLayer I)}
    (hB : XChain [] B (dualW s ++ t)) :
    XChain s (B.map (xwhL s []) ++ (capA (dualW s)).map (xwhL [] t)) t :=
  XChain.append (by simpa using hB.whisk s [])
    (by simpa [List.append_assoc] using (xChain_capA_dual s).whisk [] t)

/-- **`bendG ∘ bendF` on an extended diagram**: the sign is `(-1)^{pairPar s* + cupsPar s* · |A|}`,
from the block zigzag `zigB_block` and from moving the caps below `A`. -/
theorem bendG_bendF_xev (μ : X) {s t : List (Letter I)} {A : List (XLayer I)}
    (hA : XChain s A t) :
    bendG cs μ s t (bendF cs μ s t (xev cs μ s t A)) =
      zsign k (pairPar D μ (dualW s) + cupsPar D μ (dualW s) * xpar D μ A) • xev cs μ s t A := by
  rw [bendF_xev cs μ hA, bendG_xev cs μ (xChain_bendF hA)]
  set w := dualW s with hw
  have hpre : XChain s ((cupA w).map (xwhL s [])) ([] ++ ((s ++ w) ++ s) ++ []) := by
    simpa [hw] using (xChain_cupA_dual s).whisk s []
  have E := xev_ichg_exact' cs μ (S := s) (T := t) ((cupA w).map (xwhL s [])) [] [] []
    (xChain_capA_dual s) hA hpre
  simp only [List.append_nil, List.nil_append, map_xwhL_nil_nil] at E
  have e₁ : (cupA w ++ A.map (xwhL w [])).map (xwhL s []) ++ (capA w).map (xwhL [] t) =
      (cupA w).map (xwhL s []) ++ A.map (xwhL (s ++ w) []) ++ (capA w).map (xwhL [] t) := by
    simp [List.map_map, List.append_assoc]
  have hZ : XChain s ((cupA w).map (xwhL s []) ++ (capA w).map (xwhL [] s)) s :=
    XChain.append (by simpa [hw] using (xChain_cupA_dual s).whisk s [])
      (by simpa using (xChain_capA_dual s).whisk [] s)
  have Z := zigB_block cs μ w
  rw [hw, dualW_dualW, ← hw] at Z
  rw [e₁, E, xpar_capA, xev_append cs _ hZ, Z, Linear.smul_comp, Category.id_comp, smul_smul,
    ← zsign_add, add_comm]

/-- **`bendF ∘ bendG` on an extended diagram**: the sign is
`(-1)^{cupsPar s* · |B| + pairPar s* + cupsPar s*}`, from moving `B` below the cups and from the block
zigzag `zigA_block`. -/
theorem bendF_bendG_xev (μ : X) {s t : List (Letter I)} {B : List (XLayer I)}
    (hB : XChain [] B (dualW s ++ t)) :
    bendF cs μ s t (bendG cs μ s t (xev cs μ [] (dualW s ++ t) B)) =
      zsign k (cupsPar D μ (dualW s) * xpar D μ B + (pairPar D μ (dualW s) + cupsPar D μ (dualW s))) •
        xev cs μ [] (dualW s ++ t) B := by
  rw [bendG_xev cs μ hB, bendF_xev cs μ (xChain_bendG hB)]
  set w := dualW s with hw
  have E := xev_ichg_exact cs μ (S := []) (T := w ++ t) [] ((capA w).map (xwhL w t)) [] []
    (xChain_cupA_dual s) hB (by simp)
  simp only [List.append_nil, List.nil_append, map_xwhL_nil_nil] at E
  have e₁ : cupA w ++ (B.map (xwhL s []) ++ (capA w).map (xwhL [] t)).map (xwhL w []) =
      cupA w ++ B.map (xwhL (w ++ s) []) ++ (capA w).map (xwhL w t) := by
    simp [List.map_map, List.append_assoc]
  have hZ : XChain w ((cupA w).map (xwhL [] w) ++ (capA w).map (xwhL w [])) w := by
    have h1 := (xChain_cupA_dual s).whisk [] w
    have h2 := (xChain_capA_dual s).whisk w []
    simp only [List.append_nil, List.nil_append, ← hw] at h1 h2
    exact h1.append (by simpa [List.append_assoc] using h2)
  have Z := xev_ctx_smul_id cs μ (s₀ := w ++ t) (t₀ := w ++ t) [] [] [] t
    (zigA_block cs (wt D μ t) w) (by simp) hZ
  rw [pairPar_wt, cupsPar_wt] at Z
  have e₂ : (cupA w).map (xwhL [] (w ++ t)) ++ (capA w).map (xwhL w t) =
      [] ++ ((cupA w).map (xwhL [] w) ++ (capA w).map (xwhL w [])).map (xwhL [] t) ++ [] := by
    simp [List.map_map]
  rw [e₁, E, xpar_cupA, List.append_assoc, xev_append cs _ hB, e₂, Z, List.append_nil,
    xev_nil_eq_id, Linear.comp_smul, Category.comp_id, smul_smul, ← zsign_add]

/-! ## Bending homogeneous 2-morphisms -/

/-- **`bendG` is a left inverse of `bendF` up to an explicit sign**: for `f` of parity `p`,
`bendG (bendF f) = (-1)^{pairPar s* + cupsPar s* · p} f`. -/
theorem bendG_bendF (μ : X) {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) :
    bendG cs μ s t (bendF cs μ s t f) =
      zsign k (pairPar D μ (dualW s) + cupsPar D μ (dualW s) * p) • f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, hp, rfl⟩ := hf
    rw [← xev_map_ofL cs, bendG_bendF_xev cs μ (XChain.of_sChain hL), xpar_map_ofL, hp]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, map_smul, hx, smul_comm]

/-- **`bendF` is a left inverse of `bendG` up to an explicit sign**: for `g` of parity `q`,
`bendF (bendG g) = (-1)^{cupsPar s* · q + pairPar s* + cupsPar s*} g`. -/
theorem bendF_bendG (μ : X) {s t : List (Letter I)} {q : ZMod 2}
    {g : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t))}
    (hg : g ∈ homPar D Sc μ [] (dualW s ++ t) q) :
    bendF cs μ s t (bendG cs μ s t g) =
      zsign k (cupsPar D μ (dualW s) * q + (pairPar D μ (dualW s) + cupsPar D μ (dualW s))) • g := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨L, hL, hp, rfl⟩ := hg
    rw [← xev_map_ofL cs, bendF_bendG_xev cs μ (XChain.of_sChain hL), xpar_map_ofL, hp]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, map_smul, hx, smul_comm]

/-- `bendF` shifts the parity by the parity `cupsPar s*` of the nested cups. -/
theorem bendF_mem_homPar (μ : X) {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) :
    bendF cs μ s t f ∈ homPar D Sc μ [] (dualW s ++ t) (cupsPar D μ (dualW s) + p) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, hp, rfl⟩ := hf
    rw [← xev_map_ofL cs, bendF_xev cs μ (XChain.of_sChain hL)]
    have h := xev_mem_homPar cs μ [] (dualW s ++ t)
      (cupA (dualW s) ++ (L.map ofL).map (xwhL (dualW s) []))
    rwa [xpar_append, xpar_map_xwhL, xpar_cupA, xpar_map_ofL, hp] at h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- `bendG` shifts the parity by the parity `cupsPar s*` of the nested caps. -/
theorem bendG_mem_homPar (μ : X) {s t : List (Letter I)} {q : ZMod 2}
    {g : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t))}
    (hg : g ∈ homPar D Sc μ [] (dualW s ++ t) q) :
    bendG cs μ s t g ∈ homPar D Sc μ s t (q + cupsPar D μ (dualW s)) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨L, hL, hp, rfl⟩ := hg
    rw [← xev_map_ofL cs, bendG_xev cs μ (XChain.of_sChain hL)]
    have h := xev_mem_homPar cs μ s t
      ((L.map ofL).map (xwhL s []) ++ (capA (dualW s)).map (xwhL [] t))
    rwa [xpar_append, xpar_map_xwhL, xpar_map_xwhL, xpar_capA, xpar_map_ofL, hp] at h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- `bendF` preserves crossing counts (the nested cups have no crossings). -/
theorem bendF_mem_leL (μ : X) {s t : List (Letter I)} {c : ℕ}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ LeL D Sc cs μ s t c) : bendF cs μ s t f ∈ LeL D Sc cs μ [] (dualW s ++ t) c := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    by_cases hc : XChain s L t
    · rw [bendF_xev cs μ hc]
      exact xev_mem_leL cs (by simpa using hL)
    · rw [xev_of_not cs hc, map_zero]; exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- `bendG` preserves crossing counts (the nested caps have no crossings). -/
theorem bendG_mem_leL (μ : X) {s t : List (Letter I)} {c : ℕ}
    {g : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t))}
    (hg : g ∈ LeL D Sc cs μ [] (dualW s ++ t) c) : bendG cs μ s t g ∈ LeL D Sc cs μ s t c := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨L, hL, rfl⟩ := hg
    by_cases hc : XChain [] L (dualW s ++ t)
    · rw [bendG_xev cs μ hc]
      exact xev_mem_leL cs (by simpa using hL)
    · rw [xev_of_not cs hc, map_zero]; exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-! ## Transport of spanning sets -/

/-- A homogeneous 2-morphism whose bent form lies in `M` is the bent-back image of an element of
`M`. -/
theorem mem_map_bendG_of_bendF_mem (μ : X) {s t : List (Letter I)} {p : ZMod 2}
    {M : Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t)))}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) (h : bendF cs μ s t f ∈ M) : f ∈ M.map (bendG cs μ s t) := by
  have e := bendG_bendF cs μ hf
  have e' : f = zsign k (pairPar D μ (dualW s) + cupsPar D μ (dualW s) * p) •
      bendG cs μ s t (bendF cs μ s t f) := by
    rw [e, smul_smul, zsign_mul_self', one_smul]
  rw [e']
  exact Submodule.smul_mem _ _ ⟨_, h, rfl⟩

/-- A homogeneous 2-morphism whose bent-back form lies in `M` is the bent image of an element of
`M`. -/
theorem mem_map_bendF_of_bendG_mem (μ : X) {s t : List (Letter I)} {q : ZMod 2}
    {M : Submodule k ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t))}
    {g : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t))}
    (hg : g ∈ homPar D Sc μ [] (dualW s ++ t) q) (h : bendG cs μ s t g ∈ M) :
    g ∈ M.map (bendF cs μ s t) := by
  have e := bendF_bendG cs μ hg
  have e' : g = zsign k (cupsPar D μ (dualW s) * q + (pairPar D μ (dualW s) + cupsPar D μ (dualW s))) •
      bendF cs μ s t (bendG cs μ s t g) := by
    rw [e, smul_smul, zsign_mul_self', one_smul]
  rw [e']
  exact Submodule.smul_mem _ _ ⟨_, h, rfl⟩

/-- If every normal-form diagram lies in a submodule, so does every 2-morphism. -/
theorem eq_top_of_cl_mem {μ : X} {s t : List (Letter I)}
    {N : Submodule k ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t))}
    (h : ∀ L, SChain s L t → cl D Sc μ s t L ∈ N) : N = ⊤ := by
  refine eq_top_iff.2 fun f _ => Submodule.span_le.2 ?_ (mem_span_cl μ f)
  rintro _ ⟨L, hL, rfl⟩
  exact h L hL

/-- **Spanning sets bend back**: if `S` spans `HOM(1_μ, E_{s* t} 1_μ)`, then `bendG '' S` spans
`HOM(E_s 1_μ, E_t 1_μ)`. -/
theorem span_image_bendG_eq_top (μ : X) {s t : List (Letter I)}
    {S : Set ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t)))}
    (hS : Submodule.span k S = ⊤) : Submodule.span k (bendG cs μ s t '' S) = ⊤ := by
  rw [← Submodule.map_span]
  exact eq_top_of_cl_mem fun L _ => mem_map_bendG_of_bendF_mem cs μ
    (cl_mem_homPar' μ s t L) (by rw [hS]; exact Submodule.mem_top)

/-- **Spanning sets bend up**: if `S` spans `HOM(E_s 1_μ, E_t 1_μ)`, then `bendF '' S` spans
`HOM(1_μ, E_{s* t} 1_μ)`. -/
theorem span_image_bendF_eq_top (μ : X) {s t : List (Letter I)}
    {S : Set ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t))}
    (hS : Submodule.span k S = ⊤) : Submodule.span k (bendF cs μ s t '' S) = ⊤ := by
  rw [← Submodule.map_span]
  exact eq_top_of_cl_mem fun L _ => mem_map_bendF_of_bendG_mem cs μ
    (cl_mem_homPar' μ [] (dualW s ++ t) L) (by rw [hS]; exact Submodule.mem_top)

/-! ## Diagrams followed by bubbles: the form of Theorem 8.1 -/

variable (D Sc) in
/-- The span of the diagrams `C ∈ 𝒞` (`E_s 1_μ → E_t 1_μ`) followed by an element of the image of
`β_μ` in the rightmost region: the right `SYM`-submodule generated by the diagrams of `𝒞`, as in
[BE2] Theorem 8.1. -/
def diagBubSpan (μ : X) (s t : List (Letter I)) (𝒞 : Set (List (XLayer I))) :
    Submodule k ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :=
  Submodule.span k {g | ∃ C ∈ 𝒞, ∃ β, IsBub cs μ β ∧ g = xev cs μ s t C ≫ bubAt D Sc μ t β}

/-- The two-sided bent form `E_s → E_t` of a one-sided diagram `C : 1 → E_{s* t}`: `C` to the
right of the strands `s`, then the nested caps `capA s*` on the left. -/
def bendL (s t : List (Letter I)) (C : List (XLayer I)) : List (XLayer I) :=
  C.map (xwhL s []) ++ (capA (dualW s)).map (xwhL [] t)

theorem xChain_bendL {s t : List (Letter I)} {C : List (XLayer I)}
    (hC : XChain [] C (dualW s ++ t)) : XChain s (bendL s t C) t := xChain_bendG hC

@[simp] theorem xcnt_bendL (s t : List (Letter I)) (C : List (XLayer I)) :
    xcnt (bendL s t C) = xcnt C := by
  simp [bendL]

theorem xpar_bendL (μ : X) (s t : List (Letter I)) (C : List (XLayer I)) :
    xpar D μ (bendL s t C) = xpar D μ C + cupsPar D μ (dualW s) := by
  rw [bendL, xpar_append, xpar_map_xwhL, xpar_map_xwhL, xpar_capA]

/-- **Bending back a diagram followed by bubbles, with the exact sign**: for `β` of parity `q`,
`bendG (C · β) = (-1)^{cupsPar s* · q} (bendL C) · β`; the sign comes from moving `β` below the nested
caps. -/
theorem bendG_xev_comp_bubAt (μ : X) {s t : List (Letter I)} {C : List (XLayer I)}
    (hC : XChain [] C (dualW s ++ t)) {q : ZMod 2}
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}
    (hβ : β ∈ closedPar D Sc μ q) :
    bendG cs μ s t (xev cs μ [] (dualW s ++ t) C ≫ bubAt D Sc μ (dualW s ++ t) β) =
      zsign k (cupsPar D μ (dualW s) * q) • (xev cs μ s t (bendL s t C) ≫ bubAt D Sc μ t β) := by
  induction hβ using Submodule.span_induction with
  | mem β hβ =>
    obtain ⟨M, hM, hq, rfl⟩ := hβ
    set w := dualW s with hw
    have hM' : XChain [] (M.map ofL) [] := XChain.of_sChain hM
    rw [bubAt_cl, bubAt_cl, ← xev_map_ofL cs μ (w ++ t), ← xev_map_ofL cs μ t,
      ← map_xwhL_map_ofL, ← map_xwhL_map_ofL, ← xev_append cs _ hC,
      ← xev_append cs _ (xChain_bendL hC),
      bendG_xev cs μ (hC.append (by simpa using hM'.whisk (w ++ t) []))]
    have hpre : XChain s (C.map (xwhL s [])) ([] ++ ((s ++ w ++ t) ++ []) ++ []) := by
      simpa [List.append_assoc] using hC.whisk s []
    have hcap : XChain (s ++ w ++ t) ((capA w).map (xwhL [] t)) t := by
      simpa [List.append_assoc] using (xChain_capA_dual s).whisk [] t
    have E := xev_ichg_exact' cs μ (S := s) (T := t) (C.map (xwhL s [])) [] [] [] hcap hM' hpre
    simp only [List.append_nil, List.nil_append, map_xwhL_nil_nil] at E
    have e₁ : (C ++ (M.map ofL).map (xwhL (w ++ t) [])).map (xwhL s []) ++
        (capA w).map (xwhL [] t) = C.map (xwhL s []) ++ (M.map ofL).map (xwhL (s ++ w ++ t) []) ++
          (capA w).map (xwhL [] t) := by
      simp [List.map_map, List.append_assoc]
    rw [e₁, E, xpar_map_xwhL, xpar_capA, xpar_map_ofL, hq, bendL, List.append_assoc]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, Preadditive.comp_add, map_add, hx, hy, map_add, Preadditive.comp_add, smul_add]
  | smul a x _ hx =>
    rw [map_smul, Linear.comp_smul, map_smul, hx, map_smul, Linear.comp_smul, smul_comm]

/-- **Bending back carries the one-sided form to the two-sided form**: `bendG` maps the span of
the diagrams of `𝒞` followed by bubbles into the span of their bent forms `bendL s t C` followed
by bubbles. -/
theorem bendG_diagBubSpan_le (μ : X) (s t : List (Letter I)) (𝒞 : Set (List (XLayer I))) :
    (diagBubSpan D Sc cs μ [] (dualW s ++ t) 𝒞).map (bendG cs μ s t) ≤
      diagBubSpan D Sc cs μ s t (bendL s t '' 𝒞) := by
  rw [diagBubSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨C, hC𝒞, β, hβ, rfl⟩, rfl⟩
  by_cases hC : XChain [] C (dualW s ++ t)
  · have hβ' := (isBub_iff_mem_bubbleProdSpan cs).1 hβ
    clear hβ
    induction hβ' using Submodule.span_induction with
    | mem β hβ =>
      obtain ⟨q, hq⟩ := hβ.exists_mem
      rw [SetLike.mem_coe, bendG_xev_comp_bubAt cs μ hC hq]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨bendL s t C, ⟨C, hC𝒞, rfl⟩, β, hβ.isBub, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [SetLike.mem_coe, map_add, Preadditive.comp_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [SetLike.mem_coe, map_smul, Linear.comp_smul, map_smul]
      exact Submodule.smul_mem _ a hx
  · rw [SetLike.mem_coe, xev_of_not cs hC, Limits.zero_comp, map_zero]
    exact Submodule.zero_mem _

/-- **Transport of the form of Theorem 8.1 along bending, for one homogeneous 2-morphism**: if
`f : E_s 1_μ → E_t 1_μ` is homogeneous and its bent form `bendF f` lies in the span of the
diagrams of `𝒞` followed by bubbles, then `f` lies in the span of the bent diagrams
`bendL s t C` followed by bubbles. -/
theorem mem_diagBubSpan_bendL_of_bendF_mem (μ : X) {s t : List (Letter I)}
    {𝒞 : Set (List (XLayer I))} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) (h : bendF cs μ s t f ∈ diagBubSpan D Sc cs μ [] (dualW s ++ t) 𝒞) :
    f ∈ diagBubSpan D Sc cs μ s t (bendL s t '' 𝒞) :=
  bendG_diagBubSpan_le cs μ s t 𝒞 (mem_map_bendG_of_bendF_mem cs μ hf h)

/-- **Reduction of Theorem 8.1 to the one-sided case**: if the diagrams of `𝒞` generate
`HOM(1_μ, E_{s* t} 1_μ)` as a right `SYM`-module (via `β_μ` in the rightmost region), then the
bent diagrams `bendL s t C`, `C ∈ 𝒞`, generate `HOM(E_s 1_μ, E_t 1_μ)`. -/
theorem diagBubSpan_bendL_eq_top (μ : X) {s t : List (Letter I)} {𝒞 : Set (List (XLayer I))}
    (h : diagBubSpan D Sc cs μ [] (dualW s ++ t) 𝒞 = ⊤) :
    diagBubSpan D Sc cs μ s t (bendL s t '' 𝒞) = ⊤ :=
  eq_top_of_cl_mem fun L _ => mem_diagBubSpan_bendL_of_bendF_mem cs μ (cl_mem_homPar' μ s t L)
    (by rw [h]; exact Submodule.mem_top)

end OddMath.SKM
