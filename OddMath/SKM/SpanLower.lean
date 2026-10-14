/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PlacementHom
import OddMath.SKM.ChevalleyInv

/-!
# Normal forms and lower terms in `𝔘(𝔤)`

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1 (the diagrams `f(σ, λ)` span `Hom(E_a 1_λ, E_b 1_λ)` as a right module over the
bubbles). The paper omits the proof, referring to M. Khovanov, A. Lauda, *A categorification of
quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11: induction on the number of crossings, using
that the local relations hold modulo diagrams with fewer crossings ("lower terms"). This file
sets up the induction.

## Normal forms

Every diagram of `𝔘(𝔤)` between the objects `E_s 1_μ` and `E_t 1_μ` is a normal-form diagram
(`diag_eq_mkD`), so every 2-morphism is a linear combination of classes `cl μ s t L`
(`mem_span_cl`). Consequently placement between strands is compatible with composition for all
2-morphisms (`plcL_comp`).

## Diagrams with leftward cups and caps

The leftward cup `η'` and cap `ε'` ((2.10), (2.11)) are not generators of the presentation: for
`⟨hᵢ, λ⟩ ≤ 0` the cup `η'` is the rightward cup followed by the leftward crossing, and for
`⟨hᵢ, λ⟩ ≥ 0` the cap `ε'` is the leftward crossing followed by the rightward cap. Counting
crossings in normal-form diagrams would therefore count a crossing in `η'` or `ε'` depending on the
weight, and the pitchfork relations (7.5), (7.6) would not preserve the count. As in the paper's
pictures we treat `η'` and `ε'` as crossingless: an extended layer (`XLayer`) carries a generator
of the presentation (`XShape.gen`), or `η'` (`XShape.lcup`) or `ε'` (`XShape.lcap`) placed
between strands, and `xev μ s t L` is the 2-morphism of a list of extended layers (`0` if they do
not chain from `s` to `t`). Normal-form diagrams are the lists of generators (`xev_map_ofL`).

## Crossing counts and lower terms

`xcnt L` counts the layers of `L` that are upward crossings `τ` or leftward crossings; `ccnt` is
the same count on normal-form layers. The rightward crossing `σ` (1.11) has one crossing, and the
downward crossing (2.1) one. Dots, rightward cups and caps, `♦`-cups and `♦`-caps, `η'` and `ε'`
count zero. (The `♦`-cups and caps are expressed through `η'`, `ε'`, dots and bubbles by (5.11),
(5.12).)

`LeL μ s t c` is the span of the 2-morphisms `xev μ s t L` with `xcnt L ≤ c`. It is closed under
composition (adding counts, `leL_comp`), placement (`plcL_leL`), rewriting in context (`ctxL_leL`)
and scalars (in particular the signs of the super interchange law); every 2-morphism lies in some
`LeL μ s t c` (`exists_mem_leL`). `xev_mod_ctx`, `xev_mod_at`: a relation modulo lower terms
holds in any context.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## Every 2-morphism is a combination of normal-form diagrams -/

/-- **Every 2-morphism is a linear combination of normal-form diagrams.** -/
theorem mem_span_cl (μ : X) {s t : List (Letter I)}
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    f ∈ Submodule.span k {g | ∃ L, SChain s L t ∧ g = cl D Sc μ s t L} := by
  obtain ⟨F, rfl⟩ := (pres D Sc).lin_surjective f
  induction F using Finsupp.induction_linear with
  | zero => rw [Presentation.lin_zero]; exact Submodule.zero_mem _
  | add F₁ F₂ h₁ h₂ => rw [Presentation.lin_add]; exact Submodule.add_mem _ h₁ h₂
  | single d r =>
    rw [Presentation.lin_single]
    refine Submodule.smul_mem _ r (Submodule.subset_span ?_)
    obtain ⟨ls, hls, rfl⟩ := diag_eq_mkD d
    exact ⟨ls, hls, (cl_of hls).symm⟩

/-- Placement between strands is compatible with composition. -/
theorem plcL_comp (μ : X) (u v : List (Letter I)) {s t r : List (Letter I)}
    (f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t))
    (g : (pres D Sc).obj (ob D (wt D μ v) t) ⟶ (pres D Sc).obj (ob D (wt D μ v) r)) :
    plcL D Sc μ u v s r (f ≫ g) = plcL D Sc μ u v s t f ≫ plcL D Sc μ u v t r g := by
  have hf := mem_span_cl (wt D μ v) f
  have hg := mem_span_cl (wt D μ v) g
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨M, hM, rfl⟩ := hg
      exact plcL_cl_comp μ u v L M hL hM
    | zero => simp
    | add x y _ _ hx hy => rw [Preadditive.comp_add, map_add, map_add, hx, hy, Preadditive.comp_add]
    | smul a x _ hx => rw [Linear.comp_smul, map_smul, map_smul, hx, Linear.comp_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [Preadditive.add_comp, map_add, map_add, hx, hy, Preadditive.add_comp]
  | smul a x _ hx => rw [Linear.smul_comp, map_smul, map_smul, hx, Linear.smul_comp]

/-! ## Identities between equal boundaries -/

theorem cl_nil_comp_nil {ν : X} {a b c : List (Letter I)} (h : b = c) :
    cl D Sc ν a b [] ≫ cl D Sc ν b c [] = cl D Sc ν a c [] := by
  subst h; rw [cl_nil, Category.comp_id]

theorem cl_cast {ν : X} {s s' t t' : List (Letter I)} (L : List (LayerData I)) (hs : s = s')
    (ht : t' = t) : cl D Sc ν s s' [] ≫ cl D Sc ν s' t' L ≫ cl D Sc ν t' t [] = cl D Sc ν s t L := by
  subst hs ht; rw [cl_nil, cl_nil, Category.id_comp, Category.comp_id]

theorem eq_of_wordCast {ν : X} {s t s' t' : List (Letter I)} (hs : s = s') (ht : t = t')
    {f : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    {g : (pres D Sc).obj (ob D ν s') ⟶ (pres D Sc).obj (ob D ν t')}
    (h : wordCast ν hs ht f = g) : f = cl D Sc ν s s' [] ≫ g ≫ cl D Sc ν t' t [] := by
  subst hs ht
  rw [cl_nil, cl_nil, Category.id_comp, Category.comp_id, ← h]
  rfl

/-! ## Crossing counts of normal-form layers -/

/-- The crossings among the generators: the upward crossing and the leftward crossing. -/
def Shape.isCross : Shape I → Bool
  | .cross _ _ => true
  | .lcross _ _ => true
  | _ => false

/-- The number of crossing layers of a list of normal-form layers. -/
def ccnt (L : List (LayerData I)) : ℕ := L.countP fun x => x.2.1.isCross

@[simp] theorem ccnt_nil : ccnt ([] : List (LayerData I)) = 0 := rfl

@[simp] theorem ccnt_cons (x : LayerData I) (L : List (LayerData I)) :
    ccnt (x :: L) = ccnt L + if x.2.1.isCross then 1 else 0 := by
  unfold ccnt; rw [List.countP_cons]

@[simp] theorem ccnt_append (L M : List (LayerData I)) : ccnt (L ++ M) = ccnt L + ccnt M := by
  unfold ccnt; rw [List.countP_append]

@[simp] theorem ccnt_map_whL (u v : List (Letter I)) (L : List (LayerData I)) :
    ccnt (L.map (whL u v)) = ccnt L := by
  unfold ccnt; rw [List.countP_map]; rfl

@[simp] theorem ccnt_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    ccnt (dotsL u i v n) = 0 := by
  unfold ccnt dotsL; rw [List.countP_eq_zero]; intro x hx
  rw [List.eq_of_mem_replicate hx]; simp [Shape.isCross]

@[simp] theorem ccnt_sigmaL (i j : I) : ccnt (sigmaL i j) = 1 := rfl
@[simp] theorem ccnt_lcrossL (i j : I) : ccnt (lcrossL i j) = 1 := rfl
@[simp] theorem ccnt_crossL (u : List (Letter I)) (i j : I) (v : List (Letter I)) :
    ccnt (crossL u i j v) = 1 := rfl
@[simp] theorem ccnt_dcupL (i : I) (n : ℕ) : ccnt (dcupL i n) = 0 := rfl
@[simp] theorem ccnt_dcapL (i : I) (n : ℕ) : ccnt (dcapL i n) = 0 := rfl
@[simp] theorem ccnt_epsL (i : I) (n : ℕ) : ccnt (epsL i n) = 0 := by simp [epsL, Shape.isCross]
@[simp] theorem ccnt_etaL (i : I) (n : ℕ) : ccnt (etaL i n) = 0 := by simp [etaL, Shape.isCross]

/-! ## Diagrams with leftward cups and caps -/

/-- The generators of the extended diagram language: a generator of the presentation, the
leftward cup `η' : 1 → Eᵢ Fᵢ` (2.10) or the leftward cap `ε' : Fᵢ Eᵢ → 1` (2.11). -/
inductive XShape (I : Type u)
  /-- A generator of the presentation `pres D Sc`. -/
  | gen (g : Shape I)
  /-- The leftward cup `η'`. -/
  | lcup (i : I)
  /-- The leftward cap `ε'`. -/
  | lcap (i : I)

namespace XShape

/-- Bottom boundary. -/
def dom : XShape I → List (Letter I)
  | gen g => g.dom
  | lcup _ => []
  | lcap i => [dn i, up i]

/-- Top boundary. -/
def cod : XShape I → List (Letter I)
  | gen g => g.cod
  | lcup i => [up i, dn i]
  | lcap _ => []

/-- Crossings: the upward and the leftward crossing. -/
def isCross : XShape I → Bool
  | gen g => g.isCross
  | _ => false

end XShape

/-- An extended layer: strands to the left, a generator, strands to the right. -/
abbrev XLayer (I : Type u) : Type u := List (Letter I) × XShape I × List (Letter I)

/-- A normal-form layer as an extended layer. -/
def ofL (x : LayerData I) : XLayer I := (x.1, .gen x.2.1, x.2.2)

/-- An extended layer placed between the strands `u` and `v`. -/
def xwhL (u v : List (Letter I)) (x : XLayer I) : XLayer I := (u ++ x.1, x.2.1, x.2.2 ++ v)

@[simp] theorem xwhL_ofL (u v : List (Letter I)) (x : LayerData I) :
    xwhL u v (ofL x) = ofL (whL u v x) := rfl

@[simp] theorem map_xwhL_map_ofL (u v : List (Letter I)) (L : List (LayerData I)) :
    (L.map ofL).map (xwhL u v) = (L.map (whL u v)).map ofL := by
  simp [List.map_map, Function.comp_def]

/-- The extended layers `L` form a diagram from `s` (bottom) to `t` (top). -/
def XChain : List (Letter I) → List (XLayer I) → List (Letter I) → Prop
  | s, [], t => s = t
  | s, x :: L, t => s = x.1 ++ x.2.1.dom ++ x.2.2 ∧ XChain (x.1 ++ x.2.1.cod ++ x.2.2) L t

theorem XChain.append {s r t : List (Letter I)} {L M : List (XLayer I)} (h₁ : XChain s L r)
    (h₂ : XChain r M t) : XChain s (L ++ M) t := by
  induction L generalizing s with
  | nil => cases h₁; exact h₂
  | cons x L ih => exact ⟨h₁.1, ih h₁.2⟩

theorem XChain.whisk {s t : List (Letter I)} {L : List (XLayer I)} (h : XChain s L t)
    (u v : List (Letter I)) : XChain (u ++ s ++ v) (L.map (xwhL u v)) (u ++ t ++ v) := by
  induction L generalizing s with
  | nil => cases h; rfl
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [xwhL], ?_⟩
    simpa [xwhL] using ih h

theorem XChain.of_sChain {s t : List (Letter I)} {L : List (LayerData I)} (h : SChain s L t) :
    XChain s (L.map ofL) t := by
  induction L generalizing s with
  | nil => exact h
  | cons x L ih => exact ⟨h.1, ih h.2⟩

/-- The number of crossing layers of a list of extended layers. -/
def xcnt (L : List (XLayer I)) : ℕ := L.countP fun x => x.2.1.isCross

@[simp] theorem xcnt_nil : xcnt ([] : List (XLayer I)) = 0 := rfl

@[simp] theorem xcnt_append (L M : List (XLayer I)) : xcnt (L ++ M) = xcnt L + xcnt M := by
  unfold xcnt; rw [List.countP_append]

@[simp] theorem xcnt_cons (x : XLayer I) (L : List (XLayer I)) :
    xcnt (x :: L) = xcnt L + if x.2.1.isCross then 1 else 0 := by
  unfold xcnt; rw [List.countP_cons]

@[simp] theorem xcnt_map_xwhL (u v : List (Letter I)) (L : List (XLayer I)) :
    xcnt (L.map (xwhL u v)) = xcnt L := by
  unfold xcnt; rw [List.countP_map]; rfl

@[simp] theorem xcnt_map_ofL (L : List (LayerData I)) : xcnt (L.map ofL) = ccnt L := by
  unfold xcnt ccnt; rw [List.countP_map]; rfl

variable (cs : CScalars Sc)

/-- The 2-morphism of a single extended layer, with rightmost region `ν`. -/
def xlay (ν : X) : (x : XLayer I) →
    ((pres D Sc).obj (ob D ν (x.1 ++ x.2.1.dom ++ x.2.2)) ⟶
      (pres D Sc).obj (ob D ν (x.1 ++ x.2.1.cod ++ x.2.2)))
  | (a, .gen g, b) => cl D Sc ν _ _ [(a, g, b)]
  | (a, .lcup i, b) => plcL D Sc ν a b [] [up i, dn i] (etaP cs i (wt D ν b))
  | (a, .lcap i, b) => plcL D Sc ν a b [dn i, up i] [] (epsP cs i (wt D ν b))

/-- The 2-morphism `E_s 1_ν → E_t 1_ν` of a list of extended layers (`0` if they do not chain from
`s` to `t`). -/
def xev (ν : X) : (s t : List (Letter I)) → List (XLayer I) →
    ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t))
  | s, t, [] => cl D Sc ν s t []
  | s, t, x :: L => cl D Sc ν s (x.1 ++ x.2.1.dom ++ x.2.2) [] ≫ xlay cs ν x ≫
      xev ν (x.1 ++ x.2.1.cod ++ x.2.2) t L

theorem xev_nil (ν : X) (s t : List (Letter I)) : xev cs ν s t [] = cl D Sc ν s t [] := rfl

theorem xev_cons (ν : X) (s t : List (Letter I)) (x : XLayer I) (L : List (XLayer I)) :
    xev cs ν s t (x :: L) = cl D Sc ν s (x.1 ++ x.2.1.dom ++ x.2.2) [] ≫ xlay cs ν x ≫
      xev cs ν (x.1 ++ x.2.1.cod ++ x.2.2) t L := rfl

theorem xev_of_not {ν : X} {s t : List (Letter I)} {L : List (XLayer I)} (h : ¬ XChain s L t) :
    xev cs ν s t L = 0 := by
  induction L generalizing s with
  | nil => exact cl_of_not h
  | cons x L ih =>
    rw [xev_cons]
    by_cases hs : s = x.1 ++ x.2.1.dom ++ x.2.2
    · rw [ih (fun h' => h ⟨hs, h'⟩), Limits.comp_zero, Limits.comp_zero]
    · rw [cl_of_not (show ¬ SChain s [] _ from hs), Limits.zero_comp]

theorem xev_append {ν : X} {s r t : List (Letter I)} {L : List (XLayer I)} (M : List (XLayer I))
    (h : XChain s L r) : xev cs ν s t (L ++ M) = xev cs ν s r L ≫ xev cs ν r t M := by
  induction L generalizing s with
  | nil =>
    obtain rfl : s = r := h
    rw [List.nil_append, xev_nil, cl_nil, Category.id_comp]
  | cons x L ih =>
    rw [List.cons_append, xev_cons, xev_cons, ih h.2]
    simp only [Category.assoc]

theorem cl_nil_comp_xev {ν : X} {b c t : List (Letter I)} (L : List (XLayer I)) (h : b = c) :
    cl D Sc ν b c [] ≫ xev cs ν c t L = xev cs ν b t L := by
  subst h; rw [cl_nil, Category.id_comp]

/-- **Normal-form diagrams are diagrams of the extended language.** -/
@[simp] theorem xev_map_ofL (ν : X) (s t : List (Letter I)) (L : List (LayerData I)) :
    xev cs ν s t (L.map ofL) = cl D Sc ν s t L := by
  induction L generalizing s with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨a, g, b⟩ := x
    rw [List.map_cons, xev_cons, ih]
    change cl D Sc ν s (a ++ g.dom ++ b) [] ≫ cl D Sc ν (a ++ g.dom ++ b) (a ++ g.cod ++ b)
      [(a, g, b)] ≫ cl D Sc ν (a ++ g.cod ++ b) t L = _
    by_cases hs : s = a ++ g.dom ++ b
    · subst hs
      rw [cl_nil, Category.id_comp]
      by_cases hL : SChain (a ++ g.cod ++ b) L t
      · exact cl_comp (show SChain _ [(a, g, b)] _ from ⟨rfl, rfl⟩) hL
      · rw [cl_of_not hL, Limits.comp_zero, cl_of_not]
        exact fun h => hL h.2
    · rw [cl_of_not (show ¬ SChain s [] _ from hs), Limits.zero_comp, cl_of_not]
      exact fun h => hs h.1

theorem xev_single_gen (ν : X) (a b : List (Letter I)) (g : Shape I) :
    xev cs ν (a ++ g.dom ++ b) (a ++ g.cod ++ b) [(a, .gen g, b)] =
      cl D Sc ν (a ++ g.dom ++ b) (a ++ g.cod ++ b) [(a, g, b)] :=
  xev_map_ofL cs ν _ _ [(a, g, b)]

/-- A single extended layer. -/
theorem xev_single (ν : X) (x : XLayer I) :
    xev cs ν (x.1 ++ x.2.1.dom ++ x.2.2) (x.1 ++ x.2.1.cod ++ x.2.2) [x] = xlay cs ν x := by
  rw [xev_cons, xev_nil, cl_nil, cl_nil, Category.id_comp, Category.comp_id]

/-- An extended diagram followed by one more layer. -/
theorem xev_snoc (ν : X) {s : List (Letter I)} {L : List (XLayer I)} (x : XLayer I)
    (h : XChain s L (x.1 ++ x.2.1.dom ++ x.2.2)) :
    xev cs ν s (x.1 ++ x.2.1.cod ++ x.2.2) (L ++ [x]) =
      xev cs ν s (x.1 ++ x.2.1.dom ++ x.2.2) L ≫ xlay cs ν x := by
  rw [xev_append cs _ h, xev_single]

/-- One layer followed by an extended diagram. -/
theorem xev_cons_eq (ν : X) {t : List (Letter I)} (x : XLayer I) (L : List (XLayer I)) :
    xev cs ν (x.1 ++ x.2.1.dom ++ x.2.2) t (x :: L) =
      xlay cs ν x ≫ xev cs ν (x.1 ++ x.2.1.cod ++ x.2.2) t L := by
  rw [xev_cons, cl_nil, Category.id_comp]

/-! ## Placement of extended diagrams -/

/-- Placement of a single extended layer. -/
theorem plcL_xlay (μ : X) (u v : List (Letter I)) (x : XLayer I) :
    plcL D Sc μ u v _ _ (xlay cs (wt D μ v) x) =
      cl D Sc μ (u ++ (x.1 ++ x.2.1.dom ++ x.2.2) ++ v) ((u ++ x.1) ++ x.2.1.dom ++ (x.2.2 ++ v))
          [] ≫ xlay cs μ (xwhL u v x) ≫
        cl D Sc μ ((u ++ x.1) ++ x.2.1.cod ++ (x.2.2 ++ v)) (u ++ (x.1 ++ x.2.1.cod ++ x.2.2) ++ v)
          [] := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | gen g =>
    change plcL D Sc μ u v _ _ (cl D Sc (wt D μ v) _ _ [(a, g, b)]) =
      _ ≫ cl D Sc μ _ _ [(u ++ a, g, b ++ v)] ≫ _
    rw [plcL_cl, cl_cast _ (by simp) (by simp)]
    rfl
  | lcup i =>
    have E := plcL_nested μ u v a b (etaP_mem cs i (wt D (wt D μ v) b))
    simp only [regionCast_family (f := fun ν => etaP cs i ν)] at E
    exact eq_of_wordCast _ _ E
  | lcap i =>
    have E := plcL_nested μ u v a b (epsP_mem cs i (wt D (wt D μ v) b))
    simp only [regionCast_family (f := fun ν => epsP cs i ν)] at E
    exact eq_of_wordCast _ _ E

/-- **Placement of extended diagrams** acts by placing every layer. -/
theorem plcL_xev (μ : X) (u v : List (Letter I)) {s t : List (Letter I)} (L : List (XLayer I)) :
    plcL D Sc μ u v s t (xev cs (wt D μ v) s t L) =
      xev cs μ (u ++ s ++ v) (u ++ t ++ v) (L.map (xwhL u v)) := by
  induction L generalizing s with
  | nil => exact plcL_cl D Sc μ u v s t []
  | cons x L ih =>
    rw [xev_cons, plcL_comp, plcL_comp, ih, plcL_cl, plcL_xlay, List.map_cons, xev_cons]
    simp only [List.map_nil, Category.assoc]
    rw [cl_nil_comp_xev cs _ (by simp), ← Category.assoc,
      cl_nil_comp_nil (by simp)]
    rfl

/-! ## Lower terms -/

variable (D Sc) in
/-- **Lower terms**: the span of the extended diagrams `E_s 1_ν → E_t 1_ν` with at most `c`
crossings. -/
def LeL (ν : X) (s t : List (Letter I)) (c : ℕ) :
    Submodule k ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)) :=
  Submodule.span k {f | ∃ L, xcnt L ≤ c ∧ f = xev cs ν s t L}

theorem xev_mem_leL {ν : X} {s t : List (Letter I)} {c : ℕ} {L : List (XLayer I)}
    (h : xcnt L ≤ c) : xev cs ν s t L ∈ LeL D Sc cs ν s t c :=
  Submodule.subset_span ⟨L, h, rfl⟩

theorem cl_mem_leL {ν : X} {s t : List (Letter I)} {c : ℕ} {L : List (LayerData I)}
    (h : ccnt L ≤ c) : cl D Sc ν s t L ∈ LeL D Sc cs ν s t c := by
  rw [← xev_map_ofL cs]; exact xev_mem_leL cs (by simpa using h)

theorem leL_mono {ν : X} {s t : List (Letter I)} {c c' : ℕ} (h : c ≤ c') :
    LeL D Sc cs ν s t c ≤ LeL D Sc cs ν s t c' :=
  Submodule.span_mono fun _ ⟨L, hL, e⟩ => ⟨L, hL.trans h, e⟩

theorem xev_comp_xev_mem_leL {ν : X} {s t r : List (Letter I)} {c : ℕ} {L M : List (XLayer I)}
    (h : xcnt L + xcnt M ≤ c) : xev cs ν s t L ≫ xev cs ν t r M ∈ LeL D Sc cs ν s r c := by
  by_cases hL : XChain s L t
  · rw [← xev_append cs M hL]; exact xev_mem_leL cs (by rw [xcnt_append]; exact h)
  · rw [xev_of_not cs hL, Limits.zero_comp]; exact Submodule.zero_mem _

/-- Composition adds crossings. -/
theorem leL_comp {ν : X} {s t r : List (Letter I)} {c c' : ℕ}
    {f : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    {g : (pres D Sc).obj (ob D ν t) ⟶ (pres D Sc).obj (ob D ν r)}
    (hf : f ∈ LeL D Sc cs ν s t c) (hg : g ∈ LeL D Sc cs ν t r c') :
    f ≫ g ∈ LeL D Sc cs ν s r (c + c') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨M, hM, rfl⟩ := hg
      exact xev_comp_xev_mem_leL cs (by omega)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hx

theorem leL_comp_le {ν : X} {s t r : List (Letter I)} {c c' d : ℕ}
    {f : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    {g : (pres D Sc).obj (ob D ν t) ⟶ (pres D Sc).obj (ob D ν r)}
    (hf : f ∈ LeL D Sc cs ν s t c) (hg : g ∈ LeL D Sc cs ν t r c') (h : c + c' ≤ d) :
    f ≫ g ∈ LeL D Sc cs ν s r d :=
  leL_mono cs h (leL_comp cs hf hg)

/-- Placement between strands preserves crossing counts. -/
theorem plcL_leL {μ : X} {u v s t : List (Letter I)} {c : ℕ}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ LeL D Sc cs (wt D μ v) s t c) :
    plcL D Sc μ u v s t f ∈ LeL D Sc cs μ (u ++ s ++ v) (u ++ t ++ v) c := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    rw [plcL_xev]; exact xev_mem_leL cs (by rw [xcnt_map_xwhL]; exact hL)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- Rewriting in context (`ctxL`, with normal-form diagrams below and above) adds the crossings
of the context. -/
theorem ctxL_leL {μ : X} {s₀ t₀ : List (Letter I)} {pre post : List (LayerData I)}
    {u v s t : List (Letter I)} {c : ℕ}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ LeL D Sc cs (wt D μ v) s t c) :
    ctxL D Sc μ s₀ t₀ pre u v post s t f ∈ LeL D Sc cs μ s₀ t₀ (ccnt pre + c + ccnt post) := by
  show cl D Sc μ s₀ (u ++ s ++ v) pre ≫ plcL D Sc μ u v s t f ≫ cl D Sc μ (u ++ t ++ v) t₀ post ∈ _
  exact leL_comp_le cs (cl_mem_leL cs le_rfl)
    (leL_comp cs (plcL_leL cs hf) (cl_mem_leL cs le_rfl)) (by omega)

/-- **Every 2-morphism has finitely many crossings**: it lies in some `LeL μ s t c`. -/
theorem exists_mem_leL (μ : X) {s t : List (Letter I)}
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    ∃ c, f ∈ LeL D Sc cs μ s t c := by
  induction mem_span_cl μ f using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, -, rfl⟩ := hf
    exact ⟨ccnt L, cl_mem_leL cs le_rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨max c d, Submodule.add_mem _ (leL_mono cs (le_max_left c d) hc)
      (leL_mono cs (le_max_right c d) hd)⟩
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, Submodule.smul_mem _ a hc⟩

/-! ## Rewriting modulo lower terms -/

theorem leL_sub_trans {ν : X} {s t : List (Letter I)} {c : ℕ}
    {a b d : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    (h₁ : a - b ∈ LeL D Sc cs ν s t c) (h₂ : b - d ∈ LeL D Sc cs ν s t c) :
    a - d ∈ LeL D Sc cs ν s t c := by
  have := Submodule.add_mem _ h₁ h₂; rwa [sub_add_sub_cancel] at this

theorem leL_sub_of_eq {ν : X} {s t : List (Letter I)} {c : ℕ}
    {a b : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)} (h : a = b) :
    a - b ∈ LeL D Sc cs ν s t c := by
  rw [h, sub_self]; exact Submodule.zero_mem _

/-- An extended diagram in context, as a composite. -/
theorem xev_ctx (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (XLayer I)}
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) :
    xev cs μ s₀ t₀ (pre ++ A.map (xwhL u v) ++ post) =
      xev cs μ s₀ (u ++ s ++ v) pre ≫ plcL D Sc μ u v s t (xev cs (wt D μ v) s t A) ≫
        xev cs μ (u ++ t ++ v) t₀ post := by
  rw [List.append_assoc, xev_append cs _ hpre, xev_append cs _ (hA.whisk u v), plcL_xev]

/-- **A local relation modulo lower terms holds in any context.** -/
theorem xev_mod_ctx (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (XLayer I)} {c : ℕ}
    (E : xev cs (wt D μ v) s t A - xev cs (wt D μ v) s t B ∈ LeL D Sc cs (wt D μ v) s t c)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) (hB : XChain s B t) :
    xev cs μ s₀ t₀ (pre ++ A.map (xwhL u v) ++ post) -
        xev cs μ s₀ t₀ (pre ++ B.map (xwhL u v) ++ post) ∈
      LeL D Sc cs μ s₀ t₀ (xcnt pre + c + xcnt post) := by
  rw [xev_ctx cs μ pre post u v hpre hA, xev_ctx cs μ pre post u v hpre hB, ← Preadditive.comp_sub,
    ← Preadditive.sub_comp, ← map_sub]
  exact leL_comp_le cs (xev_mem_leL cs le_rfl)
    (leL_comp cs (plcL_leL cs E) (xev_mem_leL cs le_rfl)) (by omega)

/-- **A local diagram with few crossings, in any context.** -/
theorem xev_mem_ctx (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (XLayer I)} {c : ℕ}
    (E : xev cs (wt D μ v) s t A ∈ LeL D Sc cs (wt D μ v) s t c)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) :
    xev cs μ s₀ t₀ (pre ++ A.map (xwhL u v) ++ post) ∈
      LeL D Sc cs μ s₀ t₀ (xcnt pre + c + xcnt post) := by
  rw [xev_ctx cs μ pre post u v hpre hA]
  exact leL_comp_le cs (xev_mem_leL cs le_rfl)
    (leL_comp cs (plcL_leL cs E) (xev_mem_leL cs le_rfl)) (by omega)

theorem list_take_drop_split {α : Type*} (L : List α) (n l : ℕ) :
    L = L.take n ++ (L.drop n).take l ++ L.drop (n + l) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- **A local relation modulo lower terms, at a position**: the layers `n, …, n + |A| - 1` of `L`
are `A` placed between `u` and `v`. -/
theorem xev_mod_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (XLayer I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (XLayer I)} {c : ℕ}
    (E : xev cs (wt D μ v) s t A - xev cs (wt D μ v) s t B ∈ LeL D Sc cs (wt D μ v) s t c)
    (hpre : XChain s₀ (L.take n) (u ++ s ++ v)) (hA : XChain s A t) (hB : XChain s B t)
    (hL : (L.drop n).take A.length = A.map (xwhL u v)) :
    xev cs μ s₀ t₀ L -
        xev cs μ s₀ t₀ (L.take n ++ B.map (xwhL u v) ++ L.drop (n + A.length)) ∈
      LeL D Sc cs μ s₀ t₀ (xcnt (L.take n) + c + xcnt (L.drop (n + A.length))) := by
  have e : L = L.take n ++ A.map (xwhL u v) ++ L.drop (n + A.length) := by
    rw [← hL]; exact list_take_drop_split L n A.length
  have h := xev_mod_ctx cs (t₀ := t₀) μ (L.take n) (L.drop (n + A.length)) u v E hpre hA hB
  rw [← e] at h
  exact h

/-! ## The leftward cup and cap -/

theorem plcL_nil_cl (ν : X) (s t : List (Letter I)) (L : List (LayerData I)) :
    plcL D Sc ν [] [] s t (cl D Sc (wt D ν []) s t L) =
      cl D Sc ν ([] ++ s ++ []) ([] ++ t ++ []) L := by
  rw [plcL_cl]; congr 1; induction L <;> simp_all

theorem plcL_nil_cup {ν : X} {i : I} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [up i, dn i])}
    (hf : f ∈ homPar D Sc ν [] [up i, dn i] p) : plcL D Sc ν [] [] [] [up i, dn i] f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, -, -, rfl⟩ := hf
    exact plcL_nil_cl ν [] [up i, dn i] L
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem plcL_nil_cap {ν : X} {i : I} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D ν [dn i, up i]) ⟶ (pres D Sc).obj (ob D ν [])}
    (hf : f ∈ homPar D Sc ν [dn i, up i] [] p) : plcL D Sc ν [] [] [dn i, up i] [] f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, -, -, rfl⟩ := hf
    exact plcL_nil_cl ν [dn i, up i] [] L
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/-- `η'` is the extended layer `lcup`. -/
theorem xev_lcup (ν : X) (i : I) : xev cs ν [] [up i, dn i] [([], .lcup i, [])] = etaP cs i ν := by
  exact (xev_single cs ν ([], .lcup i, [])).trans (plcL_nil_cup (etaP_mem cs i ν))

/-- `ε'` is the extended layer `lcap`. -/
theorem xev_lcap (ν : X) (i : I) : xev cs ν [dn i, up i] [] [([], .lcap i, [])] = epsP cs i ν := by
  exact (xev_single cs ν ([], .lcap i, [])).trans (plcL_nil_cap (epsP_mem cs i ν))

theorem etaP_mem_leL (ν : X) (i : I) (c : ℕ) : etaP cs i ν ∈ LeL D Sc cs ν [] [up i, dn i] c := by
  rw [← xev_lcup]; exact xev_mem_leL cs (by simp [XShape.isCross])

theorem epsP_mem_leL (ν : X) (i : I) (c : ℕ) : epsP cs i ν ∈ LeL D Sc cs ν [dn i, up i] [] c := by
  rw [← xev_lcap]; exact xev_mem_leL cs (by simp [XShape.isCross])

/-- `η'` placed between strands is the extended layer `lcup`. -/
theorem plcL_etaP_mem_leL (μ : X) (u v : List (Letter I)) (i : I) (c : ℕ) :
    plcL D Sc μ u v [] [up i, dn i] (etaP cs i (wt D μ v)) ∈
      LeL D Sc cs μ (u ++ [] ++ v) (u ++ [up i, dn i] ++ v) c :=
  plcL_leL cs (etaP_mem_leL cs _ i c)

/-- `ε'` placed between strands is the extended layer `lcap`. -/
theorem plcL_epsP_mem_leL (μ : X) (u v : List (Letter I)) (i : I) (c : ℕ) :
    plcL D Sc μ u v [dn i, up i] [] (epsP cs i (wt D μ v)) ∈
      LeL D Sc cs μ (u ++ [dn i, up i] ++ v) (u ++ [] ++ v) c :=
  plcL_leL cs (epsP_mem_leL cs _ i c)

end OddMath.SKM
