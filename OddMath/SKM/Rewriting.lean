/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Calculus

/-!
# Positional rewriting and block interchange for `𝔘(𝔤)`

A positional front end for `OddMath.SKM.Calculus`, following categorification-lean's even
`KL3.Rewriting`, with the Koszul signs of the super interchange law:

* `cl_congr_ctx`: a subdiagram may be replaced, in any context, by a scalar multiple of another
  with the same typing behaviour;
* `cl_swapLR_at`, `cl_swapRL_at`: the super interchange law for the layers `n` and `n + 1`;
* `cl_step_at`, `cl_stepL_at`: rewriting at a position;
* `cl_interchange_one`, `cl_interchange`: the super interchange law for blocks of layers, with the
  sign `(-1)^{|A||B|}` (`parsum`: the parity of a list of layers).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

variable (D) in
/-- The parity of a list of layers: the sum of the parities of its generators. -/
def parsum (L : List (LayerData I)) : ZMod 2 := (L.map fun x => x.2.1.parity D).sum

@[simp] theorem parsum_nil : parsum D ([] : List (LayerData I)) = 0 := rfl

@[simp] theorem parsum_cons (x : LayerData I) (L : List (LayerData I)) :
    parsum D (x :: L) = x.2.1.parity D + parsum D L := by
  simp [parsum]

theorem parsum_append (L M : List (LayerData I)) :
    parsum D (L ++ M) = parsum D L + parsum D M := by
  simp [parsum]

@[simp] theorem parsum_map_whL (u v : List (Letter I)) (L : List (LayerData I)) :
    parsum D (L.map (whL u v)) = parsum D L := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [ih, whL]

/-! ## Replacing a subdiagram in context -/

/-- A subdiagram `A` may be replaced by `c • B` in any context if `A` and `B` chain between the
same boundaries and `cl A = c • cl B` whenever they chain. -/
theorem cl_congr_ctx {μ : X} {A B : List (LayerData I)} (c : k)
    (hc : ∀ s t, SChain s A t → SChain s B t) (hc' : ∀ s t, SChain s B t → SChain s A t)
    (hd : ∀ s t, SChain s A t → cl D Sc μ s t A = c • cl D Sc μ s t B)
    (s₀ t₀ : List (Letter I)) (pre post : List (LayerData I)) :
    cl D Sc μ s₀ t₀ (pre ++ A ++ post) = c • cl D Sc μ s₀ t₀ (pre ++ B ++ post) := by
  by_cases h : SChain s₀ (pre ++ A ++ post) t₀
  · obtain ⟨b, h₁, h₂⟩ := SChain.split h
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    rw [← cl_comp h₁ h₂, ← cl_comp h₃ h₄, hd a b h₄, Linear.comp_smul, Linear.smul_comp,
      cl_comp h₃ (hc a b h₄), cl_comp (h₃.append (hc a b h₄)) h₂]
  · rw [cl_of_not h, cl_of_not, smul_zero]
    intro h'
    obtain ⟨b, h₁, h₂⟩ := SChain.split h'
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    exact h ((h₃.append (hc' a b h₄)).append h₂)

theorem list_split_at (L : List (LayerData I)) (n : ℕ) (x y : LayerData I)
    (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest) :
    L = L.take n ++ [x, y] ++ rest := by
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, ← hL,
    List.take_append_drop]

/-! ## The super interchange law at a position -/

/-- Exchange of the layers `x` (below) and `y` (above), the generator of `x` being to the left of
that of `y`. -/
def swapLR (x y : LayerData I) : List (LayerData I) :=
  [(x.1 ++ x.2.1.dom ++ y.1.drop (x.1.length + x.2.1.cod.length), y.2.1, y.2.2),
    (x.1, x.2.1, y.1.drop (x.1.length + x.2.1.cod.length) ++ y.2.1.cod ++ y.2.2)]

/-- Exchange of the layers `x` (below) and `y` (above), the generator of `x` being to the right
of that of `y`. -/
def swapRL (x y : LayerData I) : List (LayerData I) :=
  [(y.1, y.2.1, x.1.drop (y.1.length + y.2.1.dom.length) ++ x.2.1.dom ++ x.2.2),
    (y.1 ++ y.2.1.cod ++ x.1.drop (y.1.length + y.2.1.dom.length), x.2.1, x.2.2)]

theorem sChain_swap_iff (a m b : List (Letter I)) (g h : Shape I) (s t : List (Letter I)) :
    SChain s [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] t ↔
      SChain s [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] t := by
  simp only [sChain_cons, sChain_nil, List.append_assoc, true_and]

/-- **The super interchange law at the position `n`**: the layers `n` (generator on the left)
and `n + 1` (generator on the right) are exchanged, with the sign `(-1)^{|g||h|}`. -/
theorem cl_swapLR_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.2.2 = y.1.drop (x.1.length + x.2.1.cod.length) ++ y.2.1.dom ++ y.2.2)
    (hy : y.1 = x.1 ++ x.2.1.cod ++ y.1.drop (x.1.length + x.2.1.cod.length)) :
    cl D Sc μ s t L = zsign k (x.2.1.parity D * y.2.1.parity D) •
      cl D Sc μ s t (L.take n ++ swapLR x y ++ rest) := by
  rw [congrArg (cl D Sc μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨a, g, r⟩ := x
  obtain ⟨p, h, b⟩ := y
  simp only [swapLR] at hx hy ⊢
  generalize p.drop (a.length + g.cod.length) = m at hx hy ⊢
  subst hx hy
  exact cl_congr_ctx _ (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t => (sChain_swap_iff a m b g h s t).2) (fun s t _ => cl_swap μ s t a m b g h)
    s t _ _

/-- **The super interchange law at the position `n`**: the layers `n` (generator on the right)
and `n + 1` (generator on the left) are exchanged, with the sign `(-1)^{|g||h|}`. -/
theorem cl_swapRL_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.1 = y.1 ++ y.2.1.dom ++ x.1.drop (y.1.length + y.2.1.dom.length))
    (hy : y.2.2 = x.1.drop (y.1.length + y.2.1.dom.length) ++ x.2.1.cod ++ x.2.2) :
    cl D Sc μ s t L = zsign k (y.2.1.parity D * x.2.1.parity D) •
      cl D Sc μ s t (L.take n ++ swapRL x y ++ rest) := by
  rw [congrArg (cl D Sc μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨p, h, b⟩ := x
  obtain ⟨a, g, r⟩ := y
  simp only [swapRL] at hx hy ⊢
  generalize p.drop (a.length + g.dom.length) = m at hx hy ⊢
  subst hx hy
  have hsq : zsign k (g.parity D * h.parity D) * zsign k (g.parity D * h.parity D) = 1 := by
    rw [← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero]
  refine cl_congr_ctx _ (fun s t => (sChain_swap_iff a m b g h s t).2)
    (fun s t => (sChain_swap_iff a m b g h s t).1) (fun s t _ => ?_) s t _ _
  rw [cl_swap μ s t a m b g h, smul_smul, hsq, one_smul]

/-- The super interchange law for two adjacent layers in any context. -/
theorem cl_swap_ctx {μ : X} (S T : List (Letter I)) (pre post : List (LayerData I))
    (a m b : List (Letter I)) (g h : Shape I) :
    cl D Sc μ S T (pre ++ [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] ++ post) =
      zsign k (g.parity D * h.parity D) •
        cl D Sc μ S T (pre ++ [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] ++ post) :=
  cl_congr_ctx _ (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t => (sChain_swap_iff a m b g h s t).2) (fun s t _ => cl_swap μ s t a m b g h) S T pre post

/-- The super interchange law for two adjacent layers in any context, the right generator
first. -/
theorem cl_swap_ctx' {μ : X} (S T : List (Letter I)) (pre post : List (LayerData I))
    (a m b : List (Letter I)) (g h : Shape I) :
    cl D Sc μ S T (pre ++ [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] ++ post) =
      zsign k (g.parity D * h.parity D) •
        cl D Sc μ S T (pre ++ [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] ++ post) := by
  rw [cl_swap_ctx, smul_smul, ← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul,
    zsign_zero, one_smul]

/-! ## Local rewriting at a position -/

theorem list_split_at' (L : List (LayerData I)) (n l : ℕ) :
    L = L.take n ++ (L.drop n).take l ++ L.drop (n + l) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- **One step of a certificate chain at a position.** -/
theorem cl_step_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)}
    (E : cl D Sc (wt D μ v) s t A = cl D Sc (wt D μ v) s t B)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    cl D Sc μ s₀ t₀ L =
      cl D Sc μ s₀ t₀ (L.take n ++ B.map (whL u v) ++ L.drop (n + A.length)) :=
  cl_step μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length) rfl

/-- One step of a certificate chain at a position, with a linear combination on the right. -/
theorem cl_stepL_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)}
    {F : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (E : cl D Sc (wt D μ v) s t A = F)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    cl D Sc μ s₀ t₀ L = ctxL D Sc μ s₀ t₀ (L.take n) u v (L.drop (n + A.length)) s t F :=
  cl_stepL μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length)

/-! ## The super interchange law for blocks of layers -/

/-- A layer `(a, g, b)` on the left slides past a list of layers `B` on the strands to its right,
with the sign `(-1)^{|g||B|}`. -/
theorem cl_interchange_one {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    (a b : List (Letter I)) (g : Shape I) {t₀ t₁ : List (Letter I)} {B : List (LayerData I)}
    (hB : SChain t₀ B t₁) :
    cl D Sc μ S T (pre ++ [(a, g, b ++ t₀)] ++ B.map (whL (a ++ g.cod ++ b) []) ++ post) =
      zsign k (g.parity D * parsum D B) •
        cl D Sc μ S T (pre ++ B.map (whL (a ++ g.dom ++ b) []) ++ [(a, g, b ++ t₁)] ++ post) := by
  induction B generalizing pre t₀ with
  | nil =>
    cases hB
    simp [zsign_zero]
  | cons y B ih =>
    obtain ⟨c, h, d⟩ := y
    obtain ⟨rfl, hB'⟩ := hB
    have e₁ : pre ++ [(a, g, b ++ (c ++ h.dom ++ d))] ++
        List.map (whL (a ++ g.cod ++ b) []) ((c, h, d) :: B) ++ post =
        pre ++ [(a, g, (b ++ c) ++ h.dom ++ d), (a ++ g.cod ++ (b ++ c), h, d)] ++
          (List.map (whL (a ++ g.cod ++ b) []) B ++ post) := by
      simp [whL, List.append_assoc]
    have e₂ : pre ++ [(a ++ g.dom ++ (b ++ c), h, d), (a, g, (b ++ c) ++ h.cod ++ d)] ++
        (List.map (whL (a ++ g.cod ++ b) []) B ++ post) =
        (pre ++ [(a ++ g.dom ++ b ++ c, h, d)]) ++ [(a, g, b ++ (c ++ h.cod ++ d))] ++
          List.map (whL (a ++ g.cod ++ b) []) B ++ post := by
      simp [List.append_assoc]
    rw [e₁, cl_congr_ctx _ (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).1)
      (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).2)
      (fun s t _ => cl_swap μ s t a (b ++ c) d g h) S T pre _, e₂, ih _ hB', smul_smul,
      ← zsign_add, parsum_cons, mul_add]
    congr 1
    simp [whL, List.append_assoc]

/-- **The super interchange law for blocks of layers**: a diagram `A` (from `s` to `s'`) on the
left and a diagram `B` (from `t` to `t'`) on the right can be exchanged, in any context, with the
sign `(-1)^{|A||B|}`. -/
theorem cl_interchange {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    {s s' t t' : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A s')
    (hB : SChain t B t') :
    cl D Sc μ S T (pre ++ A.map (whL [] t) ++ B.map (whL s' []) ++ post) =
      zsign k (parsum D A * parsum D B) •
        cl D Sc μ S T (pre ++ B.map (whL s []) ++ A.map (whL [] t') ++ post) := by
  induction A generalizing pre s with
  | nil =>
    cases hA
    simp [zsign_zero]
  | cons x A ih =>
    obtain ⟨a, g, b⟩ := x
    obtain ⟨rfl, hA'⟩ := hA
    have e₁ : pre ++ List.map (whL [] t) ((a, g, b) :: A) ++ B.map (whL s' []) ++ post =
        (pre ++ [(a, g, b ++ t)]) ++ A.map (whL [] t) ++ B.map (whL s' []) ++ post := by
      simp [whL, List.append_assoc]
    have e₂ : (pre ++ [(a, g, b ++ t)]) ++ B.map (whL (a ++ g.cod ++ b) []) ++
        A.map (whL [] t') ++ post =
        pre ++ [(a, g, b ++ t)] ++ B.map (whL (a ++ g.cod ++ b) []) ++
          (A.map (whL [] t') ++ post) := by
      simp [List.append_assoc]
    rw [e₁, ih _ hA', e₂, cl_interchange_one _ _ a b g hB, smul_smul, ← zsign_add,
      parsum_cons, add_mul]
    congr 1
    · ring
    · simp [whL, List.append_assoc]

end OddMath.SKM
