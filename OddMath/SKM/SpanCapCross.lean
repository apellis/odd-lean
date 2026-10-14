/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCapBlock

/-!
# The cap block and a crossing

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. These are the local relations used to
push the cap block `capBlk S l d` below a crossing, up to sign modulo diagrams with fewer crossings
(`XEq`): dots sliding through a crossing, a strand entering the block, the two-strand cancellations
(Reidemeister 2 and a curl), and Reidemeister 3 inside the block.

Two inputs enter as explicit hypotheses: Reidemeister 3 for every orientation of the three
strands (`R3Rel`), and the curl formed by a crossing followed by a cap (`CapCurlRel`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem XEq.congr {ν : X} {s t : List (Letter I)} {c : ℕ} {L₁ L₂ L₁' L₂' : List (XLayer I)}
    (hL : L₁ = L₂) (hL' : L₁' = L₂') (E : XEq cs ν s t c L₂ L₂') : XEq cs ν s t c L₁ L₁' :=
  hL ▸ hL' ▸ E

/-! ## Dots sliding through a crossing -/

/-- Dots on the right incoming strand of a crossing slide to its left outgoing strand. -/
theorem dsR_rep (ν : X) (a b : Letter I) : ∀ d : ℕ,
    XEq cs ν [a, b] [b, a] 0 ((xDotsL b d).map (xwhL [a] []) ++ xCrL a b)
      (xCrL a b ++ (xDotsL b d).map (xwhL [] [a]))
  | 0 => XEq.of_eq (by simp [xDotsL])
  | d + 1 => by
    have ih := dsR_rep (wt D ν []) a b d
    have hD : XChain [a, b] ((xDotsL b d).map (xwhL [a] [])) [a, b] := by
      simpa using (xChain_xDotsL b d).whisk [a] []
    have hD' : XChain [b, a] ((xDotsL b d).map (xwhL [] [a])) [b, a] := by
      simpa using (xChain_xDotsL b d).whisk [] [a]
    have h1 : XChain [a, b] ((xDotL b).map (xwhL [a] [])) [a, b] := by
      simpa using (xChain_xDotL b).whisk [a] []
    have h1' : XChain [b, a] ((xDotL b).map (xwhL [] [a])) [b, a] := by
      simpa using (xChain_xDotL b).whisk [] [a]
    refine XEq.trans (XEq.at ((xDotsL b d).map (xwhL [a] [])) [] [] [] (ds_right cs _ a b)
      (by simpa using hD) (h1.append (xChain_xCrL a b)) ((xChain_xCrL a b).append h1')
      (by simp [xDotsL_succ']) rfl (by simp)) ?_
    refine XEq.at [] ((xDotL b).map (xwhL [] [a])) [] [] ih (by simp)
      (hD.append (xChain_xCrL a b)) ((xChain_xCrL a b).append hD') (by simp) ?_ (by simp)
    simp [xDotsL_succ']

/-- Dots on the left incoming strand of a crossing slide to its right outgoing strand. -/
theorem dsL_rep (ν : X) (a b : Letter I) : ∀ d : ℕ,
    XEq cs ν [a, b] [b, a] 0 ((xDotsL a d).map (xwhL [] [b]) ++ xCrL a b)
      (xCrL a b ++ (xDotsL a d).map (xwhL [b] []))
  | 0 => XEq.of_eq (by simp [xDotsL])
  | d + 1 => by
    have ih := dsL_rep (wt D ν []) a b d
    have hD : XChain [a, b] ((xDotsL a d).map (xwhL [] [b])) [a, b] := by
      simpa using (xChain_xDotsL a d).whisk [] [b]
    have hD' : XChain [b, a] ((xDotsL a d).map (xwhL [b] [])) [b, a] := by
      simpa using (xChain_xDotsL a d).whisk [b] []
    have h1 : XChain [a, b] ((xDotL a).map (xwhL [] [b])) [a, b] := by
      simpa using (xChain_xDotL a).whisk [] [b]
    have h1' : XChain [b, a] ((xDotL a).map (xwhL [b] [])) [b, a] := by
      simpa using (xChain_xDotL a).whisk [b] []
    refine XEq.trans (XEq.at ((xDotsL a d).map (xwhL [] [b])) [] [] [] (ds_left cs _ a b)
      (by simpa using hD) (h1.append (xChain_xCrL a b)) ((xChain_xCrL a b).append h1')
      (by simp [xDotsL_succ']) rfl (by simp)) ?_
    refine XEq.at [] ((xDotL a).map (xwhL [b] [])) [] [] ih (by simp)
      (hD.append (xChain_xCrL a b)) ((xChain_xCrL a b).append hD') (by simp) ?_ (by simp)
    simp [xDotsL_succ']

/-! ## The dots of the block -/

/-- The dots on the leg `A` of the block may be placed below the strand `B` moving across `S`. -/
theorem capBlk_dots (ν : X) (S : List (Letter I)) (l : Letter I) (d c : ℕ) :
    XEq cs ν ([flipL l] ++ S ++ [l]) S c
      ((xDotsL (flipL l) d).map (xwhL [] (S ++ [l])) ++ capBlk S l 0) (capBlk S l d) :=
  XEq.ichg cs [] ((xCapL l).map (xwhL [] S)) [] [] (xChain_xDotsL (flipL l) d)
    (xChain_lmLc S l) (by simp) (by simp [capBlk, xDotsL]) (by simp [capBlk])

/-- `capBlk_dots` in context. -/
theorem capBlk_dots_at {ν : X} {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I))
    (P Q S : List (Letter I)) (l : Letter I) (d c : ℕ)
    (hpre : XChain s₀ pre (P ++ ([flipL l] ++ (S ++ [l])) ++ Q)) :
    XEq cs ν s₀ t₀ c
      (pre ++ ((xDotsL (flipL l) d).map (xwhL [] (S ++ [l])) ++ capBlk S l 0).map (xwhL P Q) ++
        post) (pre ++ (capBlk S l d).map (xwhL P Q) ++ post) :=
  XEq.ichg cs pre ((xCapL l).map (xwhL P (S ++ Q)) ++ post) P Q (xChain_xDotsL (flipL l) d)
    (xChain_lmLc S l) hpre (by simp [capBlk, xDotsL]) (by simp [capBlk])

/-! ## A strand entering the block -/

/-- A strand entering the block from the right joins it (exact). -/
theorem capBlk_enterR (S : List (Letter I)) (e l : Letter I) (d : ℕ) :
    (xCrL e l).map (xwhL ([flipL l] ++ S) []) ++ (capBlk S l d).map (xwhL [] [e]) =
      capBlk (S ++ [e]) l d := by
  simp [capBlk, lmLc_snoc]

/-- A strand entering the block from the left joins it, without dots on `A`, modulo lower terms:
it passes the strand `B` moving across `S`, then through the cap (pitchfork). -/
theorem capBlk_enterL0 (ν : X) (S : List (Letter I)) (e l : Letter I) :
    XEq cs ν ([flipL l, e] ++ S ++ [l]) (e :: S) S.length
      ((xCrL (flipL l) e).map (xwhL [] (S ++ [l])) ++ (capBlk S l 0).map (xwhL [e] []))
      (capBlk (e :: S) l 0) := by
  -- step 1: the crossing passes the strand `B` moving across `S`
  refine XEq.trans (XEq.ichg cs [] ((xCapL l).map (xwhL [e] S)) [] [] (xChain_xCrL (flipL l) e)
    (xChain_lmLc S l) (by simp) (by simp [capBlk, xDotsL]) rfl) ?_
  -- step 2: the pitchfork
  refine XEq.trans (XEq.at ((lmLc S l).map (xwhL ([] ++ [flipL l, e]) [])) [] [] S (capPF cs _ l e)
    ?_ ?_ ?_ ?_ rfl ?_) ?_
  · simpa using (xChain_lmLc S l).whisk [flipL l, e] []
  · exact ((xChain_xCrL (flipL l) e).whisk [] [l]).app ((xChain_xCapL l).whisk [e] []) (by simp)
  · exact ((xChain_xCrL e l).whisk [flipL l] []).app ((xChain_xCapL l).whisk [] [e]) (by simp)
  · simp
  · simp
  · exact XEq.of_eq (by simp [capBlk, lmLc, xDotsL])

/-- A strand entering the block from the left joins it, modulo lower terms. -/
theorem capBlk_enterL (ν : X) (S : List (Letter I)) (e l : Letter I) (d : ℕ) :
    XEq cs ν ([flipL l, e] ++ S ++ [l]) (e :: S) S.length
      ((xCrL (flipL l) e).map (xwhL [] (S ++ [l])) ++ (capBlk S l d).map (xwhL [e] []))
      (capBlk (e :: S) l d) := by
  have hX : XChain ([flipL l, e] ++ S ++ [l]) ((xCrL (flipL l) e).map (xwhL [] (S ++ [l]))) ([e, flipL l] ++ S ++ [l]) :=
    by simpa using (xChain_xCrL (flipL l) e).whisk [] (S ++ [l])
  -- step 1: the dots of the block are placed below
  refine XEq.trans (XEq.congr cs (by simp) rfl (XEq.symm (capBlk_dots_at cs (ν := ν)
    (t₀ := e :: S) ((xCrL (flipL l) e).map (xwhL [] (S ++ [l]))) [] [e] [] S l d S.length
    (by simpa using hX)))) ?_
  -- step 2: the dots pass the crossing
  refine XEq.trans (XEq.at [] ((capBlk S l 0).map (xwhL [e] [])) [] (S ++ [l])
    (XEq.symm (dsL_rep cs _ (flipL l) e d)) (by simp) ?_ ?_ (by simp) rfl (by simp)) ?_
  · exact (xChain_xCrL (flipL l) e).app ((xChain_xDotsL (flipL l) d).whisk [e] []) (by simp)
  · exact ((xChain_xDotsL (flipL l) d).whisk [] [e]).app (xChain_xCrL (flipL l) e) (by simp)
  -- step 3: the strand enters the block
  refine XEq.trans (XEq.at ((xDotsL (flipL l) d).map (xwhL [] (e :: S ++ [l]))) [] [] []
    (capBlk_enterL0 cs _ S e l) ?_ ?_ ?_ (by simp) rfl (by simp)) ?_
  · simpa using (xChain_xDotsL (flipL l) d).whisk [] (e :: S ++ [l])
  · exact hX.app ((xChain_capBlk S l 0).whisk [e] [] |>.cast rfl (by simp)) (by simp)
  · simpa using xChain_capBlk (e :: S) l 0
  -- step 4: the dots return to the block
  exact XEq.congr cs (by simp) (by simp) (capBlk_dots_at cs (ν := ν) [] [] [] [] (e :: S) l d
    S.length (by simp))

/-! ## Two-strand cancellations -/

/-- A crossing of the last strand of the block with `B` gives lower terms (Reidemeister 2). -/
theorem capBlk_sB (ν : X) (S : List (Letter I)) (s l : Letter I) (d : ℕ) :
    xev cs ν ([flipL l] ++ S ++ [l, s]) (S ++ [s])
        ((xCrL l s).map (xwhL ([flipL l] ++ S) []) ++ capBlk (S ++ [s]) l d) ∈
      LeL D Sc cs ν ([flipL l] ++ S ++ [l, s]) (S ++ [s]) S.length := by
  refine xev_low_at cs [] ((lmLc S l).map (xwhL [flipL l] [s]) ++
    (xDotsL (flipL l) d).map (xwhL [] (l :: (S ++ [s]))) ++ (xCapL l).map (xwhL [] (S ++ [s])))
    ([flipL l] ++ S) [] (r2_all cs _ l s) (by simp) ((xChain_xCrL l s).append (xChain_xCrL s l))
    ?_ (by simp)
  simp [capBlk, lmLc_snoc]

variable (D Sc) in
/-- **The curl of a crossing and a cap**: the strand `l` crossing `l*` and then capped off with
it gives lower terms. For `l` downward this is the curl of a leftward crossing and the cap `ε`,
which follows from the curl relations of Section 5 after rotating the leftward crossing. -/
def CapCurlRel : Prop :=
  ∀ (ν : X) (l : Letter I), xev cs ν [l, flipL l] [] (xCrL l (flipL l) ++ xCapL l) ∈
    LeL D Sc cs ν [l, flipL l] [] 0

/-- A crossing of `B` and `A` (no strands in the block) is a curl: lower terms. -/
theorem capBlk_AB (hC : CapCurlRel D Sc cs) (ν : X) (l : Letter I) (d : ℕ) :
    xev cs ν [l, flipL l] [] (xCrL l (flipL l) ++ capBlk [] l d) ∈
      LeL D Sc cs ν [l, flipL l] [] 0 := by
  have E := XEq.at (ν := ν) (s₀ := [l, flipL l]) (t₀ := []) (L := xCrL l (flipL l) ++ capBlk [] l d) [] (xCapL l) [] []
    (XEq.symm (dsR_rep cs _ l (flipL l) d)) (by simp)
    ((xChain_xCrL l (flipL l)).app ((xChain_xDotsL (flipL l) d).whisk [] [l]) (by simp))
    (((xChain_xDotsL (flipL l) d).whisk [l] []).app (xChain_xCrL l (flipL l)) (by simp))
    (by simp [capBlk, lmLc]) rfl (c := 0) (by simp)
  refine E.low (xev_low_at cs ((xDotsL (flipL l) d).map (xwhL [l] [])) [] [] [] (hC _ l) ?_
    ((xChain_xCrL l (flipL l)).append (xChain_xCapL l)) (by simp) (by simp))
  simpa using (xChain_xDotsL (flipL l) d).whisk [l] []

/-- A crossing of `A` with the first strand of the block, without dots on `A`: lower terms
(the strand passes `B`, then through the cap, then Reidemeister 2). -/
theorem capBlk_sA0 (ν : X) (s : Letter I) (S : List (Letter I)) (l : Letter I) :
    xev cs ν ([s, flipL l] ++ S ++ [l]) (s :: S)
        ((xCrL s (flipL l)).map (xwhL [] (S ++ [l])) ++ capBlk (s :: S) l 0) ∈
      LeL D Sc cs ν ([s, flipL l] ++ S ++ [l]) (s :: S) (S.length + 1) := by
  -- step 1: the crossing passes the strand `B` moving across `S`
  have E₁ := XEq.ichg cs (ν := ν) (S := [s, flipL l] ++ S ++ [l]) (T := s :: S) (c := S.length + 1)
    (L := (xCrL s (flipL l)).map (xwhL [] (S ++ [l])) ++ capBlk (s :: S) l 0) [] ((xCrL s l).map
      (xwhL [flipL l] S) ++ (xCapL l).map (xwhL [] (s :: S))) [] [] (xChain_xCrL s (flipL l)) (xChain_lmLc S l)
    (by simp) (by simp [capBlk, lmLc, xDotsL]) rfl
  refine E₁.low (xev_low_at cs ((lmLc S l).map (xwhL ([] ++ [s, flipL l]) [])) [] [] S (c₀ := 1) (s := [s, flipL l, l]) (t := [s])
    (A := (xCrL s (flipL l)).map (xwhL [] [l]) ++ (xCrL s l).map (xwhL [flipL l] []) ++
      (xCapL l).map (xwhL [] [s])) ?_ ?_ ?_ ?_ (by simp))
  · -- step 2: the pitchfork, then Reidemeister 2
    have hX := (xChain_xCrL s (flipL l)).whisk [] [l]
    have E₂ := XEq.at (ν := wt D ν S) (s₀ := [s, (flipL l), l]) (t₀ := [s]) (c := 1)
      (L := (xCrL s (flipL l)).map (xwhL [] [l]) ++ (xCrL s l).map (xwhL [flipL l] []) ++
        (xCapL l).map (xwhL [] [s])) ((xCrL s (flipL l)).map (xwhL [] [l])) [] [] []
      (XEq.symm (capPF cs _ l s)) (by simpa using hX)
      (((xChain_xCrL s l).whisk [flipL l] []).app ((xChain_xCapL l).whisk [] [s]) (by simp))
      (((xChain_xCrL (flipL l) s).whisk [] [l]).app ((xChain_xCapL l).whisk [s] []) (by simp))
      (by simp) rfl (by simp)
    refine E₂.low (xev_low_at cs [] ((xCapL l).map (xwhL [s] [])) [] [l] (r2_all cs _ s (flipL l))
      (by simp) ((xChain_xCrL s (flipL l)).append (xChain_xCrL (flipL l) s)) (by simp) (by simp))
  · simpa using (xChain_lmLc S l).whisk [s, flipL l] []
  · exact (((xChain_xCrL s (flipL l)).whisk [] [l]).app ((xChain_xCrL s l).whisk [flipL l] []) (by simp)).app
      ((xChain_xCapL l).whisk [] [s]) (by simp)
  · simp

/-- A crossing of `A` with the first strand of the block gives lower terms. -/
theorem capBlk_sA (ν : X) (s : Letter I) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    xev cs ν ([s, flipL l] ++ S ++ [l]) (s :: S)
        ((xCrL s (flipL l)).map (xwhL [] (S ++ [l])) ++ capBlk (s :: S) l d) ∈
      LeL D Sc cs ν ([s, flipL l] ++ S ++ [l]) (s :: S) (S.length + 1) := by
  have hX : XChain ([s, flipL l] ++ S ++ [l]) ((xCrL s (flipL l)).map (xwhL [] (S ++ [l]))) ([flipL l, s] ++ S ++ [l]) :=
    by simpa using (xChain_xCrL s (flipL l)).whisk [] (S ++ [l])
  -- step 1: the dots of the block are placed below
  refine (XEq.congr cs (by simp) rfl (XEq.symm (capBlk_dots_at cs (ν := ν) (t₀ := s :: S)
    ((xCrL s (flipL l)).map (xwhL [] (S ++ [l]))) [] [] [] (s :: S) l d (S.length + 1)
    (by simpa using hX)))).low ?_
  -- step 2: the dots pass the crossing
  refine (XEq.at [] (capBlk (s :: S) l 0) [] (S ++ [l]) (XEq.symm (dsR_rep cs _ s (flipL l) d))
    (by simp) ?_ ?_ (by simp) rfl (by simp)).low ?_
  · exact (xChain_xCrL s (flipL l)).app ((xChain_xDotsL (flipL l) d).whisk [] [s]) (by simp)
  · exact ((xChain_xDotsL (flipL l) d).whisk [s] []).app (xChain_xCrL s (flipL l)) (by simp)
  refine xev_low_at cs ((xDotsL (flipL l) d).map (xwhL [s] (S ++ [l]))) [] [] [] (capBlk_sA0 cs _ s S l)
    ?_ ?_ (by simp) (by simp)
  · simpa using (xChain_xDotsL (flipL l) d).whisk [s] (S ++ [l])
  · exact hX.app (xChain_capBlk (s :: S) l 0) (by simp)

/-! ## Reidemeister 3 inside the block -/

/-- The left side of Reidemeister 3: `a b c → b a c → b c a → c b a`. -/
def r3L (a b c : Letter I) : List (XLayer I) :=
  (xCrL a b).map (xwhL [] [c]) ++ (xCrL a c).map (xwhL [b] []) ++ (xCrL b c).map (xwhL [] [a])

/-- The right side of Reidemeister 3: `a b c → a c b → c a b → c b a`. -/
def r3R (a b c : Letter I) : List (XLayer I) :=
  (xCrL b c).map (xwhL [a] []) ++ (xCrL a c).map (xwhL [] [b]) ++ (xCrL a b).map (xwhL [c] [])

variable (D Sc) in
/-- **Reidemeister 3** for every orientation of the three strands, up to sign modulo diagrams
without crossings ((3.7)–(3.9), Lemma 3.3 and their rotations). -/
def R3Rel : Prop :=
  ∀ (ν : X) (a b c : Letter I), XEq cs ν [a, b, c] [c, b, a] 0 (r3L a b c) (r3R a b c)

theorem lmLc_pair (S₁ S₂ : List (Letter I)) (a b x : Letter I) :
    lmLc (S₁ ++ [a, b] ++ S₂) x = (lmLc S₂ x).map (xwhL (S₁ ++ [a, b]) []) ++
      (xCrL b x).map (xwhL (S₁ ++ [a]) S₂) ++ (xCrL a x).map (xwhL S₁ (b :: S₂)) ++
        (lmLc S₁ x).map (xwhL [] (a :: b :: S₂)) := by
  simp [lmLc_append, lmLc]

/-- **A crossing of two strands of the block** passes the block, modulo lower terms
(Reidemeister 3 with `B`). -/
theorem capBlk_crossS (hR : R3Rel D Sc cs) (ν : X) (S₁ S₂ : List (Letter I))
    (l₁ l₂ l : Letter I) (d : ℕ) :
    XEq cs ν ([flipL l] ++ (S₁ ++ [l₁, l₂] ++ S₂) ++ [l]) (S₁ ++ [l₂, l₁] ++ S₂)
      (S₁.length + S₂.length)
      ((xCrL l₁ l₂).map (xwhL ([flipL l] ++ S₁) (S₂ ++ [l])) ++ capBlk (S₁ ++ [l₂, l₁] ++ S₂) l d)
      (capBlk (S₁ ++ [l₁, l₂] ++ S₂) l d ++ (xCrL l₁ l₂).map (xwhL S₁ S₂)) := by
  set rest := (capBlk S₁ l d).map (xwhL [] (l₂ :: l₁ :: S₂))
  set pre := (lmLc S₂ l).map (xwhL (flipL l :: S₁ ++ [l₁, l₂]) [])
  have hpre : XChain ([flipL l] ++ (S₁ ++ [l₁, l₂] ++ S₂) ++ [l]) pre (flipL l :: S₁ ++ [l₁, l₂] ++ l :: S₂) :=
    by simpa [pre] using (xChain_lmLc S₂ l).whisk (flipL l :: S₁ ++ [l₁, l₂]) []
  -- step 1: the crossing passes `lmLc S₂`
  refine XEq.trans (XEq.ichg cs [] ((xCrL l₁ l).map (xwhL (flipL l :: S₁ ++ [l₂]) S₂) ++
    (xCrL l₂ l).map (xwhL (flipL l :: S₁) (l₁ :: S₂)) ++ rest) (flipL l :: S₁) [] (xChain_xCrL l₁ l₂)
    (xChain_lmLc S₂ l) (by simp) ?_ rfl) ?_
  · simp [rest, capBlk, lmLc_append, lmLc]
  -- step 2: Reidemeister 3 with `B`
  refine XEq.trans (XEq.at pre rest (flipL l :: S₁) S₂ (hR _ l₁ l₂ l) (by simpa using hpre) ?_ ?_ ?_ rfl
    ?_) ?_
  · exact (((xChain_xCrL l₁ l₂).whisk [] [l]).app ((xChain_xCrL l₁ l).whisk [l₂] []) (by simp)).app
      ((xChain_xCrL l₂ l).whisk [] [l₁]) (by simp)
  · exact (((xChain_xCrL l₂ l).whisk [l₁] []).app ((xChain_xCrL l₁ l).whisk [] [l₂]) (by simp)).app
      ((xChain_xCrL l₁ l₂).whisk [l] []) (by simp)
  · simp [pre, r3L]
  · simp [pre, rest]; omega
  -- step 3: the crossing passes the rest of the block
  refine XEq.symm (XEq.ichg cs (pre ++ (xCrL l₂ l).map (xwhL (flipL l :: S₁ ++ [l₁]) S₂) ++
    (xCrL l₁ l).map (xwhL (flipL l :: S₁) (l₂ :: S₂))) [] [] S₂ (xChain_capBlk' S₁ l d)
    (xChain_xCrL l₁ l₂) ?_ ?_ ?_)
  · refine ((hpre.app ((xChain_xCrL l₂ l).whisk (flipL l :: S₁ ++ [l₁]) S₂) (by simp)).app
      ((xChain_xCrL l₁ l).whisk (flipL l :: S₁) (l₂ :: S₂)) (by simp)).cast rfl (by simp)
  · simp [pre, capBlk, lmLc_append, lmLc]
  · simp [pre, rest, r3R]

end OddMath.SKM
