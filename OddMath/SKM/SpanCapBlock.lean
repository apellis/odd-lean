/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanLocal2

/-!
# The cap block: local moves

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. The cap push in the proof of KL III
Proposition 3.11 moves the cap block `capBlk S l d` (the strand `B = l` moves left across the
strands `S`, `d` dots on `A = l*`, the cap joining `A` and `B`) below a dot, crossing or cup. This
file records the local relations between the block and a move just below it, up to sign modulo
diagrams with fewer crossings (`XEq`, `OddMath.SKM.SpanLocal2`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem lmLc_mid (S₁ S₂ : List (Letter I)) (x b : Letter I) :
    lmLc (S₁ ++ x :: S₂) b = (lmLc S₂ b).map (xwhL (S₁ ++ [x]) []) ++
      (xCrL x b).map (xwhL S₁ S₂) ++ (lmLc S₁ b).map (xwhL [] (x :: S₂)) := by
  rw [lmLc_append, lmLc]
  simp

theorem xChain_capBlk' (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    XChain (flipL l :: (S ++ [l])) (capBlk S l d) S := by
  simpa using xChain_capBlk S l d

/-- **A dot on a strand of the block** passes the block, modulo lower terms: it slides through
the crossing with `B` ((3.1)–(3.6), (4.1), (4.2)) and commutes with the rest. -/
theorem capBlk_dotS (ν : X) (S₁ S₂ : List (Letter I)) (x l : Letter I) (d : ℕ) :
    XEq cs ν ([flipL l] ++ (S₁ ++ [x] ++ S₂) ++ [l]) (S₁ ++ [x] ++ S₂) (S₁.length + S₂.length)
      ((xDotL x).map (xwhL ([flipL l] ++ S₁) (S₂ ++ [l])) ++ capBlk (S₁ ++ [x] ++ S₂) l d)
      (capBlk (S₁ ++ [x] ++ S₂) l d ++ (xDotL x).map (xwhL S₁ S₂)) := by
  set A := flipL l
  -- step 1: the dot passes `lmLc S₂`
  refine XEq.trans (XEq.ichg cs [] ((xCrL x l).map (xwhL (A :: S₁) S₂) ++
      (lmLc S₁ l).map (xwhL [A] (x :: S₂)) ++
        (xDotsL A d).map (xwhL [] (l :: (S₁ ++ [x] ++ S₂))) ++
        (xCapL l).map (xwhL [] (S₁ ++ [x] ++ S₂)))
    (A :: S₁) [] (xChain_xDotL x) (xChain_lmLc S₂ l) (by simp) ?_ rfl) ?_
  · simp [capBlk, lmLc_mid, A]
  -- step 2: the dot slides through the crossing of `x` and `B`
  refine XEq.trans (XEq.at ((lmLc S₂ l).map (xwhL (A :: S₁ ++ [x]) []))
      ((lmLc S₁ l).map (xwhL [A] (x :: S₂)) ++
        (xDotsL A d).map (xwhL [] (l :: (S₁ ++ [x] ++ S₂))) ++
        (xCapL l).map (xwhL [] (S₁ ++ [x] ++ S₂))) (A :: S₁) S₂ (ds_left cs _ x l) ?_
      (by have h := ((xChain_xDotL x).whisk [] [l]).append (xChain_xCrL x l); simpa using h)
      (by have h := (xChain_xCrL x l).append ((xChain_xDotL x).whisk [l] []); simpa using h)
      ?_ rfl ?_) ?_
  · simpa using (xChain_lmLc S₂ l).whisk (A :: S₁ ++ [x]) []
  · simp
  · simp; omega
  -- step 3: the dot passes the rest of the block
  refine XEq.symm (XEq.ichg cs ((lmLc S₂ l).map (xwhL (A :: S₁ ++ [x]) []) ++
    (xCrL x l).map (xwhL (A :: S₁) S₂)) [] [] S₂ (xChain_capBlk' S₁ l d) (xChain_xDotL x) ?_ ?_ ?_)
  · refine (((xChain_lmLc S₂ l).whisk (A :: S₁ ++ [x]) []).app
      ((xChain_xCrL x l).whisk (A :: S₁) S₂) (by simp)).cast (by simp [A]) (by simp [A])
  · simp [capBlk, lmLc_mid, A]
  · simp [capBlk, A]

/-- A dot on the strand `b` moving left across `S` slides along it, modulo lower terms. -/
theorem lmLc_dot (ν : X) (b : Letter I) : ∀ S : List (Letter I),
    XEq cs ν (S ++ [b]) (b :: S) (S.length - 1) ((xDotL b).map (xwhL S []) ++ lmLc S b)
      (lmLc S b ++ (xDotL b).map (xwhL [] S))
  | [] => XEq.of_eq (by simp [lmLc])
  | [s] => by
    simpa [lmLc] using ds_right cs ν s b
  | s :: s' :: S => by
    have ih := lmLc_dot (wt D ν []) b (s' :: S)
    -- the dot slides along `lmLc (s' :: S) b`
    refine XEq.trans (XEq.at [] ((xCrL s b).map (xwhL [] (s' :: S))) [s] [] ih (by simp)
      ((xChain_xDotL b).whisk (s' :: S) [] |>.app (xChain_lmLc (s' :: S) b) (by simp)
        |>.cast (by simp) rfl)
      ((xChain_lmLc (s' :: S) b).app ((xChain_xDotL b).whisk [] (s' :: S)) (by simp)
        |>.cast rfl (by simp))
      (by simp [lmLc]) rfl ?_) ?_
    · simp
    -- the dot slides through the crossing of `s` and `b`
    refine XEq.trans (XEq.at ((lmLc (s' :: S) b).map (xwhL [s] [])) [] [] (s' :: S)
      (ds_right cs _ s b)
      ((xChain_lmLc (s' :: S) b).whisk [s] [] |>.cast (by simp) (by simp))
      ((xChain_xDotL b).whisk [s] [] |>.app (xChain_xCrL s b) (by simp))
      ((xChain_xCrL s b).app ((xChain_xDotL b).whisk [] [s]) (by simp))
      (by simp) rfl ?_) ?_
    · simp
    exact XEq.of_eq (by simp [lmLc])

theorem xDotsL_succ' (l : Letter I) (d : ℕ) : xDotsL l (d + 1) = xDotsL l d ++ xDotL l := by
  simp [xDotsL, List.replicate_succ']

/-- **A dot on `B` passes the strands of the block**, modulo lower terms: it arrives just below
the cap. -/
theorem capBlk_dotB (ν : X) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    XEq cs ν ([flipL l] ++ S ++ [l]) S (S.length - 1)
      ((xDotL l).map (xwhL ([flipL l] ++ S) []) ++ capBlk S l d)
      ((lmLc S l).map (xwhL [flipL l] []) ++ ((xDotL l).map (xwhL [flipL l] []) ++
        (xDotsL (flipL l) d).map (xwhL [] [l]) ++ xCapL l).map (xwhL [] S)) := by
  refine XEq.at [] ((xDotsL (flipL l) d).map (xwhL [] (l :: S)) ++ (xCapL l).map (xwhL [] S))
    [flipL l] [] (lmLc_dot cs _ l S) (by simp)
    ((xChain_xDotL l).whisk S [] |>.app (xChain_lmLc S l) (by simp) |>.cast (by simp) rfl)
    ((xChain_lmLc S l).app ((xChain_xDotL l).whisk [] S) (by simp) |>.cast rfl (by simp))
    (by simp [capBlk]) ?_ (by simp)
  simp

/-- **The dots below the cap**: a dot on `B` just below the cap moves to `A` ((2.3), (4.3)), up to
sign and a term with an odd bubble in the region of the cap. -/
theorem dotsCap_dotB (ν : X) (l : Letter I) (d : ℕ) : ∃ (p : ZMod 2) (r : k),
    xev cs ν [flipL l, l] [] ((xDotL l).map (xwhL [flipL l] []) ++
        (xDotsL (flipL l) d).map (xwhL [] [l]) ++ xCapL l) =
      zsign k p • xev cs ν [flipL l, l] [] ((xDotsL (flipL l) (d + 1)).map (xwhL [] [l]) ++
        xCapL l) +
      r • (xev cs ν [flipL l, l] [] ((xDotsL (flipL l) d).map (xwhL [] [l]) ++ xCapL l) ≫
        oddBubble cs l.2 ν) := by
  obtain ⟨q, hq⟩ := xev_ichg cs ν (S := [flipL l, l]) (T := []) [] (xCapL l) [] []
    (xChain_xDotsL (flipL l) d) (xChain_xDotL l) rfl
  obtain ⟨p, r, -, hpr⟩ := dotCap cs ν l
  have hD : XChain [flipL l, l] ((xDotsL (flipL l) d).map (xwhL [] [l])) [flipL l, l] := by
    simpa using (xChain_xDotsL (flipL l) d).whisk [] [l]
  have hD' : XChain [flipL l, l] ((xDotL (flipL l)).map (xwhL [] [l])) [flipL l, l] := by
    simpa using (xChain_xDotL (flipL l)).whisk [] [l]
  refine ⟨q + p, zsign k q * r, ?_⟩
  have e₁ : (xDotL l).map (xwhL [flipL l] []) ++ (xDotsL (flipL l) d).map (xwhL [] [l]) ++
      xCapL l = [] ++ (xDotL l).map (xwhL ([] ++ [flipL l]) []) ++
        (xDotsL (flipL l) d).map (xwhL [] ([l] ++ [])) ++ xCapL l := by simp
  have e₂ : [] ++ (xDotsL (flipL l) d).map (xwhL [] ([l] ++ [])) ++
      (xDotL l).map (xwhL ([] ++ [flipL l]) []) ++ xCapL l =
      (xDotsL (flipL l) d).map (xwhL [] [l]) ++ ((xDotL l).map (xwhL [flipL l] []) ++
        xCapL l) := by simp
  have hq' := congrArg (zsign k q • ·) hq
  simp only [smul_smul, zsign_mul_self', one_smul] at hq'
  rw [e₁, ← hq', e₂, xev_append cs _ hD, hpr, Preadditive.comp_add, Linear.comp_smul,
    Linear.comp_smul, ← xev_append cs _ hD, ← Category.assoc, ← xev_append cs _ hD, smul_add,
    smul_smul, smul_smul, ← zsign_add, ← List.append_assoc, ← List.map_append, ← xDotsL_succ']

end OddMath.SKM
