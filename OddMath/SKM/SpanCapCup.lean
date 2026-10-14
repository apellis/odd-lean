/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCapCross
import OddMath.SKM.ChevalleyLeft

/-!
# The cap block and a cup

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. These are the local relations used to
push the cap block `capBlk S l d` below a cup: the pitchfork of a strand through a cup, the
zigzags ((1.10), (6.6)), the curls formed by a cup creating a leg of the cap, and the closed bubble
formed by a cup creating both legs ((2.3)).

The curl formed by a cup followed by the crossing of its two legs enters as the explicit
hypothesis `CupCurlRel`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Pitchforks through a cup -/

theorem xev_lcup_at (ν : X) (u v : List (Letter I)) (i : I) :
    xev cs ν (u ++ [] ++ v) (u ++ [up i, dn i] ++ v) [(u, .lcup i, v)] = cupAt cs i ν u v :=
  xev_single cs ν (u, .lcup i, v)

/-- **A strand passes below a cup** of either orientation: the cup `xCupL x` to the left of the
strand `m`, followed by `m` crossing its right leg, equals the cup to the right of `m`, preceded
by `m` crossing its left leg ((2.4), (2.5), Proposition 7.2 (7.5), (7.6)). -/
theorem cupPF (ν : X) (x m : Letter I) :
    XEq cs ν [m] [x, m, flipL x] 0
      ((xCupL x).map (xwhL [] [m]) ++ (xCrL (flipL x) m).map (xwhL [x] []))
      ((xCupL x).map (xwhL [m] []) ++ (xCrL m x).map (xwhL [] [flipL x])) := by
  obtain ⟨_ | _, i⟩ := x <;> obtain ⟨_ | _, j⟩ := m <;>
    simp only [flipL, Bool.not_false, Bool.not_true]
  · -- the rightward cup and a downward strand, (2.5)
    refine XEq.of_cl (A := [([], Shape.cup i, [dn j])] ++ (sigmaL j i).map (whL [dn i] []))
      (B := [([dn j], Shape.cup i, [])] ++ (dcrossL j i).map (whL [] [up i])) ?_ ?_ 0 ?_
    · simp only [xCupL_dn, xCrL_up_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · simp only [xCupL_dn, xCrL_dn_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · rw [eq_2_5_a, zsign_zero, one_smul, sub_self]; exact Submodule.zero_mem _
  · -- the rightward cup and an upward strand, (2.4)
    refine XEq.of_cl (A := [([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])])
      (B := [([up j], Shape.cup i, [])] ++ (sigmaL i j).map (whL [] [up i])) ?_ ?_ 0 ?_
    · rfl
    · simp only [xCupL_dn, xCrL_up_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · rw [eq_2_4_b, zsign_zero, one_smul, sub_self]; exact Submodule.zero_mem _
  · -- the leftward cup and a downward strand, (7.6)
    have hA : SChain [up i, dn i, dn j] ((dcrossL i j).map (whL [up i] [])) [up i, dn j, dn i] :=
      (sChain_dcrossL i j).wh [up i] [] rfl rfl
    have hB : SChain [dn j, up i, dn i] ((lcrossL j i).map (whL [] [dn i])) [up i, dn j, dn i] :=
      (sChain_lcrossL j i).wh [] [dn i] rfl rfl
    have e₁ : (xCupL (up i)).map (xwhL [] [dn j]) ++ (xCrL (dn i) (dn j)).map (xwhL [up i] []) =
        [([], .lcup i, [dn j])] ++ ((dcrossL i j).map (whL [up i] [])).map ofL := by
      simp only [xCrL_dn_dn, xCupL_up, map_xwhL_map_ofL]; rfl
    have e₂ : (xCupL (up i)).map (xwhL [dn j] []) ++ (xCrL (dn j) (up i)).map (xwhL [] [dn i]) =
        [([dn j], .lcup i, [])] ++ ((lcrossL j i).map (whL [] [dn i])).map ofL := by
      simp only [xCrL_dn_up, xCupL_up]; rfl
    refine ⟨D.parity i * D.parity j, ?_⟩
    rw [e₁, e₂, xev_append cs _ (show XChain [dn j] [([], .lcup i, [dn j])] [up i, dn i, dn j]
        from ⟨rfl, rfl⟩), xev_append cs _ (show XChain [dn j] [([dn j], .lcup i, [])]
        [dn j, up i, dn i] from ⟨rfl, rfl⟩), xev_map_ofL, xev_map_ofL,
      show xev cs ν [dn j] [up i, dn i, dn j] [([], .lcup i, [dn j])] = cupAt cs i ν [] [dn j] from
        xev_lcup_at cs ν [] [dn j] i,
      show xev cs ν [dn j] [dn j, up i, dn i] [([dn j], .lcup i, [])] = cupAt cs i ν [dn j] [] from
        xev_lcup_at cs ν [dn j] [] i]
    have E := eq_7_6_a cs i j ν
    unfold pdcupL pdcupR at E
    rw [E, sub_self]; exact Submodule.zero_mem _
  · -- the leftward cup and an upward strand, (7.5)
    refine XEq.symm (XEq.of_smul 0 ?_)
    rw [zsign_zero, one_smul]
    exact pitchfork_cup cs ν i j

/-! ## Zigzags -/

/-- The zigzag with the cup on the left ((1.10), (6.6)), up to sign. -/
theorem zigL (ν : X) (l : Letter I) : ∃ p : ZMod 2,
    xev cs ν [l] [l] ((xCupL l).map (xwhL [] [l]) ++ (xCapL l).map (xwhL [l] [])) =
      zsign k p • 𝟙 _ := by
  obtain ⟨_ | _, i⟩ := l
  · refine ⟨0, ?_⟩
    rw [zsign_zero, one_smul, show (xCupL (dn i)).map (xwhL [] [dn i]) ++
      (xCapL (dn i)).map (xwhL [dn i] []) =
        [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])].map ofL from rfl, xev_map_ofL,
      cl_zigF, cl_nil]
  · refine ⟨ipar D i ν, ?_⟩
    rw [← eq_6_6_a cs i ν]
    change xev cs ν [up i] [up i] ([([], .lcup i, [up i])] ++ [([up i], .lcap i, [])]) = _
    rw [xev_append cs _ (show XChain [up i] [([], .lcup i, [up i])] [up i, dn i, up i] from
      ⟨rfl, rfl⟩), show xev cs ν [up i] [up i, dn i, up i] [([], .lcup i, [up i])] = leta cs i ν
        from xev_single cs ν ([], .lcup i, [up i]), show xev cs ν [up i, dn i, up i] [up i] [([up i], .lcap i, [])] =
          reps cs i ν from xev_single cs ν ([up i], .lcap i, [])]

/-- The zigzag with the cup on the right ((1.10), (6.6)), up to sign. -/
theorem zigR (ν : X) (l : Letter I) : ∃ p : ZMod 2,
    xev cs ν [flipL l] [flipL l]
        ((xCupL l).map (xwhL [flipL l] []) ++ (xCapL l).map (xwhL [] [flipL l])) =
      zsign k p • 𝟙 _ := by
  obtain ⟨_ | _, i⟩ := l
  · refine ⟨0, ?_⟩
    change xev cs ν [up i] [up i] ([([up i], Shape.cup i, []), ([], Shape.cap i, [up i])].map ofL) =
      _
    rw [zsign_zero, one_smul, xev_map_ofL, cl_zigE, cl_nil]
    rfl
  · refine ⟨0, ?_⟩
    change xev cs ν [dn i] [dn i] ([([dn i], .lcup i, [])] ++ [([], .lcap i, [dn i])]) =
      zsign k 0 • 𝟙 ((pres D Sc).obj (ob D ν [dn i]))
    rw [zsign_zero, one_smul, ← eq_6_6_b cs i ν, xev_append cs _ (show XChain [dn i]
      [([dn i], .lcup i, [])] [dn i, up i, dn i] from ⟨rfl, rfl⟩),
      show xev cs ν [dn i] [dn i, up i, dn i] [([dn i], .lcup i, [])] = retaF cs i ν
        from xev_single cs ν ([dn i], .lcup i, []),
      show xev cs ν [dn i, up i, dn i] [dn i] [([], .lcap i, [dn i])] = lepsF cs i ν
        from xev_single cs ν ([], .lcap i, [dn i])]

/-! ## A cup creating `A`: the zigzag -/

/-- A cup creating a strand and `A` cancels the cap (zigzag): the block without dots becomes the
strand `B` moving left across `S`, up to sign. -/
theorem capBlk_cupAleft0 (ν : X) (S : List (Letter I)) (l : Letter I) : ∃ p : ZMod 2,
    xev cs ν (S ++ [l]) (l :: S)
        ((xCupL l).map (xwhL [] (S ++ [l])) ++ (capBlk S l 0).map (xwhL [l] [])) =
      zsign k p • xev cs ν (S ++ [l]) (l :: S) (lmLc S l) := by
  obtain ⟨p, hp⟩ := xev_ichg cs ν (S := S ++ [l]) (T := l :: S) [] ((xCapL l).map (xwhL [l] S))
    [] [] (xChain_xCupL l) (xChain_lmLc S l) (by simp)
  obtain ⟨q, hq⟩ := zigL cs (wt D ν S) l
  refine ⟨p + q, ?_⟩
  have e₁ : (xCupL l).map (xwhL [] (S ++ [l])) ++ (capBlk S l 0).map (xwhL [l] []) =
      [] ++ (xCupL l).map (xwhL [] ((S ++ [l]) ++ [])) ++
        (lmLc S l).map (xwhL ([] ++ [l, flipL l]) []) ++ (xCapL l).map (xwhL [l] S) := by
    simp [capBlk, xDotsL]
  have hZ : XChain [l] ((xCupL l).map (xwhL [] [l]) ++ (xCapL l).map (xwhL [l] [])) [l] :=
    ((xChain_xCupL l).whisk [] [l]).app ((xChain_xCapL l).whisk [l] []) (by simp)
  have e₂ := xev_ctx cs ν (s₀ := S ++ [l]) (t₀ := l :: S) (lmLc S l) [] [] S
    (by simpa using xChain_lmLc S l) hZ
  rw [e₁, hp, show [] ++ (lmLc S l).map (xwhL ([] ++ []) []) ++
      (xCupL l).map (xwhL [] ((l :: S) ++ [])) ++ (xCapL l).map (xwhL [l] S) =
      lmLc S l ++ ((xCupL l).map (xwhL [] [l]) ++ (xCapL l).map (xwhL [l] [])).map (xwhL [] S) ++
        [] by simp, e₂, hq, map_smul, plcL_id]
  erw [xev_nil, cl_nil]
  simp [zsign_add, smul_smul]

/-! ## Curls formed by a cup -/

variable (D Sc) in
/-- **The curl of a cup and a crossing**: a cup followed by the crossing of its two legs gives
lower terms. This is the curl relation of Section 5 for the leftward cup `η'`, and its rotation for
the rightward cup `η`. -/
def CupCurlRel : Prop :=
  ∀ (ν : X) (l : Letter I), xev cs ν [] [l, flipL l] (xCupL (flipL l) ++ xCrL (flipL l) l) ∈
    LeL D Sc cs ν [] [l, flipL l] 0

/-- A cup creating `A` and the first strand of the block, without dots on `A`, is a curl: lower
terms (the strand passes `B`, then the pitchfork, then the curl). -/
theorem capBlk_cupAs0 (hU : CupCurlRel D Sc cs) (ν : X) (S : List (Letter I)) (l : Letter I) :
    xev cs ν (S ++ [l]) (l :: S)
        ((xCupL (flipL l)).map (xwhL [] (S ++ [l])) ++ capBlk (l :: S) l 0) ∈
      LeL D Sc cs ν (S ++ [l]) (l :: S) S.length := by
  have hcup : XChain [] (xCupL (flipL l)) [flipL l, l] := by
    simpa using xChain_xCupL (flipL l)
  -- step 1: the cup passes the strand `B` moving across `S`
  have E₁ := XEq.ichg cs (ν := ν) (S := S ++ [l]) (T := l :: S) (c := S.length)
    (L := (xCupL (flipL l)).map (xwhL [] (S ++ [l])) ++ capBlk (l :: S) l 0) []
    ((xCrL l l).map (xwhL [flipL l] S) ++ (xCapL l).map (xwhL [] (l :: S))) [] [] hcup
    (xChain_lmLc S l) (by simp) (by simp [capBlk, lmLc, xDotsL]) rfl
  refine E₁.low (xev_low_at cs ((lmLc S l).map (xwhL ([] ++ []) [])) [] [] S (c₀ := 0)
    (s := [l]) (t := [l]) (A := (xCupL (flipL l)).map (xwhL [] [l]) ++
      (xCrL l l).map (xwhL [flipL l] []) ++ (xCapL l).map (xwhL [] [l])) ?_ ?_ ?_ ?_ (by simp))
  · -- step 2: the pitchfork, then the curl
    have hX := hcup.whisk [] [l]
    have E₂ := XEq.at (ν := wt D ν S) (s₀ := [l]) (t₀ := [l]) (c := 0)
      (L := (xCupL (flipL l)).map (xwhL [] [l]) ++ (xCrL l l).map (xwhL [flipL l] []) ++
        (xCapL l).map (xwhL [] [l])) ((xCupL (flipL l)).map (xwhL [] [l])) [] [] []
      (XEq.symm (capPF cs _ l l)) (by simpa using hX)
      (((xChain_xCrL l l).whisk [flipL l] []).app ((xChain_xCapL l).whisk [] [l]) (by simp))
      (((xChain_xCrL (flipL l) l).whisk [] [l]).app ((xChain_xCapL l).whisk [l] []) (by simp))
      (by simp) rfl (by simp)
    refine E₂.low (xev_low_at cs [] ((xCapL l).map (xwhL [l] [])) [] [l] (hU _ l) (by simp)
      (hcup.append (by simpa using xChain_xCrL (flipL l) l)) (by simp) (by simp))
  · simpa using xChain_lmLc S l
  · exact (((hcup.whisk [] [l]).app ((xChain_xCrL l l).whisk [flipL l] []) (by simp)).app
      ((xChain_xCapL l).whisk [] [l]) (by simp)).cast (by simp) (by simp)
  · simp

/-- A cup creating the last strand of the block and `B` is a curl: lower terms. -/
theorem capBlk_cupsB (hU : CupCurlRel D Sc cs) (ν : X) (S : List (Letter I)) (l : Letter I)
    (d : ℕ) :
    xev cs ν ([flipL l] ++ S) (S ++ [flipL l])
        ((xCupL (flipL l)).map (xwhL ([flipL l] ++ S) []) ++ capBlk (S ++ [flipL l]) l d) ∈
      LeL D Sc cs ν ([flipL l] ++ S) (S ++ [flipL l]) S.length := by
  refine xev_low_at cs [] ((lmLc S l).map (xwhL [flipL l] [flipL l]) ++
    (xDotsL (flipL l) d).map (xwhL [] (l :: (S ++ [flipL l]))) ++
      (xCapL l).map (xwhL [] (S ++ [flipL l]))) ([flipL l] ++ S) [] (hU _ l) (by simp)
    ((show XChain [] (xCupL (flipL l)) [flipL l, l] by simpa using xChain_xCupL (flipL l)).append
      (xChain_xCrL (flipL l) l)) ?_ (by simp)
  simp [capBlk, lmLc_snoc]

/-- A strand passing below both legs of a cup: lower terms (pitchfork, then Reidemeister 2). -/
theorem cupPF2 (ν : X) (x m : Letter I) :
    xev cs ν [m] [m, x, flipL x] ((xCupL x).map (xwhL [] [m]) ++
      (xCrL (flipL x) m).map (xwhL [x] []) ++ (xCrL x m).map (xwhL [] [flipL x])) ∈
      LeL D Sc cs ν [m] [m, x, flipL x] 1 := by
  have hcup := xChain_xCupL x
  refine (XEq.at (ν := ν) (s₀ := [m]) (t₀ := [m, x, flipL x]) (c := 1)
    (L := (xCupL x).map (xwhL [] [m]) ++ (xCrL (flipL x) m).map (xwhL [x] []) ++
      (xCrL x m).map (xwhL [] [flipL x])) [] ((xCrL x m).map
    (xwhL [] [flipL x])) [] [] (cupPF cs _ x m) (by simp)
    ((hcup.whisk [] [m]).app ((xChain_xCrL (flipL x) m).whisk [x] []) (by simp))
    ((hcup.whisk [m] []).app ((xChain_xCrL m x).whisk [] [flipL x]) (by simp)) (by simp) rfl
    (by simp)).low ?_
  refine xev_low_at cs ((xCupL x).map (xwhL [m] [])) [] [] [flipL x] (r2_all cs _ m x)
    (by simpa using hcup.whisk [m] []) ((xChain_xCrL m x).append (xChain_xCrL x m)) (by simp)
    (by simp)

/-- A cup creating two strands of the block gives lower terms. -/
theorem capBlk_cupSS (ν : X) (S₁ S₂ : List (Letter I)) (x l : Letter I) (d : ℕ) :
    xev cs ν ([flipL l] ++ (S₁ ++ S₂) ++ [l]) (S₁ ++ [x, flipL x] ++ S₂)
        ((xCupL x).map (xwhL ([flipL l] ++ S₁) (S₂ ++ [l])) ++
          capBlk (S₁ ++ [x, flipL x] ++ S₂) l d) ∈
      LeL D Sc cs ν ([flipL l] ++ (S₁ ++ S₂) ++ [l]) (S₁ ++ [x, flipL x] ++ S₂)
        (S₁.length + S₂.length + 1) := by
  set rest := (lmLc S₁ l).map (xwhL [flipL l] (x :: flipL x :: S₂)) ++
    (xDotsL (flipL l) d).map (xwhL [] (l :: (S₁ ++ [x, flipL x] ++ S₂))) ++
    (xCapL l).map (xwhL [] (S₁ ++ [x, flipL x] ++ S₂))
  -- step 1: the cup passes `lmLc S₂`
  have E₁ := XEq.ichg cs (ν := ν) (S := [flipL l] ++ (S₁ ++ S₂) ++ [l])
    (T := S₁ ++ [x, flipL x] ++ S₂) (c := S₁.length + S₂.length + 1)
    (L := (xCupL x).map (xwhL ([flipL l] ++ S₁) (S₂ ++ [l])) ++
      capBlk (S₁ ++ [x, flipL x] ++ S₂) l d) []
    ((xCrL (flipL x) l).map (xwhL (flipL l :: S₁ ++ [x]) S₂) ++
      (xCrL x l).map (xwhL (flipL l :: S₁) (flipL x :: S₂)) ++ rest) (flipL l :: S₁) []
    (xChain_xCupL x) (xChain_lmLc S₂ l) (by simp) (by simp [rest, capBlk, lmLc_append, lmLc]) rfl
  refine E₁.low (xev_low_at cs ((lmLc S₂ l).map (xwhL (flipL l :: S₁ ++ []) []))
    rest (flipL l :: S₁) S₂ (cupPF2 cs _ x l) ?_ ?_ ?_ ?_)
  · simpa using (xChain_lmLc S₂ l).whisk (flipL l :: S₁) []
  · exact (((xChain_xCupL x).whisk [] [l]).app ((xChain_xCrL (flipL x) l).whisk [x] [])
      (by simp)).app ((xChain_xCrL x l).whisk [] [flipL x]) (by simp)
  · simp
  · simp [rest]; omega

/-! ## A cup creating `B` and a strand to the right of the block -/

/-- A cup on the right of the block's strands, pushed below the strand moving left across them
(pitchforks): the strand `l*` of the cup moves right instead, modulo lower terms. -/
theorem cupThru (l : Letter I) : ∀ (S : List (Letter I)) (ν : X),
    XEq cs ν S (l :: S ++ [flipL l]) (S.length - 1)
      ((xCupL l).map (xwhL S []) ++ (lmLc S l).map (xwhL [] [flipL l]))
      ((xCupL l).map (xwhL [] S) ++ (lmRc (flipL l) S).map (xwhL [l] []))
  | [], ν => XEq.of_eq (by simp [lmLc, lmRc])
  | [s], ν => by
    simpa [lmLc, lmRc] using XEq.symm (cupPF cs ν l s)
  | s :: s' :: S, ν => by
    have ih := cupThru l (s' :: S) (wt D ν [])
    have hA := (xChain_xCupL l).whisk (s' :: S) []
    have hB := (xChain_xCupL l).whisk [] (s' :: S)
    -- step 1: the induction hypothesis
    refine XEq.trans (XEq.at [] ((xCrL s l).map (xwhL [] (s' :: S ++ [flipL l]))) [s] [] ih
      (by simp) ?_ ?_ (by simp [lmLc]) rfl (by simp)) ?_
    · exact hA.app ((xChain_lmLc (s' :: S) l).whisk [] [flipL l]) (by simp) |>.cast (by simp)
        (by simp)
    · exact hB.app ((xChain_lmRc (flipL l) (s' :: S)).whisk [l] []) (by simp) |>.cast (by simp)
        (by simp)
    -- step 2: the crossing of `s` and `l` passes the strand moving right
    refine XEq.trans (XEq.symm (XEq.ichg cs ((xCupL l).map (xwhL [s] (s' :: S))) [] [] []
      (xChain_xCrL s l) (xChain_lmRc (flipL l) (s' :: S)) ?_ rfl ?_)) ?_
    · simpa using (xChain_xCupL l).whisk [s] (s' :: S)
    · simp
    -- step 3: the pitchfork
    refine XEq.trans (XEq.at [] ((lmRc (flipL l) (s' :: S)).map (xwhL ([] ++ [l, s]) [])) []
      (s' :: S) (XEq.symm (cupPF cs _ l s)) (by simp) ?_ ?_ (by simp) rfl (by simp)) ?_
    · exact ((xChain_xCupL l).whisk [s] []).app ((xChain_xCrL s l).whisk [] [flipL l]) (by simp)
    · exact ((xChain_xCupL l).whisk [] [s]).app ((xChain_xCrL (flipL l) s).whisk [l] []) (by simp)
    exact XEq.of_eq (by simp [lmRc])

/-- A cup creating `B` and a strand to the right of the block, without dots on `A`, cancels the
cap (pitchforks, then the zigzag): the block becomes the strand `A` moving right across `S`. -/
theorem capBlk_cupBright0 (ν : X) (S : List (Letter I)) (l : Letter I) :
    XEq cs ν ([flipL l] ++ S) (S ++ [flipL l]) (S.length - 1)
      ((xCupL l).map (xwhL ([flipL l] ++ S) []) ++ (capBlk S l 0).map (xwhL [] [flipL l]))
      (lmRc (flipL l) S) := by
  have hcap : XChain [flipL l, l] (xCapL l) [] := xChain_xCapL l
  -- step 1: pitchforks
  refine XEq.trans (XEq.at [] ((xCapL l).map (xwhL [] (S ++ [flipL l]))) [flipL l] []
    (cupThru cs l S _) (by simp) ?_ ?_ (by simp [capBlk, xDotsL]) rfl (by simp)) ?_
  · exact ((xChain_xCupL l).whisk S []).app ((xChain_lmLc S l).whisk [] [flipL l]) (by simp)
      |>.cast (by simp) (by simp)
  · exact ((xChain_xCupL l).whisk [] S).app ((xChain_lmRc (flipL l) S).whisk [l] []) (by simp)
      |>.cast (by simp) (by simp)
  -- step 2: the strand moving right passes the cap
  refine XEq.trans (XEq.symm (XEq.ichg cs ((xCupL l).map (xwhL [flipL l] S)) [] [] []
    hcap (xChain_lmRc (flipL l) S) ?_ rfl (by simp))) ?_
  · simpa using (xChain_xCupL l).whisk [flipL l] S
  -- step 3: the zigzag
  obtain ⟨p, hp⟩ := zigR cs (wt D ν S) l
  refine XEq.of_smul p ?_
  have hZ : XChain [flipL l] ((xCupL l).map (xwhL [flipL l] []) ++
      (xCapL l).map (xwhL [] [flipL l])) [flipL l] :=
    ((xChain_xCupL l).whisk [flipL l] []).app (hcap.whisk [] [flipL l]) (by simp)
  have e := xev_ctx cs ν (s₀ := [flipL l] ++ S) (t₀ := S ++ [flipL l]) []
    (lmRc (flipL l) S) [] S (by simp) hZ
  refine (congrArg (xev cs ν ([flipL l] ++ S) (S ++ [flipL l])) (?_ : _ = [] ++
    ((xCupL l).map (xwhL [flipL l] []) ++ (xCapL l).map (xwhL [] [flipL l])).map (xwhL [] S) ++
      lmRc (flipL l) S)).trans ?_
  · simp
  rw [e, hp, map_smul, plcL_id]
  erw [xev_nil, cl_nil]
  simp

theorem mvLay_dotMv (d : ℕ) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) :
    mvLay (dotMv d u l v) = (xDotsL l d).map (xwhL u v) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show dotMv (d + 1) u l v = Mv.dot u l v :: dotMv d u l v from List.replicate_succ ..,
      mvLay_cons, ih]
    simp [xDotsL, List.replicate_succ, Mv.lay, Mv.loc, Mv.pre, Mv.post]

/-! ## A cup creating both legs of the cap: a bubble -/

theorem xDotsL_up (i : I) (d : ℕ) : xDotsL (up i) d = (dotsL [] i [] d).map ofL := by
  induction d with
  | zero => rfl
  | succ d ih => simp [xDotsL, dotsL, List.replicate_succ, xDotL_up] at ih ⊢; exact ⟨rfl, Or.inr rfl⟩

theorem xDotsL_dn (i : I) (d : ℕ) : xDotsL (dn i) d = (ddotsL i d).map ofL := by
  induction d with
  | zero => rfl
  | succ d ih => simp [xDotsL, ddotsL, List.replicate_succ, xDotL_dn] at ih ⊢

/-- **A cup creating `A` and `B`** (no strands in the block) closes a dotted bubble ((2.3)). -/
theorem cupBubble (ν : X) (l : Letter I) (d : ℕ) : ∃ (a : k)
    (β : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])), IsBubbleProd cs ν β ∧
      xev cs ν [] [] (xCupL (flipL l) ++ capBlk [] l d) = a • β := by
  obtain ⟨_ | _, i⟩ := l
  · -- a clockwise bubble
    refine ⟨1, bubL cs i ν d, by simpa using IsBubbleProd.bubL (cs := cs) (ν := ν) i d .id, ?_⟩
    have e : xCupL (flipL (dn i)) ++ capBlk [] (dn i) d =
        [([], .lcup i, [])] ++ (epsL i d).map ofL := by
      simp [capBlk, lmLc, xDotsL_up, epsL, xCupL_up, xCapL_dn]
      exact ⟨by simp [dotsL, List.map_replicate]; exact Or.inr rfl, rfl⟩
    rw [e, xev_append cs _ (show XChain [] [([], .lcup i, [])] [up i, dn i] from ⟨rfl, rfl⟩),
      xev_lcup, xev_map_ofL, one_smul, bubL]
    simp only [Int.natCast_nonneg, ↓reduceIte]
    rfl
  · -- a counterclockwise bubble
    refine ⟨zsign k (D.parity i * ((d / 2 : ℕ) : ZMod 2)), bubR cs i ν d,
      by simpa using IsBubbleProd.bubR (cs := cs) (ν := ν) i d .id, ?_⟩
    have e : xCupL (flipL (up i)) ++ capBlk [] (up i) d =
        ([([], Shape.cup i, [])] ++ (ddotsL i d).map (whL [] [up i])).map ofL ++
          [([], .lcap i, [])] := by
      simp [capBlk, lmLc, xDotsL_dn, xCupL_dn, xCapL_up]
      exact ⟨rfl, rfl⟩
    rw [e, xev_append cs _ (XChain.of_sChain (show SChain [] ([([], Shape.cup i, [])] ++
      (ddotsL i d).map (whL [] [up i])) [dn i, up i] from
        (show SChain [] [([], Shape.cup i, [])] [dn i, up i] by simp [Shape.dom, Shape.cod]).append
          (sChain_ddotsL_wh i d [] [up i]))), xev_map_ofL, xev_lcap, eq_2_3_a', bubR,
      Linear.smul_comp]
    simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
    congr 3
    simp [etaL, dotsL, List.map_replicate]
    exact Or.inr rfl

end OddMath.SKM
