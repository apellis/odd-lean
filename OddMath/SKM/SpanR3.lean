/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCurls
import OddMath.SKM.SpanCapsPushCup

/-!
# Reidemeister 3 for all orientations, and elimination of caps

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11.

The cap push needs Reidemeister 3 for every orientation of the three strands, up to sign modulo
diagrams without crossings (`R3Rel`). The braid relations of the paper give two orientations:
three upward strands ((1.9), `r3Up`) and an upward, a downward and an upward strand
(Proposition 7.6, `r3Alt`). The others follow by rotation, as in KL III: given the relation for
the strands `a b c`, bend the strand `c` around the left of the diagram with a cup at the bottom
right and a cap at the top left (`r3At_rot`). The pitchfork relations ((2.4), (2.5), (7.5),
(7.6), `cupPF_sgn`) move the cup below the crossings with `c`, and the zigzag ((1.10), (6.6))
cancels the cup against the cap; the two sides of Reidemeister 3 for `a b c` become, up to sign,
the two sides of Reidemeister 3 for `c* a b`. Starting from `↑↑↑` this rotation reaches the six
orientations other than `↑↓↑` and `↓↑↓`, and `↓↑↓` is the rotation of `↑↓↑`.

With `capCurlRel` and `cupCurlRel` (`OddMath.SKM.SpanCurls`) this discharges the hypotheses of
the elimination of caps `capElim'`.

## Main results

* `cupPF_sgn`: a strand passes below a cup of either orientation, up to sign.
* `r3At_rot`: the rotation of Reidemeister 3.
* `r3Rel`: Reidemeister 3 for every orientation (`R3Rel`).
* `capElim_full`: elimination of caps, with no hypotheses.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Pitchforks through a cup, up to sign -/

theorem XSgn.of_cl {ν : X} {s t : List (Letter I)} {L L' : List (XLayer I)}
    {A B : List (LayerData I)} (hL : L = A.map ofL) (hL' : L' = B.map ofL) (p : ZMod 2)
    (h : cl D Sc ν s t A = zsign k p • cl D Sc ν s t B) : XSgn cs ν s t L L' :=
  ⟨p, by subst hL hL'; rwa [xev_map_ofL, xev_map_ofL]⟩

/-- **A strand passes below a cup** of either orientation, up to sign ((2.4), (2.5),
Proposition 7.2 (7.5), (7.6)); the exact form of `cupPF`. -/
theorem cupPF_sgn (ν : X) (x m : Letter I) :
    XSgn cs ν [m] [x, m, flipL x]
      ((xCupL x).map (xwhL [] [m]) ++ (xCrL (flipL x) m).map (xwhL [x] []))
      ((xCupL x).map (xwhL [m] []) ++ (xCrL m x).map (xwhL [] [flipL x])) := by
  obtain ⟨_ | _, i⟩ := x <;> obtain ⟨_ | _, j⟩ := m <;>
    simp only [flipL, Bool.not_false, Bool.not_true]
  · -- the rightward cup and a downward strand, (2.5)
    refine XSgn.of_cl cs (A := [([], Shape.cup i, [dn j])] ++ (sigmaL j i).map (whL [dn i] []))
      (B := [([dn j], Shape.cup i, [])] ++ (dcrossL j i).map (whL [] [up i])) ?_ ?_ 0 ?_
    · simp only [xCupL_dn, xCrL_up_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · simp only [xCupL_dn, xCrL_dn_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · rw [eq_2_5_a, zsign_zero, one_smul]
  · -- the rightward cup and an upward strand, (2.4)
    refine XSgn.of_cl cs (A := [([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])])
      (B := [([up j], Shape.cup i, [])] ++ (sigmaL i j).map (whL [] [up i])) ?_ ?_ 0 ?_
    · rfl
    · simp only [xCupL_dn, xCrL_up_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · rw [eq_2_4_b, zsign_zero, one_smul]
  · -- the leftward cup and a downward strand, (7.6)
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
    exact E
  · -- the leftward cup and an upward strand, (7.5)
    exact ⟨0, by rw [zsign_zero, one_smul]; exact (pitchfork_cup cs ν i j).symm⟩

/-! ## Rotation of Reidemeister 3 -/

theorem xChain_crW (u v : List (Letter I)) (a b : Letter I) :
    XChain (u ++ [a, b] ++ v) ((xCrL a b).map (xwhL u v)) (u ++ [b, a] ++ v) :=
  (xChain_xCrL a b).whisk u v

theorem xChain_cupW (u v : List (Letter I)) (l : Letter I) :
    XChain (u ++ v) ((xCupL l).map (xwhL u v)) (u ++ [l, flipL l] ++ v) := by
  simpa using (xChain_xCupL l).whisk u v

theorem xChain_capW (u v : List (Letter I)) (l : Letter I) :
    XChain (u ++ [flipL l, l] ++ v) ((xCapL l).map (xwhL u v)) (u ++ v) := by
  simpa using (xChain_xCapL l).whisk u v

/-- The strand `c` of a diagram `a b c → c b a` bent around the left: a cup at the bottom right,
a cap at the top left. -/
def r3Bend (c : Letter I) (a b : Letter I) (F : List (XLayer I)) : List (XLayer I) :=
  (xCupL c).map (xwhL [flipL c, a, b] []) ++ F.map (xwhL [flipL c] [flipL c]) ++
    (xCapL c).map (xwhL [] [b, a, flipL c])

/-- The bent left side of Reidemeister 3 for `a b c` is `±` the right side for `c* a b`. -/
theorem r3Bend_r3L (ν : X) (a b c : Letter I) :
    XSgn cs ν [flipL c, a, b] [b, a, flipL c] (r3Bend c a b (r3L a b c))
      (r3R (flipL c) a b) := by
  have hab : XChain [flipL c, a, b] ((xCrL a b).map (xwhL [flipL c] [])) [flipL c, b, a] := by
    simpa using xChain_crW [flipL c] [] a b
  -- step 1: the crossing of `a` and `b` passes below the cup
  refine XSgn.trans (XSgn.symm (XSgn.ichg cs (ν := ν) (S := [flipL c, a, b]) (T := [b, a, flipL c])
    (L' := r3Bend c a b (r3L a b c)) [] ((xCrL a c).map (xwhL [flipL c, b] [flipL c]) ++
      (xCrL b c).map (xwhL [flipL c] [a, flipL c]) ++ (xCapL c).map (xwhL [] [b, a, flipL c]))
    [flipL c] [] (xChain_xCrL a b) (xChain_xCupL c) (by simp) rfl
    (by simp [r3Bend, r3L]))) ?_
  -- step 2: the pitchfork moves the cup to the left of `a`
  refine XSgn.trans (XSgn.at
    ((xCrL a b).map (xwhL [flipL c] [])) ((xCrL b c).map (xwhL [flipL c] [a, flipL c]) ++
      (xCapL c).map (xwhL [] [b, a, flipL c])) [flipL c, b] [] (XSgn.symm (cupPF_sgn cs _ c a))
    (by simpa using hab)
    (((xChain_xCupL c).whisk [a] []).app ((xChain_xCrL a c).whisk [] [flipL c]) (by simp))
    (((xChain_xCupL c).whisk [] [a]).app ((xChain_xCrL (flipL c) a).whisk [c] []) (by simp))
    (by simp) rfl) ?_
  -- step 3: the crossing of `c*` and `a` passes the crossing of `b` and `c`
  refine XSgn.trans (XSgn.symm (XSgn.ichg cs
    ((xCrL a b).map (xwhL [flipL c] []) ++ (xCupL c).map (xwhL [flipL c, b] [a]))
    ((xCapL c).map (xwhL [] [b, a, flipL c])) [flipL c] [] (xChain_xCrL b c)
    (xChain_xCrL (flipL c) a)
    (hab.app (xChain_cupW [flipL c, b] [a] c) (by simp) |>.cast rfl (by simp)) rfl
    (by simp))) ?_
  -- step 4: the pitchfork moves the cup to the left of `b`
  refine XSgn.trans (XSgn.at
    ((xCrL a b).map (xwhL [flipL c] [])) ((xCrL (flipL c) a).map (xwhL [flipL c, c, b] []) ++
      (xCapL c).map (xwhL [] [b, a, flipL c])) [flipL c] [a] (XSgn.symm (cupPF_sgn cs _ c b))
    (by simpa using hab)
    (((xChain_xCupL c).whisk [b] []).app ((xChain_xCrL b c).whisk [] [flipL c]) (by simp))
    (((xChain_xCupL c).whisk [] [b]).app ((xChain_xCrL (flipL c) b).whisk [c] []) (by simp))
    (by simp) rfl) ?_
  -- step 5: the cap passes below the crossings of `c*`
  have hB : XChain [flipL c, b, a] ((xCrL (flipL c) b).map (xwhL [] [a]) ++
      (xCrL (flipL c) a).map (xwhL [b] [])) [b, a, flipL c] :=
    (xChain_crW [] [a] (flipL c) b).app (xChain_crW [b] [] (flipL c) a) (by simp)
  refine XSgn.trans (XSgn.symm (XSgn.ichg cs
    ((xCrL a b).map (xwhL [flipL c] []) ++ (xCupL c).map (xwhL [flipL c] [b, a])) [] [] []
    (xChain_xCapL c) hB
    (hab.app (xChain_cupW [flipL c] [b, a] c) (by simp) |>.cast rfl (by simp))
    rfl (by simp))) ?_
  -- step 6: the zigzag
  refine XSgn.trans (XSgn.at
    ((xCrL a b).map (xwhL [flipL c] [])) (((xCrL (flipL c) b).map (xwhL [] [a]) ++
      (xCrL (flipL c) a).map (xwhL [b] [])).map (xwhL [] [])) [] [b, a] (zigR_sgn cs _ c)
    (by simpa using hab)
    (((xChain_xCupL c).whisk [flipL c] []).app ((xChain_xCapL c).whisk [] [flipL c]) (by simp))
    rfl (by simp) rfl) ?_
  exact XSgn.of_eq (by simp [r3R])

/-- The bent right side of Reidemeister 3 for `a b c` is `±` the left side for `c* a b`. -/
theorem r3Bend_r3R (ν : X) (a b c : Letter I) :
    XSgn cs ν [flipL c, a, b] [b, a, flipL c] (r3Bend c a b (r3R a b c))
      (r3L (flipL c) a b) := by
  -- step 1: the pitchfork moves the cup to the left of `b`
  refine XSgn.trans (XSgn.at [] ((xCrL a c).map (xwhL [flipL c] [b, flipL c]) ++
      (xCrL a b).map (xwhL [flipL c, c] [flipL c]) ++ (xCapL c).map (xwhL [] [b, a, flipL c]))
    [flipL c, a] [] (XSgn.symm (cupPF_sgn cs _ c b)) (by simp)
    (((xChain_xCupL c).whisk [b] []).app ((xChain_xCrL b c).whisk [] [flipL c]) (by simp))
    (((xChain_xCupL c).whisk [] [b]).app ((xChain_xCrL (flipL c) b).whisk [c] []) (by simp))
    (by simp [r3Bend, r3R]) rfl) ?_
  -- step 2: the crossing of `a` and `c` passes the crossing of `c*` and `b`
  refine XSgn.trans (XSgn.symm (XSgn.ichg cs ((xCupL c).map (xwhL [flipL c, a] [b]))
    ((xCrL a b).map (xwhL [flipL c, c] [flipL c]) ++ (xCapL c).map (xwhL [] [b, a, flipL c]))
    [flipL c] [] (xChain_xCrL a c) (xChain_xCrL (flipL c) b)
    ((xChain_cupW [flipL c, a] [b] c).cast rfl (by simp)) rfl (by simp))) ?_
  -- step 3: the pitchfork moves the cup to the left of `a`
  refine XSgn.trans (XSgn.at [] ((xCrL (flipL c) b).map (xwhL [flipL c, c, a] []) ++
      (xCrL a b).map (xwhL [flipL c, c] [flipL c]) ++ (xCapL c).map (xwhL [] [b, a, flipL c]))
    [flipL c] [b] (XSgn.symm (cupPF_sgn cs _ c a)) (by simp)
    (((xChain_xCupL c).whisk [a] []).app ((xChain_xCrL a c).whisk [] [flipL c]) (by simp))
    (((xChain_xCupL c).whisk [] [a]).app ((xChain_xCrL (flipL c) a).whisk [c] []) (by simp))
    (by simp) rfl) ?_
  -- step 4: the cap passes below the three crossings
  have hB : XChain [flipL c, a, b] ((xCrL (flipL c) a).map (xwhL [] [b]) ++
      (xCrL (flipL c) b).map (xwhL [a] []) ++ (xCrL a b).map (xwhL [] [flipL c]))
      [b, a, flipL c] :=
    ((xChain_crW [] [b] (flipL c) a).app (xChain_crW [a] [] (flipL c) b) (by simp)).app
      (xChain_crW [] [flipL c] a b) (by simp)
  refine XSgn.trans (XSgn.symm (XSgn.ichg cs ((xCupL c).map (xwhL [flipL c] [a, b])) [] [] []
    (xChain_xCapL c) hB ((xChain_cupW [flipL c] [a, b] c).cast rfl (by simp)) rfl
    (by simp))) ?_
  -- step 5: the zigzag
  refine XSgn.trans (XSgn.at [] (((xCrL (flipL c) a).map (xwhL [] [b]) ++
      (xCrL (flipL c) b).map (xwhL [a] []) ++ (xCrL a b).map (xwhL [] [flipL c])).map (xwhL [] []))
    [] [a, b] (zigR_sgn cs _ c) (by simp)
    (((xChain_xCupL c).whisk [flipL c] []).app ((xChain_xCapL c).whisk [] [flipL c]) (by simp))
    rfl (by simp) rfl) ?_
  exact XSgn.of_eq (by simp [r3L])

/-- Reidemeister 3 for the strands `a b c`, up to sign modulo diagrams without crossings. -/
def R3At (a b c : Letter I) : Prop :=
  ∀ ν : X, XEq cs ν [a, b, c] [c, b, a] 0 (r3L a b c) (r3R a b c)

/-- **Rotation of Reidemeister 3**: Reidemeister 3 for `a b c` gives Reidemeister 3 for
`c* a b`, by bending the strand `c` around the left with a cup and a cap. -/
theorem r3At_rot {a b c : Letter I} (h : R3At cs (X := X) a b c) : R3At cs (X := X) (flipL c) a b := by
  intro ν
  have hM : XEq cs ν [flipL c, a, b] [b, a, flipL c] 0 (r3Bend c a b (r3L a b c))
      (r3Bend c a b (r3R a b c)) :=
    XEq.at ((xCupL c).map (xwhL [flipL c, a, b] [])) ((xCapL c).map (xwhL [] [b, a, flipL c]))
      [flipL c] [flipL c] (h _) (by simpa using xChain_cupW [flipL c, a, b] [] c)
      (((xChain_crW [] [c] a b).app (xChain_crW [b] [] a c) (by simp)).app
        (xChain_crW [] [a] b c) (by simp))
      (((xChain_crW [a] [] b c).app (xChain_crW [] [b] a c) (by simp)).app
        (xChain_crW [c] [] a b) (by simp)) rfl rfl (by simp)
  exact ((r3Bend_r3R cs ν a b c).symm.xeq 0).trans (hM.symm.trans ((r3Bend_r3L cs ν a b c).xeq 0))

/-! ## Reidemeister 3 for every orientation -/

/-- Three upward strands ((1.9)). -/
theorem r3At_uuu (i j k' : I) : R3At cs (X := X) (up i) (up j) (up k') := fun ν =>
  XEq.of_cl (A := crossL [] i j [up k'] ++ crossL [up j] i k' [] ++ crossL [] j k' [up i])
    (B := crossL [up i] j k' [] ++ crossL [] i k' [up j] ++ crossL [up k'] i j []) rfl rfl 0
    (by rw [zsign_zero, one_smul]; exact r3Up cs ν i j k')

/-- An upward, a downward and an upward strand (Proposition 7.6). -/
theorem r3At_udu (j i a : I) : R3At cs (X := X) (up j) (dn i) (up a) := fun ν =>
  XEq.of_cl (A := altL i j a) (B := altR i j a) rfl rfl 0
    (by rw [zsign_zero, one_smul]; exact r3Alt cs ν i j a)

theorem r3At_duu (i j k' : I) : R3At cs (X := X) (dn i) (up j) (up k') :=
  r3At_rot cs (r3At_uuu cs j k' i)

theorem r3At_ddu (i j k' : I) : R3At cs (X := X) (dn i) (dn j) (up k') :=
  r3At_rot cs (r3At_duu cs j k' i)

theorem r3At_ddd (i j k' : I) : R3At cs (X := X) (dn i) (dn j) (dn k') :=
  r3At_rot cs (r3At_ddu cs j k' i)

theorem r3At_udd (i j k' : I) : R3At cs (X := X) (up i) (dn j) (dn k') :=
  r3At_rot cs (r3At_ddd cs j k' i)

theorem r3At_uud (i j k' : I) : R3At cs (X := X) (up i) (up j) (dn k') :=
  r3At_rot cs (r3At_udd cs j k' i)

theorem r3At_dud (i j k' : I) : R3At cs (X := X) (dn i) (up j) (dn k') :=
  r3At_rot cs (r3At_udu cs j k' i)

/-- **Reidemeister 3 for every orientation** (`R3Rel`): (1.9) and Proposition 7.6, and their
rotations by the pitchfork relations ((2.4), (2.5), (7.5), (7.6)) and the zigzags ((1.10),
(6.6)). -/
theorem r3Rel : R3Rel D Sc cs := by
  rintro ν ⟨_ | _, i⟩ ⟨_ | _, j⟩ ⟨_ | _, k'⟩
  · exact r3At_ddd cs i j k' ν
  · exact r3At_ddu cs i j k' ν
  · exact r3At_dud cs i j k' ν
  · exact r3At_duu cs i j k' ν
  · exact r3At_udd cs i j k' ν
  · exact r3At_udu cs i j k' ν
  · exact r3At_uud cs i j k' ν
  · exact r3At_uuu cs i j k' ν

/-! ## Elimination of caps -/

variable (μ : X) (w₀ : List (Letter I)) in
/-- **Elimination of caps** ([BE2] Theorem 8.1, KL III Proposition 3.11): every extended diagram
`E_{w₀} 1_μ → E_v 1_μ` with at most `c` crossings is a combination of move diagrams with at most
`c` crossings followed by products of bubbles in the rightmost region, modulo 2-morphisms factoring
through sequences shorter than `w₀`. This is `capElim'` with its local relations proved:
Reidemeister 3 (`r3Rel`) and the curls of a crossing with a cap or a cup (`capCurlRel`,
`cupCurlRel`). -/
theorem capElim_full :
    ∀ (c : ℕ) (v : List (Letter I)) (L : List (XLayer I)), xcnt L ≤ c →
      xev cs μ w₀ v L ∈ CapTarget D Sc cs μ w₀ v c :=
  capElim' μ w₀ (r3Rel cs) (capCurlRel cs) (cupCurlRel cs)

end OddMath.SKM
