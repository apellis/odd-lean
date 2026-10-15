/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCapsPush
import OddMath.SKM.SpanBubbleOut

/-!
# The cap push through a cup, and elimination of caps

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. This file pushes the cap block below a
cup (`push_cup`), using the local relations of `OddMath.SKM.SpanCapCup`, and assembles the steps of
the cap push (`pushHyp_all`) into the elimination of caps (`capElim'`).

The dots on `A` are created one at a time from dots on `B` ((2.3), (4.3), `dotB_decomp`); a dot on
`B` passes below a cup not touching `B` by the super interchange law.

## Main results

* `push_cup`: the cap push through a cup.
* `pushHyp_all`: the cap push.
* `capElim'`: elimination of caps, assuming the local relations `R3Rel`, `CapCurlRel` and
  `CupCurlRel` (proved in `OddMath.SKM.SpanR3` and `OddMath.SKM.SpanCurls`; the version without
  hypotheses is `capElim_full`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-- A local relation holding up to sign holds in context, up to the same sign. -/
theorem xev_sgn_at {ν : X} {s₀ t₀ s t : List (Letter I)} {L L' : List (XLayer I)}
    (pre post : List (XLayer I)) (u v : List (Letter I)) {A B : List (XLayer I)} {p : ZMod 2}
    (E : xev cs (wt D ν v) s t A = zsign k p • xev cs (wt D ν v) s t B)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) (hB : XChain s B t)
    (hL : L = pre ++ A.map (xwhL u v) ++ post) (hL' : L' = pre ++ B.map (xwhL u v) ++ post) :
    xev cs ν s₀ t₀ L = zsign k p • xev cs ν s₀ t₀ L' := by
  subst hL hL'
  rw [xev_ctx cs ν pre post u v hpre hA, xev_ctx cs ν pre post u v hpre hB, E, map_smul,
    Linear.smul_comp, Linear.comp_smul]

theorem zsign_smul_symm {M : Type*} [AddCommGroup M] [Module k M] {a b : M} {p : ZMod 2}
    (h : a = zsign k p • b) : b = zsign k p • a := by
  rw [h, smul_smul, zsign_mul_self', one_smul]

section PushCup

variable {μ : X} {w₀ : List (Letter I)}

/-- A move diagram lies in `CapTarget`. -/
theorem capT_of_mvs {v : List (Letter I)} {t : ℕ} {L : List (XLayer I)} (ms : List (Mv I))
    (hms : MvChain w₀ ms v) (hL : L = mvLay ms) (ht : xcnt (mvLay ms) ≤ t) :
    xev cs μ w₀ v L ∈ CapTarget D Sc cs μ w₀ v t := by
  subst hL
  exact Submodule.mem_sup_left (xev_mvLay_mem_mvSp cs hms ht)

/-- **Dots on `A` below a cup not touching `B`**: the cap push for a block without dots on `A`
gives the cap push with any number of dots. A dot on `A` comes from a dot on `B` ((2.3), (4.3)),
up to an odd bubble and lower terms, and a dot on `B` passes below the cup. -/
theorem cup_dotB_ind (hS : BubbleSlideOut D Sc cs) {c : ℕ} (hF : LowHyp cs μ w₀ c)
    {u R P S Q : List (Letter I)} {x l : Letter I}
    (he : u ++ [x, flipL x] ++ R = P ++ [flipL l] ++ S)
    (H0 : ∀ ms : List (Mv I), MvChain w₀ ms (u ++ R ++ [l] ++ Q) →
      xcnt (mvLay ms) + S.length ≤ c →
      xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)) ++
        (capBlk S l 0).map (xwhL P Q)) ∈
        CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + S.length)) (d : ℕ) :
    ∀ ms : List (Mv I), MvChain w₀ ms (u ++ R ++ [l] ++ Q) → xcnt (mvLay ms) + S.length ≤ c →
      xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)) ++
        (capBlk S l d).map (xwhL P Q)) ∈
        CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + S.length) := by
  induction d with
  | zero => exact H0
  | succ d ih =>
    intro ms hms hc
    have hpre : XChain w₀ (mvLay ms ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)))
        (P ++ [flipL l] ++ S ++ [l] ++ Q) :=
      hms.xChain.app ((xChain_xCupL x).whisk u (R ++ [l] ++ Q)) (by simp) |>.cast rfl
        (by rw [show u ++ [x, flipL x] ++ (R ++ [l] ++ Q) = u ++ [x, flipL x] ++ R ++ [l] ++ Q by
          simp, he])
    obtain ⟨p, r, e, he', E⟩ := dotB_decomp hF d hpre (by simpa using hc)
    simp only [xcnt_append, xcnt_map_xwhL, xcnt_xCupL, add_zero] at he'
    have key : xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)) ++
        (capBlk S l (d + 1)).map (xwhL P Q)) = zsign k p • (xev cs μ w₀ (P ++ S ++ Q)
          (mvLay ms ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)) ++
            (xDotL l).map (xwhL (P ++ [flipL l] ++ S) Q) ++ (capBlk S l d).map (xwhL P Q)) -
          r • (xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)) ++
            (capBlk S l d).map (xwhL P Q)) ≫ wordCast μ (cast_mid P S Q) (cast_mid P S Q)
              (plcL D Sc μ P (S ++ Q) [] [] (oddBubble cs l.2 (wt D μ (S ++ Q))))) - e) := by
      rw [E, add_sub_right_comm, add_sub_cancel_right, add_sub_cancel_right, smul_smul,
        zsign_mul_self', one_smul]
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.sub_mem _ ?_
      (Submodule.smul_mem _ _ (capTarget_comp_bubble_mid hS _ (ih ms hms hc)
        (isBubbleProd_oddBubble _ _)))) he')
    -- the dot on `B` passes below the cup
    have hA : XChain R ((xCupL x).map (xwhL [] R)) ([x, flipL x] ++ R) := by
      simpa using (xChain_xCupL x).whisk [] R
    obtain ⟨q, hq⟩ := xev_ichg cs μ (T := P ++ S ++ Q) (mvLay ms) ((capBlk S l d).map (xwhL P Q))
      u Q hA (xChain_xDotL l) (hms.xChain.cast rfl (by simp))
    have e₁ : mvLay ms ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)) ++
        (xDotL l).map (xwhL (P ++ [flipL l] ++ S) Q) ++ (capBlk S l d).map (xwhL P Q) =
        mvLay ms ++ ((xCupL x).map (xwhL [] R)).map (xwhL u ([l] ++ Q)) ++
          (xDotL l).map (xwhL (u ++ ([x, flipL x] ++ R)) Q) ++ (capBlk S l d).map (xwhL P Q) := by
      rw [show u ++ ([x, flipL x] ++ R) = P ++ [flipL l] ++ S by rw [← he]; simp]
      simp
    have e₂ : mvLay ms ++ (xDotL l).map (xwhL (u ++ R) Q) ++
        ((xCupL x).map (xwhL [] R)).map (xwhL u ([l] ++ Q)) ++ (capBlk S l d).map (xwhL P Q) =
        mvLay (ms ++ [Mv.dot (u ++ R) l Q]) ++ (xCupL x).map (xwhL u (R ++ [l] ++ Q)) ++
          (capBlk S l d).map (xwhL P Q) := by
      simp [mvLay_singleton, Mv.lay, Mv.loc, Mv.pre, Mv.post]
    rw [e₁, hq, e₂]
    refine Submodule.smul_mem _ _ ?_
    have hms' : MvChain w₀ (ms ++ [Mv.dot (u ++ R) l Q]) (u ++ R ++ [l] ++ Q) :=
      MvChain.snoc (m := Mv.dot (u ++ R) l Q) hms
    have hx : xcnt (mvLay (ms ++ [Mv.dot (u ++ R) l Q])) = xcnt (mvLay ms) := by
      simp [mvLay_singleton, Mv.lay, Mv.loc]
    have h := ih _ hms' (by rw [hx]; exact hc)
    rw [hx] at h
    exact h

theorem MvChain.cast' {s s' t t' : List (Letter I)} {ms : List (Mv I)} (h : MvChain s ms t)
    (hs : s = s') (ht : t = t') : MvChain s' ms t' := hs ▸ ht ▸ h

/-- **A cup creating `B` and a strand to the right of the block**: the dots on `A` pass below the
cup, and the cap cancels the cup (pitchforks, then the zigzag); the block becomes the strand `A`
moving right across `S`. -/
theorem push_cupBright {c : ℕ} {ms : List (Mv I)} (hF : LowHyp cs μ w₀ c)
    {P S v : List (Letter I)} {l : Letter I} (d : ℕ)
    (hms : MvChain w₀ ms (P ++ [flipL l] ++ S ++ v)) (hc : xcnt (mvLay ms) + S.length ≤ c) :
    xev cs μ w₀ (P ++ S ++ (flipL l :: v)) (mvLay ms ++
        (xCupL l).map (xwhL (P ++ [flipL l] ++ S) v) ++
        (capBlk S l d).map (xwhL P (flipL l :: v))) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ (flipL l :: v)) (xcnt (mvLay ms) + S.length) := by
  have hcupS : XChain S ((xCupL l).map (xwhL S [])) (S ++ [l, flipL l]) := by
    simpa using (xChain_xCupL l).whisk S []
  -- the dots on `A` pass the strand `B` moving across `S`
  obtain ⟨p₁, h₁⟩ := xev_ichg cs μ (T := P ++ S ++ (flipL l :: v))
    (mvLay ms ++ (xCupL l).map (xwhL (P ++ [flipL l] ++ S) v))
    ((xCapL l).map (xwhL P (S ++ (flipL l :: v)))) P (flipL l :: v) (xChain_xDotsL (flipL l) d)
    (xChain_lmLc S l)
    (hms.xChain.app ((xChain_xCupL l).whisk (P ++ [flipL l] ++ S) v) (by simp) |>.cast rfl
      (by simp))
  -- the dots on `A` pass below the cup
  obtain ⟨p₂, h₂⟩ := xev_ichg cs μ (T := P ++ S ++ (flipL l :: v)) (mvLay ms)
    ((lmLc S l).map (xwhL (P ++ [flipL l]) (flipL l :: v)) ++
      (xCapL l).map (xwhL P (S ++ (flipL l :: v))))
    P v (xChain_xDotsL (flipL l) d) hcupS (hms.xChain.cast rfl (by simp))
  have e₀ : mvLay ms ++ (xCupL l).map (xwhL (P ++ [flipL l] ++ S) v) ++
      (capBlk S l d).map (xwhL P (flipL l :: v)) =
      mvLay ms ++ (xCupL l).map (xwhL (P ++ [flipL l] ++ S) v) ++
        (lmLc S l).map (xwhL (P ++ [flipL l]) (flipL l :: v)) ++
        (xDotsL (flipL l) d).map (xwhL P ((l :: S) ++ (flipL l :: v))) ++
        (xCapL l).map (xwhL P (S ++ (flipL l :: v))) := by
    simp [capBlk]
  have e₁ : mvLay ms ++ (xCupL l).map (xwhL (P ++ [flipL l] ++ S) v) ++
        (xDotsL (flipL l) d).map (xwhL P ((S ++ [l]) ++ (flipL l :: v))) ++
        (lmLc S l).map (xwhL (P ++ [flipL l]) (flipL l :: v)) ++
        (xCapL l).map (xwhL P (S ++ (flipL l :: v))) =
      mvLay ms ++ ((xCupL l).map (xwhL S [])).map (xwhL (P ++ [flipL l]) v) ++
        (xDotsL (flipL l) d).map (xwhL P ((S ++ [l, flipL l]) ++ v)) ++
        ((lmLc S l).map (xwhL (P ++ [flipL l]) (flipL l :: v)) ++
          (xCapL l).map (xwhL P (S ++ (flipL l :: v)))) := by
    simp
  have hX : xev cs μ w₀ (P ++ S ++ (flipL l :: v)) (mvLay ms ++
      (xCupL l).map (xwhL (P ++ [flipL l] ++ S) v) ++ (capBlk S l d).map (xwhL P (flipL l :: v))) =
      zsign k (p₁ + p₂) • xev cs μ w₀ (P ++ S ++ (flipL l :: v)) (mvLay ms ++
        (xDotsL (flipL l) d).map (xwhL P (S ++ v)) ++
        ((xCupL l).map (xwhL S [])).map (xwhL (P ++ [flipL l]) v) ++
        ((lmLc S l).map (xwhL (P ++ [flipL l]) (flipL l :: v)) ++
          (xCapL l).map (xwhL P (S ++ (flipL l :: v))))) := by
    rw [e₀, zsign_smul_symm h₁, e₁, zsign_smul_symm h₂, smul_smul, ← zsign_add]
  refine capTarget_mem_of_smul _ hX ?_
  have hpre : XChain w₀ (mvLay ms ++ (xDotsL (flipL l) d).map (xwhL P (S ++ v)))
      (P ++ ([flipL l] ++ S) ++ v) :=
    hms.xChain.app ((xChain_xDotsL (flipL l) d).whisk P (S ++ v)) (by simp) |>.cast rfl (by simp)
  have hms₁ : MvChain w₀ (ms ++ dotMv d P (flipL l) (S ++ v)) (P ++ [flipL l] ++ (S ++ v)) :=
    (hms.cast' rfl (by simp)).append (mvChain_dotMv d P (flipL l) (S ++ v))
  have hZ : XChain ([flipL l] ++ S) ((xCupL l).map (xwhL ([flipL l] ++ S) []) ++
      (capBlk S l 0).map (xwhL [] [flipL l])) (S ++ [flipL l]) :=
    ((xChain_xCupL l).whisk ([flipL l] ++ S) []).app ((xChain_capBlk S l 0).whisk [] [flipL l])
      (by simp) |>.cast (by simp) (by simp)
  cases S with
  | nil =>
    -- the zigzag
    obtain ⟨p, hp⟩ := zigR cs (wt D μ v) l
    have hp' : xev cs (wt D μ v) [flipL l] [flipL l] ((xCupL l).map (xwhL [flipL l] []) ++
        (xCapL l).map (xwhL [] [flipL l])) = zsign k p • xev cs (wt D μ v) [flipL l] [flipL l] [] := by
      rw [hp, xev_nil, cl_nil]
    refine capTarget_mem_of_smul p (xev_sgn_at _ [] P v hp' (hpre.cast rfl (by simp))
      (by simpa [capBlk, lmLc, xDotsL] using hZ) rfl (by simp [lmLc]) rfl) ?_
    exact capT_of_mvs (ms ++ dotMv d P (flipL l) v) (by simpa using hms₁)
      (by simp [mvLay_dotMv]) (by simp)
  | cons s S =>
    -- pitchforks, then the zigzag
    refine capT_of_xeq hF (c' := xcnt (mvLay ms) + S.length) (XEq.at _ [] P v
      (capBlk_cupBright0 cs (wt D μ v) (s :: S) l) hpre hZ (xChain_lmRc (flipL l) (s :: S)) ?_ rfl
      (by simp)) (by simp at hc ⊢; omega) (by simp) ?_
    · simp [capBlk, xDotsL]
    refine capT_of_mvs (ms ++ dotMv d P (flipL l) ((s :: S) ++ v) ++
      mvWh P v (rmMv (flipL l) (s :: S))) (hms₁.append ?_) (by simp [mvLay_dotMv, mvLay_mvWh,
        mvLay_rmMv]) (by simp)
    simpa using (mvChain_rmMv (flipL l) (s :: S)).wh P v

/-- **The cap push past a cup**, given the curl of a cup and a crossing (`CupCurlRel`). -/
theorem push_cup (hS : BubbleSlideOut D Sc cs) (hU : CupCurlRel D Sc cs) {c : ℕ}
    {ms : List (Mv I)} (hF : LowHyp cs μ w₀ c) (hIH : PushHyp cs μ w₀ c ms) (u : List (Letter I))
    (x : Letter I) (v : List (Letter I)) (hms : MvChain w₀ ms (Mv.cup u x v).src) :
    PushGoal cs μ w₀ c ms (Mv.cup u x v) := by
  intro P S Q l d ht hc
  have ht' : u ++ [x, flipL x] ++ v = P ++ [flipL l] ++ S ++ [l] ++ Q := ht
  have hlay : (Mv.cup u x v).lay = (xCupL x).map (xwhL u v) := rfl
  have hms' : MvChain w₀ ms (u ++ v) := by simpa [Mv.src, Mv.pre, Mv.lsrc, Mv.post] using hms
  rcases posPair ht' with ⟨R, hP, hv⟩ | ⟨hP, h1, hv⟩ | ⟨hu, h2, S', hS', hv⟩ |
    ⟨hu, h2, hS', h1, hv⟩ | ⟨S₁, S₂, hS', hu, hv⟩ | ⟨S', hS', h1, hu, hv⟩ | ⟨hu, h2, hQ⟩ |
    ⟨R, hQ, hu⟩
  · exact push_disjL hIH hms d R hP hv hc
  · -- a cup creating a strand and `A`: the zigzag
    have hx : x = l := by simpa using congrArg flipL h1
    subst P v x
    simp only [hlay, xcnt_map_xwhL, xcnt_xCupL, add_zero] at hc ⊢
    refine cup_dotB_ind hS hF (R := S) (by simp) ?_ d ms (by simpa using hms') hc
    intro ms₁ hms₁ _
    obtain ⟨p, hp⟩ := capBlk_cupAleft0 cs (wt D μ Q) S l
    refine capTarget_mem_of_smul p (xev_sgn_at (mvLay ms₁) [] u Q hp
      (hms₁.xChain.cast rfl (by simp)) ?_ (xChain_lmLc S l) (by simp) rfl) ?_
    · exact ((xChain_xCupL l).whisk [] (S ++ [l])).app ((xChain_capBlk S l 0).whisk [l] [])
        (by simp) |>.cast (by simp) (by simp)
    refine capT_of_mvs (ms₁ ++ mvWh u Q (lmMv S l)) (hms₁.append ?_)
      (by simp [mvLay_mvWh, mvLay_lmMv]) (by simp)
    simpa using (mvChain_lmMv S l).wh u Q
  · -- a cup creating `A` and the first strand of the block: a curl
    subst u x
    rw [flipL_flipL] at hS'
    subst S v
    simp only [hlay, xcnt_map_xwhL, xcnt_xCupL, add_zero] at hc ⊢
    refine cup_dotB_ind hS hF (R := S') (by simp) ?_ d ms (by simpa using hms') hc
    intro ms₁ hms₁ hc₁
    refine capT_of_leL hF (c' := xcnt (mvLay ms₁) + S'.length) (by simp at hc₁; omega) (by simp)
      (xev_low_at cs (mvLay ms₁) [] P Q (capBlk_cupAs0 cs hU (wt D μ Q) S' l)
        (hms₁.xChain.cast rfl (by simp)) ?_ (by simp) (by simp))
    exact ((xChain_xCupL (flipL l)).whisk [] (S' ++ [l])).app (xChain_capBlk (l :: S') l 0)
      (by simp) |>.cast (by simp) rfl
  · -- a cup creating `A` and `B`: a bubble
    subst u x S v
    simp only [hlay, xcnt_map_xwhL, xcnt_xCupL, add_zero, List.length_nil] at hc ⊢
    obtain ⟨a, β, hβ, hab⟩ := cupBubble cs (wt D μ Q) l d
    have hA : XChain [] (xCupL (flipL l) ++ capBlk [] l d) [] :=
      (xChain_xCupL (flipL l)).app (xChain_capBlk [] l d) (by simp)
    have e := xev_ctx cs μ (t₀ := P ++ [] ++ Q) (mvLay ms) [] P Q (hms'.xChain.cast rfl (by simp)) hA
    rw [show mvLay ms ++ (xCupL (flipL l)).map (xwhL P Q) ++ (capBlk [] l d).map (xwhL P Q) =
      mvLay ms ++ (xCupL (flipL l) ++ capBlk [] l d).map (xwhL P Q) ++ [] by simp, e, hab,
      map_smul]
    erw [xev_nil, cl_nil, Category.comp_id]
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ _ (capTarget_comp_bubble hS
      (capT_of_mvs ms hms rfl (by simp)) hβ)
  · -- a cup creating two strands of the block: lower terms
    subst S u v
    simp only [hlay, xcnt_map_xwhL, xcnt_xCupL, add_zero] at hc ⊢
    refine capT_of_leL hF (c' := xcnt (mvLay ms) + (S₁.length + S₂.length + 1))
      (by simp at hc; omega) (by simp)
      (xev_low_at cs (mvLay ms) [] P Q (capBlk_cupSS cs (wt D μ Q) S₁ S₂ x l d)
        (hms'.xChain.cast rfl (by simp)) ?_ (by simp) (by simp))
    exact ((xChain_xCupL x).whisk ([flipL l] ++ S₁) (S₂ ++ [l])).app
      (xChain_capBlk (S₁ ++ [x, flipL x] ++ S₂) l d) (by simp) |>.cast (by simp) rfl
  · -- a cup creating the last strand of the block and `B`: a curl
    have hx : x = flipL l := by rw [← h1, flipL_flipL]
    subst x S u v
    simp only [hlay, xcnt_map_xwhL, xcnt_xCupL, add_zero] at hc ⊢
    refine capT_of_leL hF (c' := xcnt (mvLay ms) + S'.length) (by simp at hc; omega)
      (by simp)
      (xev_low_at cs (mvLay ms) [] P Q (capBlk_cupsB cs hU (wt D μ Q) S' l d)
        (hms'.xChain.cast rfl (by simp)) ?_ (by simp) (by simp))
    exact ((xChain_xCupL (flipL l)).whisk ([flipL l] ++ S') []).app
      (xChain_capBlk (S' ++ [flipL l]) l d) (by simp) |>.cast (by simp) rfl
  · -- a cup creating `B` and a strand to the right of the block
    subst u x Q
    simp only [hlay, xcnt_map_xwhL, xcnt_xCupL, add_zero] at hc ⊢
    exact push_cupBright hF d hms' hc
  · exact push_disjR hIH hms d R hQ hu hc

/-- **The cap push** ([BE2] Theorem 8.1, KL III Proposition 3.11), given the bubble slides, the
Reidemeister 3 relations and the curls of a crossing with a cap or a cup. -/
theorem pushHyp_all (hS : BubbleSlideOut D Sc cs) (hR : R3Rel D Sc cs) (hC : CapCurlRel D Sc cs)
    (hU : CupCurlRel D Sc cs) : ∀ c, LowHyp cs μ w₀ c → ∀ ms, PushHyp cs μ w₀ c ms := by
  intro c hF
  refine pushHyp_of_goal fun ms m hIH hms => ?_
  cases m with
  | dot u x v => exact push_dot hS hF hIH u x v hms
  | cross u l₁ l₂ v => exact push_cross hR hC hF hIH u l₁ l₂ v hms
  | cup u x v => exact push_cup hS hU hF hIH u x v hms

end PushCup

variable (μ : X) (w₀ : List (Letter I)) in
/-- **Elimination of caps** ([BE2] Theorem 8.1, KL III Proposition 3.11): every extended diagram
`E_{w₀} 1_μ → E_v 1_μ` with at most `c` crossings is a combination of move diagrams with at most
`c` crossings followed by products of bubbles in the rightmost region, modulo 2-morphisms factoring
through sequences shorter than `w₀`. The Reidemeister 3 relations (`R3Rel`) and the curls of a
crossing with a cap or a cup (`CapCurlRel`, `CupCurlRel`) are hypotheses; the bubble slides hold
(`bubbleSlideOut`). -/
theorem capElim' (hR : R3Rel D Sc cs) (hC : CapCurlRel D Sc cs) (hU : CupCurlRel D Sc cs) :
    ∀ (c : ℕ) (v : List (Letter I)) (L : List (XLayer I)), xcnt L ≤ c →
      xev cs μ w₀ v L ∈ CapTarget D Sc cs μ w₀ v c :=
  capElim_of_push μ w₀ (pushHyp_all (bubbleSlideOut D Sc cs) hR hC hU)

end OddMath.SKM
