/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanClosedLocal

/-!
# Closed crossingless diagrams lie in the image of `β`

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1 and
(1.21)–(1.22) (`β_λ : SYM → End(1_λ)` is surjective), for diagrams without crossings. The
argument is that for closed crossingless diagrams in M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1 (proof of Proposition 3.6): a diagram is read
from the bottom, and each cap is pushed down until it meets the cup it closes up with.

## Main results

* `cupSpan_cap`: **`CupSpan` is closed under caps.** A cap `l* l → 1` carrying a block of dots
  on its upward leg (`capDots`), placed on top of a 2-morphism in `CupSpan`, gives a 2-morphism
  in `CupSpan`. By induction on `CupSpan`: the cap commutes with a dot or cup away from it
  (super interchange law, `xev_swap`), absorbs a dot on a leg (`dotUp_capDots_dn`,
  `dotUp_capDots_up`, `ddot_capDots_dn`, `ddot_capDots_up`), closes up with a cup to a dotted
  bubble (`isBub_cup_capDots`), which slides out (`cupSpan_plcAt`), or straightens a zigzag,
  leaving dots and elements of the image of `β` (`zig_dn_left`, `zig_dn_right`, `zig_up_left`,
  `zig_up_right`, `cupSpan_plcW_slideSetR`).
* `cupSpan_dcup`, `cupSpan_dcap`: the same for the `♦`-cups and `♦`-caps, by (5.11) and (5.12)
  (Corollary 5.2).
* `CupSpan.isBub`: on the empty sequence, `CupSpan` is the image of `β_ν`.
* `xev_isBub_of_xcnt_eq_zero`, `leL_zero_le_bubbleSpan`: **every closed crossingless diagram on
  `1_ν` lies in the image of `β_ν`** ([BE2] Theorem 8.1, (1.21)–(1.22), crossingless case).
* `bubbleSpan_eq_top_of_mem_leL_zero`: hence `β_ν` is surjective as soon as every closed
  2-morphism on `1_ν` is a linear combination of crossingless diagrams. Removing the crossings
  is the remaining step of (1.21)–(1.22).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

/-! ## Relative positions of strands -/

/-- The positions of a strand `x` relative to a pair of adjacent strands `y z`: to the left,
equal to `y`, equal to `z`, or to the right. -/
theorem pos_dot_cases {α : Type*} {a b u v : List α} {x y z : α}
    (h : a ++ [x] ++ b = u ++ [y, z] ++ v) :
    (∃ c, u = a ++ x :: c ∧ b = c ++ y :: z :: v) ∨ (a = u ∧ x = y ∧ b = z :: v) ∨
      (a = u ++ [y] ∧ x = z ∧ b = v) ∨ (∃ c, a = u ++ y :: z :: c ∧ v = c ++ x :: b) := by
  simp only [List.append_assoc, List.cons_append] at h
  rcases List.append_eq_append_iff.1 h with ⟨as, hu, hb⟩ | ⟨bs, ha, hv⟩
  · rcases as with _ | ⟨x', c⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at hu hb
      exact Or.inr (Or.inl ⟨hu.symm, hb.1, hb.2⟩)
    · simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact Or.inl ⟨c, hu, rfl⟩
  · rcases bs with _ | ⟨y', _ | ⟨z', c⟩⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at ha hv
      exact Or.inr (Or.inl ⟨ha, hv.1.symm, hv.2.symm⟩)
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inl ⟨ha, rfl, rfl⟩))
    · simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inr ⟨c, ha, rfl⟩))

/-- The positions of a cup (creating the strands `x x'`) relative to a pair of adjacent strands
`y z`: to the left, sharing its right leg with `y`, equal, sharing its left leg with `z`, or to
the right. -/
theorem pos_cup_cases {α : Type*} {a b u v : List α} {x x' y z : α}
    (h : a ++ [x, x'] ++ b = u ++ [y, z] ++ v) :
    (∃ c, u = a ++ x :: x' :: c ∧ b = c ++ y :: z :: v) ∨ (u = a ++ [x] ∧ x' = y ∧ b = z :: v) ∨
      (a = u ∧ x = y ∧ x' = z ∧ b = v) ∨ (a = u ++ [y] ∧ x = z ∧ v = x' :: b) ∨
      (∃ c, a = u ++ y :: z :: c ∧ v = c ++ x :: x' :: b) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  rcases List.append_eq_append_iff.1 h with ⟨as, hu, hb⟩ | ⟨bs, ha, hv⟩
  · rcases as with _ | ⟨p, _ | ⟨q, c⟩⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at hu hb
      exact Or.inr (Or.inr (Or.inl ⟨hu.symm, hb.1, hb.2.1, hb.2.2⟩))
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      exact Or.inr (Or.inl ⟨hu, rfl, rfl⟩)
    · simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      exact Or.inl ⟨c, hu, rfl⟩
  · rcases bs with _ | ⟨p, _ | ⟨q, c⟩⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at ha hv
      exact Or.inr (Or.inr (Or.inl ⟨ha, hv.1.symm, hv.2.1.symm, hv.2.2.symm⟩))
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, rfl, rfl⟩)))
    · simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, ha, rfl⟩)))

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

theorem letter_cases (l : Letter I) : (∃ i, l = dn i) ∨ ∃ i, l = up i := by
  obtain ⟨_ | _, i⟩ := l
  exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩]

/-! ## Local pieces in `CupSpan` -/

variable (ν : X)

/-- An element of `slideSetR` (dots, then an element of the image of `β` to the right of the
strand) placed on a strand keeps a 2-morphism in `CupSpan`. -/
theorem cupSpan_plcW_slideSetR {s t u v : List (Letter I)} {l : Letter I}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f)
    {g : (pres D Sc).obj (ob D (wt D ν v) [l]) ⟶ (pres D Sc).obj (ob D (wt D ν v) [l])}
    (hg : g ∈ slideSetR cs (wt D ν v) l) : CupSpan cs ν t (f ≫ plcW ν s t u v [l] [l] g) := by
  refine cupSpan_plcW_of_span ν (fun g hg => ?_) hg
  obtain ⟨a, γ, hγ, -, rfl⟩ := hg
  rw [plcW_comp, plcW_rbub, ← Category.assoc]
  refine cupSpan_plcAt ν v (u ++ [l]) ?_ hγ
  by_cases hs : s = u ++ [l] ++ v
  · subst hs
    rw [plcW_dots]
    exact cupSpan_dots ν l u v a hf
  · rw [plcW_apply, cl_of_not (show ¬ SChain s [] (u ++ [l] ++ v) from hs)]
    simp only [Limits.zero_comp, Limits.comp_zero]; exact .zero

theorem CupSpan.congr_list {s t : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} {L L' : List (XLayer I)}
    (h : L = L') (hc : CupSpan cs ν t (f ≫ xev cs ν s t L')) :
    CupSpan cs ν t (f ≫ xev cs ν s t L) := h ▸ hc

/-- A block `Bk` followed by a move, up to a scalar. -/
theorem CupSpan.of_swap {s t : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} {Bk L : List (XLayer I)}
    (hB : ∀ r, CupSpan cs ν r (f ≫ xev cs ν s r Bk)) (m : CMove I) (P Q : List (Letter I))
    {z : k} (hL : xev cs ν s t L = z • xev cs ν s t (Bk ++ m.loc.map (xwhL P Q))) :
    CupSpan cs ν t (f ≫ xev cs ν s t L) := by
  rw [hL, Linear.comp_smul]
  exact .smul z (CupSpan.comp_append ν hB fun r t g hg => .move m P Q hg)

/-- A block on a strand evaluating into `slideSetR`. -/
theorem cupSpan_local_slide {s t u v : List (Letter I)} {l : Letter I}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f)
    {Z : List (XLayer I)} (hZ : XChain [l] Z [l]) (hne : Z ≠ [])
    (hmem : xev cs (wt D ν v) [l] [l] Z ∈ slideSetR cs (wt D ν v) l) :
    CupSpan cs ν t (f ≫ xev cs ν s t (Z.map (xwhL u v))) := by
  rw [xev_eq_plcW ν u v hZ hne]
  exact cupSpan_plcW_slideSetR ν hf hmem

/-! ## Pushing a cap down -/

/-- **`CupSpan` is closed under caps**: a cap with a block of dots on its upward leg, placed
on top of a 2-morphism in `CupSpan`, gives a 2-morphism in `CupSpan`. -/
theorem cupSpan_cap {s : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f) :
    ∀ (l : Letter I) (m : ℕ) (u v t : List (Letter I)),
      CupSpan cs ν t (f ≫ xev cs ν s t ((capDots l m).map (xwhL u v))) := by
  induction hf with
  | @bub β hβ =>
    intro l m u v t
    have h : ¬ XChain [] ((capDots l m).map (xwhL u v)) t := fun h => by
      have := (XChain.whisk_bdry (xChain_capDots l m) (capDots_ne_nil l m) h).1
      simp at this
    rw [xev_of_not cs h, Limits.comp_zero]; exact .zero
  | @move s s₁ f m' u' v' hf ih =>
    intro l m u v t
    by_cases hM : XChain s (m'.loc.map (xwhL u' v')) s₁
    swap
    · rw [xev_of_not cs hM, Limits.comp_zero, Limits.zero_comp]; exact .zero
    by_cases hC : XChain s₁ ((capDots l m).map (xwhL u v)) t
    swap
    · rw [xev_of_not cs hC, Limits.comp_zero]; exact .zero
    have h₁ := (XChain.whisk_bdry m'.xChain_loc m'.loc_ne_nil hM).2
    have h₂ := (XChain.whisk_bdry (xChain_capDots l m) (capDots_ne_nil l m) hC).1
    rw [Category.assoc, ← xev_append cs _ hM]
    have he := h₁.symm.trans h₂
    clear h₁ h₂ hM hC
    cases m' with
    | dot l' =>
      rw [CMove.cod_dot] at he
      rcases pos_dot_cases he with ⟨c, hu, hv⟩ | ⟨hu, hl, hv⟩ | ⟨hu, hl, hv⟩ | ⟨c, hu, hv⟩
      · -- the dot is to the left of the cap
        subst u v'
        obtain ⟨p, hp⟩ := xev_swap cs ν (CMove.xChain_loc (.dot l')) (xChain_capDots l m) u' c v s t
        exact CupSpan.of_swap ν (fun r => ih l m (u' ++ [l'] ++ c) v r) (.dot l') u' (c ++ v)
          (z := zsign k p) (by simpa using hp)
      · -- the dot is on the left leg of the cap
        subst u' l' v'
        obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := letter_cases l
        · refine CupSpan.congr_list ν (L' := (capDots (dn i) (m + 1)).map (xwhL u v)) ?_
            (ih (dn i) (m + 1) u v t)
          rw [← dotUp_capDots_dn, List.map_append, map_xwhL_xwhL]
          simp
        · have hd : XChain [dn i, up i] ((CMove.dot (dn i)).loc.map (xwhL [] [up i]))
              [dn i, up i] := by simpa using xChain_dot_whisk (dn i) [] [up i]
          have hc : ∀ n, XChain [dn i, up i] (capDots (up i) n) [] := xChain_capDots (up i)
          obtain ⟨a, b, E⟩ := ddot_capDots_up cs (wt D ν v) i m
          refine CupSpan.congr_list ν (L' := ((CMove.dot (dn i)).loc.map (xwhL [] [up i]) ++
            capDots (up i) m).map (xwhL u v)) ?_ ?_
          · rw [List.map_append, map_xwhL_xwhL]
            simp
          rw [xev_eq_plcW ν u v (hd.append (hc m)) (by simp [capDots_ne_nil]), E, map_add,
            map_smul, map_smul, plcW_comp, Preadditive.comp_add, Linear.comp_smul,
            Linear.comp_smul, ← xev_eq_plcW ν u v (hc (m + 1)) (capDots_ne_nil _ _),
            ← xev_eq_plcW ν u v (hc m) (capDots_ne_nil _ _), ← Category.assoc]
          exact .add (.smul a (ih (up i) (m + 1) u v t))
            (.smul b (cupSpan_plcAt ν v u (ih (up i) m u v _) (isBub_oddBubble cs i _)))
      · -- the dot is on the right leg of the cap
        subst u' l' v'
        obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := letter_cases l
        · have hd : XChain [up i, dn i] ((CMove.dot (dn i)).loc.map (xwhL [up i] []))
              [up i, dn i] := by simpa using xChain_dot_whisk (dn i) [up i] []
          have hc : ∀ n, XChain [up i, dn i] (capDots (dn i) n) [] := xChain_capDots (dn i)
          obtain ⟨c, E⟩ := ddot_capDots_dn cs (wt D ν v) i m
          refine CupSpan.congr_list ν (L' := ((CMove.dot (dn i)).loc.map (xwhL [up i] []) ++
            capDots (dn i) m).map (xwhL u v)) ?_ ?_
          · rw [List.map_append, map_xwhL_xwhL]
            simp
          rw [xev_eq_plcW ν u v (hd.append (hc m)) (by simp [capDots_ne_nil]), E, map_smul,
            Linear.comp_smul, ← xev_eq_plcW ν u v (hc (m + 1)) (capDots_ne_nil _ _)]
          exact .smul c (ih (dn i) (m + 1) u v t)
        · refine CupSpan.congr_list ν (L' := (capDots (up i) (m + 1)).map (xwhL u v)) ?_
            (ih (up i) (m + 1) u v t)
          rw [← dotUp_capDots_up, List.map_append, map_xwhL_xwhL]
          simp
      · -- the dot is to the right of the cap
        subst u' v
        obtain ⟨p, hp⟩ :=
          xev_swap' cs ν (xChain_capDots l m) (CMove.xChain_loc (.dot l')) u c v' s t
        exact CupSpan.of_swap ν (fun r => ih l m u (c ++ [l'] ++ v') r) (.dot l') (u ++ c) v'
          (z := zsign k p) (by simpa using hp)
    | cup l' =>
      rw [CMove.cod_cup] at he
      rcases pos_cup_cases he with ⟨c, hu, hv⟩ | ⟨hu, hl, hv⟩ | ⟨hu, hl, -, hv⟩ |
        ⟨hu, hl, hv⟩ | ⟨c, hu, hv⟩
      · -- the cup is to the left of the cap
        subst u v'
        obtain ⟨p, hp⟩ := xev_swap cs ν (CMove.xChain_loc (.cup l')) (xChain_capDots l m) u' c v s t
        exact CupSpan.of_swap ν (fun r => ih l m (u' ++ c) v r) (.cup l') u' (c ++ v)
          (z := zsign k p) (by simpa using hp)
      · -- the right leg of the cup is the left leg of the cap: a zigzag
        have hl' : l' = l := by simpa using congrArg flipL hl
        subst l' u v'
        have h₁ : XChain [l] ((CMove.cup l).loc.map (xwhL [] [l])) [l, flipL l, l] := by
          simpa using xChain_cup_whisk l [] [l]
        have h₂ : XChain [l, flipL l, l] ((capDots l m).map (xwhL [l] [])) [l] := by
          simpa using (xChain_capDots l m).whisk [l] []
        have hmem : xev cs (wt D ν v) [l] [l] ((CMove.cup l).loc.map (xwhL [] [l]) ++
            (capDots l m).map (xwhL [l] [])) ∈ slideSetR cs (wt D ν v) l := by
          obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := letter_cases l
          exacts [zig_dn_left cs _ i m, zig_up_left cs _ i m]
        refine CupSpan.congr_list ν (L' := ((CMove.cup l).loc.map (xwhL [] [l]) ++
          (capDots l m).map (xwhL [l] [])).map (xwhL u' v)) ?_
          (cupSpan_local_slide ν hf (h₁.append h₂) (by simp [CMove.loc_ne_nil]) hmem)
        rw [List.map_append, map_xwhL_xwhL, map_xwhL_xwhL]
        simp
      · -- the cup closes up with the cap: a dotted bubble
        subst u' l' v'
        have h₁ : XChain [] (CMove.cup (flipL l)).loc [flipL l, l] := by
          simpa using CMove.xChain_loc (.cup (flipL l))
        refine CupSpan.congr_list ν
          (L' := ((CMove.cup (flipL l)).loc ++ capDots l m).map (xwhL u v)) (by simp) ?_
        rw [xev_eq_plcW ν u v (h₁.append (xChain_capDots l m)) (by simp [capDots_ne_nil])]
        exact cupSpan_plcAt ν v u hf (isBub_cup_capDots cs _ l m)
      · -- the left leg of the cup is the right leg of the cap: a zigzag
        subst u' l' v
        have h₁ : XChain [flipL l] ((CMove.cup l).loc.map (xwhL [flipL l] []))
            [flipL l, l, flipL l] := by
          simpa using xChain_cup_whisk l [flipL l] []
        have h₂ : XChain [flipL l, l, flipL l] ((capDots l m).map (xwhL [] [flipL l]))
            [flipL l] := by
          simpa using (xChain_capDots l m).whisk [] [flipL l]
        have hmem : xev cs (wt D ν v') [flipL l] [flipL l]
            ((CMove.cup l).loc.map (xwhL [flipL l] []) ++ (capDots l m).map (xwhL [] [flipL l])) ∈
            slideSetR cs (wt D ν v') (flipL l) := by
          obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := letter_cases l
          exacts [zig_dn_right cs _ i m, zig_up_right cs _ i m]
        refine CupSpan.congr_list ν (L' := ((CMove.cup l).loc.map (xwhL [flipL l] []) ++
          (capDots l m).map (xwhL [] [flipL l])).map (xwhL u v')) ?_
          (cupSpan_local_slide ν hf (h₁.append h₂) (by simp [CMove.loc_ne_nil]) hmem)
        rw [List.map_append, map_xwhL_xwhL, map_xwhL_xwhL]
        simp
      · -- the cup is to the right of the cap
        subst u' v
        obtain ⟨p, hp⟩ :=
          xev_swap' cs ν (xChain_capDots l m) (CMove.xChain_loc (.cup l')) u c v' s t
        exact CupSpan.of_swap ν (fun r => ih l m u (c ++ v') r) (.cup l') (u ++ c) v'
          (z := zsign k p) (by simpa using hp)
  | zero => intro l m u v t; rw [Limits.zero_comp]; exact .zero
  | add _ _ ih₁ ih₂ =>
    intro l m u v t; rw [Preadditive.add_comp]; exact .add (ih₁ l m u v t) (ih₂ l m u v t)
  | smul r _ ih => intro l m u v t; rw [Linear.smul_comp]; exact .smul r (ih l m u v t)

/-! ## The `♦`-cups and `♦`-caps -/

/-- **The `♦`-cup** keeps a 2-morphism in `CupSpan`: it vanishes for `n ≥ ⟨hᵢ,λ⟩`, and
otherwise it is a sum of clockwise bubbles followed by `η'` with dots ((5.11), Corollary 5.2). -/
theorem cupSpan_dcup {s : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f)
    (i : I) (n : ℕ) (a b t : List (Letter I)) :
    CupSpan cs ν t (f ≫ xev cs ν s t [(a, .gen (.dcup i n), b)]) := by
  have hA : XChain [] ((dcupL i n).map ofL) [up i, dn i] := XChain.of_sChain (sChain_dcupL i n)
  rw [show [(a, XShape.gen (.dcup i n), b)] = ((dcupL i n).map ofL).map (xwhL a b) by
    simp [dcupL, ofL], xev_eq_plcW ν a b hA (by simp [dcupL]), xev_map_ofL]
  by_cases hn : (n : ℤ) < D.h i (wt D ν b)
  · rw [eq_5_11 cs i _ n hn, dcupRHS, map_sum, Preadditive.comp_sum]
    refine CupSpan.sum ν _ fun r _ => ?_
    rw [map_smul, Linear.comp_smul]
    refine .smul _ ?_
    have hc : XChain [] (CMove.cup (up i)).loc [up i, dn i] := ⟨rfl, rfl⟩
    have hd : XChain [up i, dn i] ((xDots (up i) r).map (xwhL [] [dn i])) [up i, dn i] :=
      (xChain_xDots (up i) r).whisk [] [dn i]
    have E : etaP cs i (wt D ν b) ≫
        cl D Sc (wt D ν b) [up i, dn i] [up i, dn i] (dotsL [] i [dn i] r) =
          xev cs (wt D ν b) [] [up i, dn i]
            ((CMove.cup (up i)).loc ++ (xDots (up i) r).map (xwhL [] [dn i])) := by
      rw [xev_append cs _ hc, CMove.loc_cup_up, xev_lcup]
      congr 1
      exact (xev_dots_up cs (wt D ν b) [] [dn i] i r).symm
    rw [E, plcW_comp, ← xev_eq_plcW ν a b (hc.append hd) (by simp),
      ← Category.assoc, List.map_append, map_xwhL_xwhL]
    exact CupSpan.comp_append ν
      (fun _ => .move (.cup (up i)) a b (cupSpan_plcAt ν b a hf (isBub_bubR cs i _ _)))
      (fun _ _ _ hg => cupSpan_dots ν (up i) (a ++ []) ([dn i] ++ b) r hg)
  · rw [cl_dcupZero (Sc := Sc) i _ n (by omega), map_zero, Limits.comp_zero]; exact .zero

/-- **The `♦`-cap** keeps a 2-morphism in `CupSpan`: it vanishes for `n ≥ -⟨hᵢ,λ⟩`, and
otherwise it is a sum of `ε'` with dots followed by counterclockwise bubbles ((5.12),
Corollary 5.2). -/
theorem cupSpan_dcap {s : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f)
    (i : I) (n : ℕ) (a b t : List (Letter I)) :
    CupSpan cs ν t (f ≫ xev cs ν s t [(a, .gen (.dcap i n), b)]) := by
  have hA : XChain [dn i, up i] ((dcapL i n).map ofL) [] := XChain.of_sChain (sChain_dcapL i n)
  rw [show [(a, XShape.gen (.dcap i n), b)] = ((dcapL i n).map ofL).map (xwhL a b) by
    simp [dcapL, ofL], xev_eq_plcW ν a b hA (by simp [dcapL]), xev_map_ofL]
  by_cases hn : (n : ℤ) < -D.h i (wt D ν b)
  · rw [eq_5_12 cs i _ n hn, dcapRHS, map_sum, Preadditive.comp_sum]
    refine CupSpan.sum ν _ fun r _ => ?_
    rw [map_smul, Linear.comp_smul]
    refine .smul _ ?_
    have hc : XChain [dn i, up i] (capDots (up i) r) [] := xChain_capDots (up i) r
    have hd : XChain [dn i, up i] ((xDots (up i) r).map (xwhL [dn i] [])) [dn i, up i] :=
      (xChain_xDots (up i) r).whisk [dn i] []
    have E : cl D Sc (wt D ν b) [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r) ≫
        epsP cs i (wt D ν b) = xev cs (wt D ν b) [dn i, up i] [] (capDots (up i) r) := by
      show _ = xev cs (wt D ν b) [dn i, up i] []
        ((xDots (up i) r).map (xwhL [dn i] []) ++ [([], .lcap i, [])])
      rw [xev_append cs _ hd, xev_lcap]
      congr 1
      exact (xev_dots_up cs (wt D ν b) [dn i] [] i r).symm
    rw [← Category.assoc, E, plcW_comp, ← xev_eq_plcW ν a b hc (capDots_ne_nil _ _),
      ← Category.assoc]
    exact cupSpan_plcAt ν b a (cupSpan_cap ν hf (up i) r a b _) (isBub_bubL cs i _ _)
  · rw [cl_dcapZero (Sc := Sc) i _ n (by omega), map_zero, Limits.comp_zero]; exact .zero

/-! ## Closed crossingless diagrams -/

/-- **Every crossingless layer** keeps a 2-morphism in `CupSpan`. -/
theorem cupSpan_layer {s : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f)
    (x : XLayer I) (hx : x.2.1.isCross = false) (t : List (Letter I)) :
    CupSpan cs ν t (f ≫ xev cs ν s t [x]) := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | gen g =>
    cases g with
    | dot i =>
      exact CupSpan.congr_list ν (L' := (CMove.dot (up i)).loc.map (xwhL a b)) (by simp)
        (.move (.dot (up i)) a b hf)
    | cup i =>
      exact CupSpan.congr_list ν (L' := (CMove.cup (dn i)).loc.map (xwhL a b)) (by simp)
        (.move (.cup (dn i)) a b hf)
    | cap i =>
      exact CupSpan.congr_list ν (L' := (capDots (dn i) 0).map (xwhL a b))
        (by simp [capDots, xDots]) (cupSpan_cap ν hf (dn i) 0 a b t)
    | dcup i n => exact cupSpan_dcup ν hf i n a b t
    | dcap i n => exact cupSpan_dcap ν hf i n a b t
    | cross i j => simp [XShape.isCross, Shape.isCross] at hx
    | lcross i j => simp [XShape.isCross, Shape.isCross] at hx
  | lcup i =>
    exact CupSpan.congr_list ν (L' := (CMove.cup (up i)).loc.map (xwhL a b)) (by simp)
      (.move (.cup (up i)) a b hf)
  | lcap i =>
    exact CupSpan.congr_list ν (L' := (capDots (up i) 0).map (xwhL a b))
      (by simp [capDots, xDots]) (cupSpan_cap ν hf (up i) 0 a b t)

/-- **Crossingless diagrams** keep a 2-morphism in `CupSpan`. -/
theorem cupSpan_comp_xev : ∀ (L : List (XLayer I)), xcnt L = 0 →
    ∀ {s t : List (Letter I)} {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)},
      CupSpan cs ν s f → CupSpan cs ν t (f ≫ xev cs ν s t L)
  | [], _, s, t, f, hf => by
    by_cases h : s = t
    · subst h; rw [xev_nil, cl_nil, Category.comp_id]; exact hf
    · rw [xev_nil, cl_of_not (show ¬ SChain s [] t from h), Limits.comp_zero]; exact .zero
  | x :: L, hL, s, t, f, hf => by
    have hx : x.2.1.isCross = false := by
      by_contra h
      simp [xcnt, List.countP_cons, h] at hL
    have hL' : xcnt L = 0 := by simpa [xcnt, List.countP_cons, hx] using hL
    rw [show x :: L = [x] ++ L from rfl]
    exact CupSpan.comp_append ν (fun r => cupSpan_layer ν hf x hx r)
      (fun _ _ _ hg => cupSpan_comp_xev L hL' hg)

/-- On the empty sequence, `CupSpan` consists of elements of the image of `β_ν`: dots and cups
end on a nonempty sequence. -/
theorem CupSpan.isBub {s : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f) :
    IsBub cs ν (f ≫ cl D Sc ν s [] []) := by
  induction hf with
  | @bub β hβ => rw [cl_nil, Category.comp_id]; exact hβ
  | @move s t f m u v _ _ =>
    by_cases ht : t = []
    · subst ht
      have h : ¬ XChain s (m.loc.map (xwhL u v)) [] := fun h => by
        have := (XChain.whisk_bdry m.xChain_loc m.loc_ne_nil h).2
        cases m <;> simp at this
      rw [xev_of_not cs h, Limits.comp_zero, Limits.zero_comp]
      exact IsBub.zero
    · rw [cl_of_not (show ¬ SChain t [] [] from ht), Limits.comp_zero]
      exact IsBub.zero
  | zero => rw [Limits.zero_comp]; exact IsBub.zero
  | add _ _ ih₁ ih₂ => rw [Preadditive.add_comp]; exact ih₁.add ih₂
  | smul r _ ih => rw [Linear.smul_comp]; exact ih.smul r

/-- **[BE2] Theorem 8.1, (1.21)–(1.22), crossingless case**: a closed diagram on `1_ν` without
crossings (dots, cups, caps, `♦`-cups and `♦`-caps, all orientations) lies in the image of
`β_ν`. -/
theorem xev_isBub_of_xcnt_eq_zero (L : List (XLayer I)) (hL : xcnt L = 0) :
    IsBub cs ν (xev cs ν [] [] L) := by
  have h := (cupSpan_comp_xev ν L hL (t := []) (CupSpan.bub (IsBub.id (cs := cs) (ν := ν)))).isBub
  rwa [Category.id_comp, cl_nil, Category.comp_id] at h

/-- The crossingless part of the closed 2-morphisms on `1_ν` lies in the image of `β_ν`. -/
theorem leL_zero_le_bubbleSpan :
    LeL D Sc cs ν [] [] 0 ≤ Subalgebra.toSubmodule (bubbleSpan cs ν) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨L, hL, rfl⟩
  exact xev_isBub_of_xcnt_eq_zero ν L (Nat.le_zero.1 hL)

/-- **Reduction of [BE2] (1.21)–(1.22) to the removal of crossings**: if every closed
2-morphism on `1_ν` is a linear combination of crossingless diagrams, then `β_ν` is surjective
(its image `bubbleSpan` is everything). -/
theorem bubbleSpan_eq_top_of_mem_leL_zero
    (h : ∀ f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν []),
      f ∈ LeL D Sc cs ν [] [] 0) :
    bubbleSpan cs ν = ⊤ := by
  rw [eq_top_iff]
  intro f _
  exact leL_zero_le_bubbleSpan ν (h f)

end OddMath.SKM
