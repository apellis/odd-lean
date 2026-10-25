/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.UpwardCoefficientDetection
import OddMath.SKM.PositiveMatchingDots

/-! # Exact upward evaluation of positioned affine words -/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams StringDiagrams.Chord
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

def PG.toDTMove : PG → SKM.DTMove I
  | .dot p => .dt p
  | .cross p => .tm (.mv (.cross p))

theorem upLayers_dot (t : List I) (p : ℕ) :
    (upLayers ((PG.dot p).ld t)).map SKM.ofL = SKM.dotOn (upWord t) p := by
  simp only [PG.ld, SKM.dotOn, upWord, ← List.map_drop, ← List.map_take]
  cases h : t.drop p with
  | nil => simp [upLayers]
  | cons i r => simp [upLayers, SKM.xDotL_up, SKM.xwhL, SKM.ofL, upWord, Shape.toSKM]

theorem upLayers_positioned_cross (t : List I) (p : ℕ) :
    (upLayers ((PG.cross p).ld t)).map SKM.ofL = SKM.tmLay (upWord t) (.mv (.cross p)) := by
  simp only [PG.ld, SKM.tmLay, SKM.moveLay, upWord, ← List.map_drop, ← List.map_take]
  cases h : t.drop p with
  | nil => simp [upLayers]
  | cons i r =>
    cases r with
    | nil => simp [upLayers]
    | cons j r => simp [upLayers, SKM.xCrL_up_up, SKM.xwhL, SKM.ofL, upWord, Shape.toSKM]

theorem upWord_cross_act {t : List I} {p : ℕ} (hp : p + 1 < t.length) :
    upWord ((PG.cross p).act t) = SKM.tLet (upWord t) (.mv (.cross p)) := by
  obtain ⟨l, i, j, r, rfl, rfl⟩ := SKM.exists_split_cross hp
  simpa [PG.act, upWord, SKM.tLet] using
    (SKM.chStep_cross (l.map SKM.up) (r.map SKM.up) (SKM.up i) (SKM.up j)).symm

theorem upLayers_pl (t : List I) (gs : List PG)
    (hg : ∀ g ∈ gs, g.pos + g.width ≤ t.length) :
    (upLayers (pl t gs)).map SKM.ofL = SKM.dLay (upWord t) (gs.map PG.toDTMove) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    have htail : ∀ h ∈ gs, h.pos + h.width ≤ (g.act t).length := by
      intro h hh
      simpa only [length_act] using hg h (List.mem_cons_of_mem g hh)
    have hhead := hg g List.mem_cons_self
    cases g with
    | dot p =>
      simpa only [pl, upLayers, List.map_append, List.map_cons, PG.toDTMove, SKM.dLay,
        PG.act] using congrArg₂ (· ++ ·) (upLayers_dot t p) (ih t htail)
    | cross p =>
      have hp : p + 1 < t.length := by simp only [PG.pos, PG.width] at hhead; omega
      have he := ih ((PG.cross p).act t) htail
      rw [upWord_cross_act hp] at he
      simpa only [pl, upLayers, List.map_append, List.map_cons, PG.toDTMove, SKM.dLay]
        using congrArg₂ (· ++ ·) (upLayers_positioned_cross t p) he

theorem alpha_cl (μ : X) {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    (alpha D Sc μ).map (cl D Sc t t' gs h) =
      SKM.cl D Sc μ (upWord t) (upWord t') (upLayers (pl t gs)) := by
  rw [cl, alpha_diag, label_mkD, SKM.cl_of h.up]

theorem alpha_cl_eq_xev (μ : X) {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t')
    (hg : ∀ g ∈ gs, g.pos + g.width ≤ t.length) :
    (alpha D Sc μ).map (cl D Sc t t' gs h) =
      SKM.xev cs μ (upWord t) (upWord t') (SKM.dLay (upWord t) (gs.map PG.toDTMove)) := by
  rw [← upLayers_pl t gs hg, SKM.xev_map_ofL]
  exact alpha_cl D Sc μ gs h

theorem NFIdx.valid_positioned {t t' : List I} (i : NFIdx t t') :
    ∀ g ∈ i.1.1.map PG.dot ++ cw (Categorification.TypeA.canWord t.length i.1.2),
      g.pos + g.width ≤ t.length := by
  intro g hg
  rcases List.mem_append.mp hg with hd | hc
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
    have := i.2.2.1 p hp
    simp only [PG.pos, PG.width]
    omega
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hv := Categorification.TypeA.validWord_canWord t.length i.1.2 p (List.mem_reverse.mp hp)
    simp only [PG.pos, PG.width]
    omega

/-- Exact affine PBW diagram in the decorated-matching syntax, with sorted
bottom dots followed by the reversed canonical crossing word. -/
theorem alpha_nf_eq_xev (μ : X) {t t' : List I} (i : NFIdx t t') :
    (alpha D Sc μ).map (i.nf (D := D) (Sc := Sc)) =
      SKM.xev cs μ (upWord t) (upWord t')
        (SKM.dLay (upWord t)
          ((i.1.1.map PG.dot ++ cw (Categorification.TypeA.canWord t.length i.1.2)).map PG.toDTMove)) :=
  alpha_cl_eq_xev D Sc cs μ _ i.2.2.2 i.valid_positioned

end OddMath.QuiverHecke
