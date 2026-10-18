import OddMath.SKM.RhoGenerators
import OddMath.SKM.ChevalleyInv

/-!
# Words for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/

noncomputable section
namespace OddMath.SKM.RhoWords
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def rhoWord (s : List (Letter I)) : List (Letter I) := (flipW s).reverse

@[simp] theorem rhoWord_nil : rhoWord ([] : List (Letter I)) = [] := rfl
@[simp] theorem rhoWord_cons (l : Letter I) (s : List (Letter I)) :
    rhoWord (l :: s) = rhoWord s ++ [flipL l] := by simp [rhoWord]
@[simp] theorem rhoWord_append (s t : List (Letter I)) :
    rhoWord (s ++ t) = rhoWord t ++ rhoWord s := by simp [rhoWord]

theorem rhoWord_wt (μ : X) (s : List (Letter I)) :
    wt D (wt D μ s) (rhoWord s) = μ := by
  induction s with
  | nil => rfl
  | cons l s ih =>
    rw [rhoWord_cons, wt_append]
    have h : wt D (wt D μ (l :: s)) [flipL l] = wt D μ s := by
      simp [wt, sh_flipL]
    rw [h, ih]

def rhoLetterShift (sy : Symmetrizer D) (μ : X) (l : Letter I) : ℤ :=
  if l.1 then -(sy.d l.2 * (1 + D.h l.2 μ)) else sy.d l.2 * (D.h l.2 μ - 1)

def rhoShift (sy : Symmetrizer D) (μ : X) : List (Letter I) → ℤ
  | [] => 0
  | l :: s => rhoLetterShift sy (wt D μ s) l + rhoShift sy μ s

theorem rhoShift_append (μ : X) (s t : List (Letter I)) :
    rhoShift sy μ (s ++ t) = rhoShift sy (wt D μ t) s + rhoShift sy μ t := by
  induction s with
  | nil => simp [rhoShift]
  | cons l s ih => simp only [List.cons_append, rhoShift, wt_append, ih]; omega

theorem hom_wt {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    wt D b.region (f.obj.word.map Col.l) = a.region := by
  obtain ⟨_, hs⟩ := word_eq_wd (D := D) f.obj.start f.obj.word f.wf
  change f.obj.start = wt D f.obj.endR _ at hs
  rw [f.endR_eq] at hs
  exact hs.symm.trans f.start_eq

def rhoMap {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    rhoObj (Sc := Sc) (sy := sy) (hc := hc) a.region ⟶ rhoObj b.region :=
  Envelope.mk 0 (QEnvelope.mk (rhoShift sy b.region (f.obj.word.map Col.l))
    (psiWordAt (D := D) (Sc := Sc) b.region a.region (rhoWord (f.obj.word.map Col.l))
      (by rw [← hom_wt f]; exact rhoWord_wt _ _)))

@[simp] theorem rhoMap_par {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rhoMap f).par = 0 := rfl
@[simp] theorem rhoMap_shift {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rhoMap f).obj.shift = rhoShift sy b.region (f.obj.word.map Col.l) := rfl
@[simp] theorem rhoMap_obj {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rhoMap f).obj.obj.obj = ob D a.region (rhoWord (f.obj.word.map Col.l)) := rfl

theorem rhoMap_id (a : UGr D Sc sy hc) :
    rhoMap (𝟙 a) = 𝟙 (rhoObj (Sc := Sc) (sy := sy) (hc := hc) a.region) := by
  apply Envelope.ext
  · rfl
  · apply QEnvelope.ext
    · rfl
    · apply Presentation.Bicat.Hom.ext
      rfl

theorem rhoMap_comp {a b c : UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    rhoMap (f ≫ g) = rhoMap f ≫ rhoMap g := by
  apply Envelope.ext
  · rfl
  · apply QEnvelope.ext
    · change rhoShift sy c.region ((f.obj.word ++ g.obj.word).map Col.l) =
        rhoShift sy c.region (g.obj.word.map Col.l) + rhoShift sy b.region (f.obj.word.map Col.l)
      rw [List.map_append, rhoShift_append, hom_wt g, add_comm]
    · apply Presentation.Bicat.Hom.ext
      change ob D a.region (rhoWord ((f.obj.word ++ g.obj.word).map Col.l)) =
        (ob D b.region (rhoWord (g.obj.word.map Col.l))).tensor
          (ob D a.region (rhoWord (f.obj.word.map Col.l)))
      rw [List.map_append, rhoWord_append]
      have h : wt D a.region (rhoWord (f.obj.word.map Col.l)) = b.region := by
        rw [← hom_wt f]; exact rhoWord_wt _ _
      apply Obj.ext
      · change wt D a.region (_ ++ _) = wt D b.region _
        rw [wt_append, h]
      · change wd D a.region (_ ++ _) = wd D b.region _ ++ wd D a.region _
        rw [wd_append, h]

theorem rhoMap_wordAt (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :
    rhoMap (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s h) =
      Envelope.mk 0 (QEnvelope.mk (rhoShift sy μ s)
        (psiWordAt μ ν (rhoWord s) (h ▸ rhoWord_wt μ s))) := by
  apply Envelope.ext
  · rfl
  · apply QEnvelope.ext
    · change rhoShift sy μ ((wd D μ s).map Col.l) = rhoShift sy μ s
      rw [wd_map_l]
    · apply Presentation.Bicat.Hom.ext
      change ob D ν (rhoWord ((wd D μ s).map Col.l)) = ob D ν (rhoWord s)
      rw [wd_map_l]

theorem rhoWord_ups (s : List I) : rhoWord (ups s) = dns s := by
  simp only [rhoWord, flipW, ups, dns, List.map_map]
  rfl

theorem rhoShift_ups (μ : X) (s : List I) : rhoShift sy μ (ups s) = rhoUpShift sy μ s := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    change rhoLetterShift sy (wt D μ (ups s)) (up i) + rhoShift sy μ (ups s) = _
    rw [ih]
    rfl

theorem rhoMap_upAt (ν μ : X) (s : List I) (h : wt D μ (ups s) = ν) :
    rhoMap (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ (ups s) h) = rhoUpAt ν μ s h := by
  apply Envelope.ext
  · rfl
  · apply QEnvelope.ext
    · change rhoShift sy μ ((wd D μ (ups s)).map Col.l) = rhoUpShift sy μ s
      rw [wd_map_l, rhoShift_ups]
    · apply Presentation.Bicat.Hom.ext
      change ob D ν (rhoWord ((wd D μ (ups s)).map Col.l)) = ob D ν (dns s)
      rw [wd_map_l, rhoWord_ups]

theorem rhoMap_E (μ : X) (i : I) :
    rhoMap (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [up i]) = rhoE μ i :=
  rhoMap_upAt _ _ [i] rfl

theorem rhoMap_F (μ : X) (i : I) :
    rhoMap (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [dn i]) = rhoF μ i := by
  apply Envelope.ext
  · rfl
  · apply QEnvelope.ext
    · change sy.d i * (D.h i μ - 1) + 0 = sy.d i * (D.h i μ - 1)
      exact add_zero _
    · apply Presentation.Bicat.Hom.ext
      rfl

end OddMath.SKM.RhoWords
