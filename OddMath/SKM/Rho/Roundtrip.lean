import OddMath.SKM.Rho.Extension

/-!
# Roundtrip for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/

noncomputable section
namespace OddMath.SKM.RhoInverse
open CategoryTheory StringDiagrams BicategoryStruct RhoWords RhoTwo RhoExtension
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

theorem rhoWord_involutive (s : List (Letter I)) : rhoWord (rhoWord s) = s := by
  change (flipW ((flipW s).reverse)).reverse = s
  rw [show flipW ((flipW s).reverse) = (flipW (flipW s)).reverse by
    simp only [flipW, List.map_reverse], flipW_flipW, List.reverse_reverse]

theorem rhoLetterShift_reverse (μ : X) (l : Letter I) :
    rhoLetterShift sy (μ + sh D l) (flipL l) = -rhoLetterShift sy μ l := by
  rcases l with ⟨b, i⟩
  cases b <;> simp only [rhoLetterShift, flipL, sh, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Datum.h, Datum.α, map_add, map_neg,
    D.cd.coroot_root_self] <;> ring

theorem rhoShift_reverse (μ : X) (s : List (Letter I)) :
    rhoShift sy (wt D μ s) (rhoWord s) = -rhoShift sy μ s := by
  induction s with
  | nil => simp [rhoShift]
  | cons l s ih =>
    rw [rhoWord_cons, rhoShift_append]
    have h : wt D (wt D μ (l :: s)) [flipL l] = wt D μ s := by
      simp [wt, sh_flipL]
    rw [h, ih]
    simp only [rhoShift, wt_nil, add_zero]
    rw [show wt D μ (l :: s) = wt D μ s + sh D l from add_comm _ _,
      rhoLetterShift_reverse]
    ring

open QPiSupercategory Envelope
local instance (a b : TwoSRev k (Uqπ D Sc sy hc)) : QPiSupercategory k (a ⟶ b) :=
  QPiTwoSupercategory.homQPiLeft a b

theorem qPowNat_normal {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (n : ℕ) :
    qPowNat k n f = ⟨f.par, ⟨(n : ℤ) + f.obj.shift, f.obj.obj⟩⟩ := by
  induction n with
  | zero => simp only [qPowNat, Nat.cast_zero, zero_add]; rfl
  | succ n ih =>
    rw [qPowNat, ih]
    apply Envelope.ext
    · change 0 + f.par = _; exact zero_add _
    · apply QEnvelope.ext
      · change 1 + ((n : ℤ) + f.obj.shift) = _; push_cast; omega
      · apply Presentation.Bicat.Hom.ext
        apply Obj.ext
        · exact f.obj.obj.start_eq.symm
        · rfl

theorem qinvPowNat_normal {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (n : ℕ) :
    qinvPowNat k n f = ⟨f.par, ⟨-(n : ℤ) + f.obj.shift, f.obj.obj⟩⟩ := by
  induction n with
  | zero => simp only [qinvPowNat, Nat.cast_zero, neg_zero, zero_add]; rfl
  | succ n ih =>
    rw [qinvPowNat, ih]
    apply Envelope.ext
    · change 0 + f.par = _; exact zero_add _
    · apply QEnvelope.ext
      · change -1 + (-(n : ℤ) + f.obj.shift) = _; push_cast; omega
      · apply Presentation.Bicat.Hom.ext
        apply Obj.ext
        · exact f.obj.obj.start_eq.symm
        · rfl

theorem qPow_normal {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (m : ℤ) :
    qPow k m f = ⟨f.par, ⟨m + f.obj.shift, f.obj.obj⟩⟩ := by
  cases m with
  | ofNat n => exact qPowNat_normal f n
  | negSucc n => simpa only [qPow, Int.negSucc_eq, Nat.cast_add, Nat.cast_one] using
      qinvPowNat_normal f (n + 1)

theorem piPow_normal {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (p : ZMod 2) :
    piPow k p f = ⟨p + f.par, f.obj⟩ := by
  fin_cases p
  · change f = ⟨(0 : ZMod 2) + f.par, f.obj⟩
    rw [zero_add]
    rfl
  · change (PiSupercategory.pi (R := k)).obj f = ⟨(1 : ZMod 2) + f.par, f.obj⟩
    apply Envelope.ext
    · rfl
    · apply QEnvelope.ext
      · exact zero_add _
      · apply Presentation.Bicat.Hom.ext
        apply Obj.ext
        · exact f.obj.obj.start_eq.symm
        · rfl

theorem rhoEnvelope_map_par (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    ((rhoEnvelope t ht).map f).par = f.par := by
  rw [rhoEnvelope_map, piPow_normal, qPow_normal]
  exact add_zero _

theorem rhoEnvelope_map_shift (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    ((rhoEnvelope t ht).map f).obj.shift =
      rhoShift sy b.as.as.region (f.obj.obj.obj.word.map Col.l) + f.obj.shift := by
  rw [rhoEnvelope_map, piPow_normal, qPow_normal]
  exact add_comm _ _

theorem rhoEnvelope_map_word (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    ((rhoEnvelope t ht).map f).obj.obj.obj =
      ob D a.as.as.region (rhoWord (f.obj.obj.obj.word.map Col.l)) := by
  rw [rhoEnvelope_map, piPow_normal, qPow_normal]
  rfl

theorem rhoEnvelope_map_roundtrip (t u : k) (ht : t ^ 2 = -1) (hu : u ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (rhoEnvelope u hu).map ((rhoEnvelope t ht).map f) = f := by
  apply Envelope.ext
  · rw [rhoEnvelope_map_par, rhoEnvelope_map_par]
  · apply QEnvelope.ext
    · rw [rhoEnvelope_map_shift, rhoEnvelope_map_shift]
      change rhoShift sy a.as.as.region
        (((rhoEnvelope t ht).map f).obj.obj.obj.word.map Col.l) +
          (rhoShift sy b.as.as.region (f.obj.obj.obj.word.map Col.l) + f.obj.shift) = _
      rw [rhoEnvelope_map_word]
      change rhoShift sy a.as.as.region
        ((wd D a.as.as.region (rhoWord (f.obj.obj.obj.word.map Col.l))).map Col.l) + _ = _
      rw [wd_map_l, ← hom_wt f.obj.obj, rhoShift_reverse]
      omega
    · apply Presentation.Bicat.Hom.ext
      rw [rhoEnvelope_map_word, rhoEnvelope_map_word]
      change ob D b.as.as.region
        (rhoWord ((wd D a.as.as.region (rhoWord (f.obj.obj.obj.word.map Col.l))).map Col.l)) = _
      rw [wd_map_l, rhoWord_involutive]
      obtain ⟨hw, hs⟩ := word_eq_wd (D := D) f.obj.obj.obj.start f.obj.obj.obj.word f.obj.obj.wf
      change f.obj.obj.obj.word = wd D f.obj.obj.obj.endR _ at hw
      change f.obj.obj.obj.start = wt D f.obj.obj.obj.endR _ at hs
      rw [f.obj.obj.endR_eq] at hw hs
      exact Obj.ext hs.symm hw.symm
end OddMath.SKM.RhoInverse
