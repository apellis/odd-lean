/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.Envelope
import OddMath.SKM.RelationsNF

/-!
# The even two-strand summands

Brundan–Ellis, arXiv:1701.04133v2, the raw-idempotent decomposition underlying
Lemma 11.5. No global divided-power normalization is chosen here.
-/

noncomputable section

namespace OddMath.SKM.TwoStrand

open CategoryTheory StringDiagrams Presentation GradedSupercategory
open CategoryTheory.Idempotents CategoryTheory.Limits

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D)
  (hc : Sc.Homogeneous) (i : I) (ν : X)

/-- The two upward strands, with rightmost region `ν`. -/
def word : (show UGr D Sc sy hc from ⟨wt (X := X) D ν [up i, up i]⟩) ⟶
    (show UGr D Sc sy hc from ⟨ν⟩) :=
  ⟨ob D ν [up i, up i], rfl, ok_wd D ν _, ob_endR D ν _⟩

/-- The crossing. Multiplication in `End` is categorical composition, right factor first. -/
def t : End (word Sc sy hc i ν) := cl D Sc ν _ _ (crossL [] i i [])

/-- The rightmost dot. -/
def xr : End (word Sc sy hc i ν) := cl D Sc ν _ _ (dotsL [up i] i [] 1)

/-- The leftmost dot. -/
def xl : End (word Sc sy hc i ν) := cl D Sc ν _ _ (dotsL [] i [up i] 1)

variable {Sc sy hc i ν}

theorem t_sq : t Sc sy hc i ν * t Sc sy hc i ν = 0 := by
  change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 0
  rw [cl_comp (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)]
  exact cl_quadEq Sc i ν

theorem slideL (hi : D.parity i = 0) :
    t Sc sy hc i ν * xl Sc sy hc i ν = xr Sc sy hc i ν * t Sc sy hc i ν + 1 := by
  change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ =
    cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ + 𝟙 ((pres D Sc).obj (ob D ν [up i, up i]))
  rw [cl_comp (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩),
    cl_comp (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)]
  simpa only [hi, zero_mul, zsign_zero, one_smul, cl_nil] using cl_slideLEq Sc i ν

theorem slideR (hi : D.parity i = 0) :
    xl Sc sy hc i ν * t Sc sy hc i ν = t Sc sy hc i ν * xr Sc sy hc i ν + 1 := by
  change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ =
    cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ + 𝟙 ((pres D Sc).obj (ob D ν [up i, up i]))
  rw [cl_comp (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩),
    cl_comp (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)]
  simpa only [hi, zero_mul, zsign_zero, one_smul, cl_nil] using cl_slideREq Sc i ν

variable (Sc sy hc i ν)

/-- The raw BE2 idempotent `-T X_right`. -/
def e : End (word Sc sy hc i ν) := -(t Sc sy hc i ν * xr Sc sy hc i ν)

/-- The degree `2dᵢ` partial inverse. -/
def uMap : End (word Sc sy hc i ν) := xl Sc sy hc i ν * e Sc sy hc i ν

variable {Sc sy hc i ν}

theorem te : t Sc sy hc i ν * e Sc sy hc i ν = 0 := by
  simp only [e, mul_neg, ← mul_assoc, t_sq, zero_mul, neg_zero]

theorem et (hi : D.parity i = 0) : e Sc sy hc i ν * t Sc sy hc i ν = t Sc sy hc i ν := by
  have h := slideR (Sc := Sc) (sy := sy) (hc := hc) (ν := ν) hi
  have he : e Sc sy hc i ν = 1 - xl Sc sy hc i ν * t Sc sy hc i ν := by
    rw [h, e]; abel
  rw [he, sub_mul, one_mul, mul_assoc, t_sq, mul_zero, sub_zero]

theorem ee (hi : D.parity i = 0) : e Sc sy hc i ν * e Sc sy hc i ν = e Sc sy hc i ν := by
  change e Sc sy hc i ν * -(t Sc sy hc i ν * xr Sc sy hc i ν) = _
  rw [mul_neg, ← mul_assoc, et hi]; rfl

theorem tu (hi : D.parity i = 0) : t Sc sy hc i ν * uMap Sc sy hc i ν = e Sc sy hc i ν := by
  rw [uMap, ← mul_assoc, slideL hi, add_mul, mul_assoc, te, mul_zero, one_mul, zero_add]

theorem ut (hi : D.parity i = 0) : uMap Sc sy hc i ν * t Sc sy hc i ν = 1 - e Sc sy hc i ν := by
  rw [uMap, mul_assoc, et hi, slideR hi, e]; abel

theorem ue (hi : D.parity i = 0) : uMap Sc sy hc i ν * e Sc sy hc i ν = uMap Sc sy hc i ν := by
  rw [uMap, mul_assoc, ee hi]

theorem eu (hi : D.parity i = 0) : e Sc sy hc i ν * uMap Sc sy hc i ν = 0 := by
  have h : e Sc sy hc i ν = 1 - uMap Sc sy hc i ν * t Sc sy hc i ν := by
    rw [ut hi]; abel
  conv_lhs => lhs; rw [h]
  rw [sub_mul, one_mul, mul_assoc, tu hi, ue hi, sub_self]

theorem cl_degree {ls : List (LayerData I)}
    (hs : SChain [up i, up i] ls [up i, up i]) {n : ℤ}
    (hn : gsum D sy ν ls = n) :
    (cl D Sc ν _ _ ls : End (word Sc sy hc i ν)) ∈
      degree (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) n := by
  change cl D Sc ν _ _ ls ∈ (pres D Sc).homDeg (gdeg D sy) _ _ n
  rw [cl_of hs]
  exact diag_mem_homDeg' ((degree_gdeg_mkD D sy ν ls hs).trans hn)

theorem cl_even {ls : List (LayerData I)}
    (hs : SChain [up i, up i] ls [up i, up i])
    (hn : (ls.map fun x => x.2.1.parity D).sum = 0) :
    (cl D Sc ν _ _ ls : End (word Sc sy hc i ν)) ∈
      Supercategory.parity (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) 0 := by
  change cl D Sc ν _ _ ls ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ 0
  rw [cl_of hs]
  exact diag_mem_homDeg' ((degree_parity_mkD D ν ls hs).trans hn)

theorem t_degree : t Sc sy hc i ν ∈
    degree (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) (-(2 * sy.d i)) := by
  apply cl_degree (ls := crossL [] i i []) ⟨rfl, rfl⟩
  simp [Datum.d_self, mul_comm]

theorem xr_degree : xr Sc sy hc i ν ∈
    degree (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) (2 * sy.d i) :=
  cl_degree (ls := dotsL [up i] i [] 1) ⟨rfl, rfl⟩ (by simp)

theorem xl_degree : xl Sc sy hc i ν ∈
    degree (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) (2 * sy.d i) :=
  cl_degree (ls := dotsL [] i [up i] 1) ⟨rfl, rfl⟩ (by simp)

theorem t_even (hi : D.parity i = 0) : t Sc sy hc i ν ∈
    Supercategory.parity (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) 0 :=
  cl_even ⟨rfl, rfl⟩ (by simp [crossL, Shape.parity, hi])

theorem xr_even (hi : D.parity i = 0) : xr Sc sy hc i ν ∈
    Supercategory.parity (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) 0 :=
  cl_even ⟨rfl, rfl⟩ (by simp [dotsL, Shape.parity, hi])

theorem xl_even (hi : D.parity i = 0) : xl Sc sy hc i ν ∈
    Supercategory.parity (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) 0 :=
  cl_even ⟨rfl, rfl⟩ (by simp [dotsL, Shape.parity, hi])

theorem e_degree : e Sc sy hc i ν ∈
    degree (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) 0 := by
  apply Submodule.neg_mem
  simpa using comp_mem_degree (xr_degree (Sc := Sc) (hc := hc) (ν := ν)) t_degree

theorem e_even (hi : D.parity i = 0) : e Sc sy hc i ν ∈
    Supercategory.parity (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) 0 := by
  apply Submodule.neg_mem
  simpa using Supercategory.comp_mem (xr_even (Sc := Sc) (hc := hc) (ν := ν) hi) (t_even hi)

theorem u_degree : uMap Sc sy hc i ν ∈
    degree (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) (2 * sy.d i) := by
  simpa [uMap] using comp_mem_degree (e_degree (Sc := Sc) (hc := hc) (ν := ν)) xl_degree

theorem u_even (hi : D.parity i = 0) : uMap Sc sy hc i ν ∈
    Supercategory.parity (R := k) (word Sc sy hc i ν) (word Sc sy hc i ν) 0 := by
  simpa [uMap] using Supercategory.comp_mem (e_even (Sc := Sc) (hc := hc) (ν := ν) hi) (xl_even hi)

variable (Sc sy hc i ν)

/-- The hom category before taking the additive Karoubi envelope. -/
abbrev Base := GUnderlying k (QPiEnvelope k
  ((show UGr D Sc sy hc from ⟨wt (X := X) D ν [up i, up i]⟩) ⟶
    (show UGr D Sc sy hc from ⟨ν⟩)))

/-- The formal degree shift of the two-strand word. -/
def shiftedWord (n : ℤ) : Base Sc sy hc i ν := ⟨⟨⟨0, ⟨n, word Sc sy hc i ν⟩⟩⟩⟩

/-- A homogeneous even endomorphism, viewed between its appropriate shifts. -/
def lift {m n : ℤ} (f : End (word Sc sy hc i ν))
    (hd : f ∈ degree (R := k) _ _ (m - n))
    (hp : f ∈ Supercategory.parity (R := k) _ _ 0) :
    shiftedWord Sc sy hc i ν m ⟶ shiftedWord Sc sy hc i ν n :=
  ⟨⟨f, by change f ∈ degree (R := k) _ _ (0 + (m - n)); simpa using hd⟩,
    by change f ∈ Supercategory.parity (R := k) _ _ (0 + (0 + 0)); simpa using hp⟩

/-- The raw idempotent at shift `n`; this is not a normalized divided power. -/
def projector (hi : D.parity i = 0) (n : ℤ) : End (shiftedWord Sc sy hc i ν n) :=
  lift Sc sy hc i ν (e Sc sy hc i ν) (by simpa using e_degree (Sc := Sc) (hc := hc) (ν := ν))
    (e_even hi)

/-- The raw homogeneous Karoubi summand at degree shift `n`. -/
def raw (hi : D.parity i = 0) (n : ℤ) :
    (GSKAR.mkObj k (UGr D Sc sy hc) ⟨wt (X := X) D ν [up i, up i]⟩ ⟶
      GSKAR.mkObj k (UGr D Sc sy hc) ⟨ν⟩) where
  X := (Mat_.embedding _).obj (shiftedWord Sc sy hc i ν n)
  p := (Mat_.embedding _).map (projector Sc sy hc i ν hi n)
  idem := by
    rw [← Functor.map_comp]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    exact ee hi

/-- The unsplit two-strand object in `UDot`. -/
def whole :
    (GSKAR.mkObj k (UGr D Sc sy hc) ⟨wt (X := X) D ν [up i, up i]⟩ ⟶
      GSKAR.mkObj k (UGr D Sc sy hc) ⟨ν⟩) :=
  (toKaroubi _).obj ((Mat_.embedding _).obj (shiftedWord Sc sy hc i ν 0))

/-- The shifted crossing, from shift zero to shift `2dᵢ`. -/
def vLift (hi : D.parity i = 0) :
    shiftedWord Sc sy hc i ν 0 ⟶ shiftedWord Sc sy hc i ν (2 * sy.d i) :=
  lift Sc sy hc i ν (t Sc sy hc i ν) (by simpa using t_degree (Sc := Sc) (hc := hc) (ν := ν))
    (t_even hi)

/-- The shifted partial inverse, from shift `2dᵢ` to shift zero. -/
def uLift (hi : D.parity i = 0) :
    shiftedWord Sc sy hc i ν (2 * sy.d i) ⟶ shiftedWord Sc sy hc i ν 0 :=
  lift Sc sy hc i ν (uMap Sc sy hc i ν)
    (by simpa using u_degree (Sc := Sc) (hc := hc) (ν := ν)) (u_even hi)

/-- Projection onto the raw summand. -/
def proj0 (hi : D.parity i = 0) : whole Sc sy hc i ν ⟶ raw Sc sy hc i ν hi 0 where
  f := (Mat_.embedding _).map (projector Sc sy hc i ν hi 0)
  comm := by
    change 𝟙 _ ≫ _ ≫ _ = _
    simp only [raw, Category.id_comp]
    rw [← Functor.map_comp]
    congr 1
    exact Subtype.ext (Subtype.ext (ee hi))

/-- Inclusion of the raw summand. -/
def incl0 (hi : D.parity i = 0) : raw Sc sy hc i ν hi 0 ⟶ whole Sc sy hc i ν where
  f := (Mat_.embedding _).map (projector Sc sy hc i ν hi 0)
  comm := by
    change _ ≫ _ ≫ 𝟙 _ = _
    simp only [raw, Category.comp_id]
    rw [← Functor.map_comp]
    congr 1
    exact Subtype.ext (Subtype.ext (ee hi))

/-- Projection onto the shifted raw summand, given by `T`. -/
def proj1 (hi : D.parity i = 0) :
    whole Sc sy hc i ν ⟶ raw Sc sy hc i ν hi (2 * sy.d i) where
  f := (Mat_.embedding _).map (vLift Sc sy hc i ν hi)
  comm := by
    change 𝟙 _ ≫ _ ≫ _ = _
    simp only [raw, Category.id_comp]
    rw [← Functor.map_comp]
    congr 1
    exact Subtype.ext (Subtype.ext (et hi))

/-- Inclusion of the shifted raw summand, given by `X_left e`. -/
def incl1 (hi : D.parity i = 0) :
    raw Sc sy hc i ν hi (2 * sy.d i) ⟶ whole Sc sy hc i ν where
  f := (Mat_.embedding _).map (uLift Sc sy hc i ν hi)
  comm := by
    change _ ≫ _ ≫ 𝟙 _ = _
    simp only [raw, Category.comp_id]
    rw [← Functor.map_comp]
    congr 1
    exact Subtype.ext (Subtype.ext (ue hi))

variable {Sc sy hc i ν}

@[reassoc (attr := simp)]
theorem incl0_proj0 (hi : D.parity i = 0) :
    incl0 Sc sy hc i ν hi ≫ proj0 Sc sy hc i ν hi = 𝟙 _ := by
  apply Karoubi.hom_ext
  change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = (Mat_.embedding _).map _
  rw [← Functor.map_comp]
  congr 1
  exact Subtype.ext (Subtype.ext (ee hi))

@[reassoc (attr := simp)]
theorem incl0_proj1 (hi : D.parity i = 0) :
    incl0 Sc sy hc i ν hi ≫ proj1 Sc sy hc i ν hi = 0 := by
  apply Karoubi.hom_ext
  change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 0
  rw [← Functor.map_comp, ← Functor.map_zero (Mat_.embedding _)]
  congr 1
  exact Subtype.ext (Subtype.ext te)

@[reassoc (attr := simp)]
theorem incl1_proj0 (hi : D.parity i = 0) :
    incl1 Sc sy hc i ν hi ≫ proj0 Sc sy hc i ν hi = 0 := by
  apply Karoubi.hom_ext
  change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 0
  rw [← Functor.map_comp, ← Functor.map_zero (Mat_.embedding _)]
  congr 1
  exact Subtype.ext (Subtype.ext (eu hi))

@[reassoc (attr := simp)]
theorem incl1_proj1 (hi : D.parity i = 0) :
    incl1 Sc sy hc i ν hi ≫ proj1 Sc sy hc i ν hi = 𝟙 _ := by
  apply Karoubi.hom_ext
  change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = (Mat_.embedding _).map _
  rw [← Functor.map_comp]
  congr 1
  exact Subtype.ext (Subtype.ext (tu hi))

theorem total (hi : D.parity i = 0) :
    proj0 Sc sy hc i ν hi ≫ incl0 Sc sy hc i ν hi +
      proj1 Sc sy hc i ν hi ≫ incl1 Sc sy hc i ν hi = 𝟙 _ := by
  apply Karoubi.hom_ext
  change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ +
    (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 𝟙 _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add]
  change (Mat_.embedding (Base Sc sy hc i ν)).map _ =
    𝟙 ((Mat_.embedding (Base Sc sy hc i ν)).obj (shiftedWord Sc sy hc i ν 0))
  rw [← (Mat_.embedding (Base Sc sy hc i ν)).map_id]
  congr 1
  apply Subtype.ext; apply Subtype.ext
  change e Sc sy hc i ν * e Sc sy hc i ν + uMap Sc sy hc i ν * t Sc sy hc i ν = 1
  rw [ee hi, ut hi]; abel

variable (Sc sy hc i ν)

/-- The raw even two-strand decomposition in the actual `UDot` hom category.
The second summand is the raw idempotent on `Q^(2dᵢ) Eᵢ²1_ν`.
This positive shift is forced by the envelope degree convention. -/
def decomposition (hi : D.parity i = 0) :
    whole Sc sy hc i ν ≅ raw Sc sy hc i ν hi 0 ⊞ raw Sc sy hc i ν hi (2 * sy.d i) where
  hom := biprod.lift (proj0 Sc sy hc i ν hi) (proj1 Sc sy hc i ν hi)
  inv := biprod.desc (incl0 Sc sy hc i ν hi) (incl1 Sc sy hc i ν hi)
  hom_inv_id := by rw [biprod.lift_desc]; exact total hi
  inv_hom_id := by
    ext <;> simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc,
      biprod.lift_fst, biprod.lift_snd, Category.comp_id, BinaryBicone.inl_fst,
      BinaryBicone.inl_snd, BinaryBicone.inr_fst, BinaryBicone.inr_snd]
    · exact incl0_proj0 hi
    · exact incl0_proj1 hi
    · exact incl1_proj0 hi
    · exact incl1_proj1 hi

/-- The two-strand relation in the split Grothendieck group of the `UDot` hom. -/
theorem class_decomposition (hi : D.parity i = 0) :
    K₀.mk (whole Sc sy hc i ν) =
      K₀.mk (raw Sc sy hc i ν hi 0) + K₀.mk (raw Sc sy hc i ν hi (2 * sy.d i)) := by
  rw [K₀.mk_eq_mk_of_iso (decomposition Sc sy hc i ν hi), K₀.mk_biprod]

end OddMath.SKM.TwoStrand
