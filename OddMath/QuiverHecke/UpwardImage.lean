/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.UpwardClasses
import OddMath.QuiverHecke.EnvelopeSerre

/-!
# Upward classes lie in the image of `γ`

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, class step for upward
words. The class map `[α_ν] : K₀(Ḣ_{q,π}) → K₀(𝔘̇(𝔤))` (`upK0`) takes values in the image of
`γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` (`upK0_mem_gammaRange`).

* `alpha_tailT_heq`: `α_ν` of a tail product `a ⊗ b` (with `a`, `b` even) is the horizontal
  composite `α(a) ⋆ α(b)`; hence `upK0_tailT`: the class of `Q^n Π^p (s iᵋ, a ⊗ b)` is
  `[Q^n Π^p (E_s, α(a))] · [(E_i^ε 1_ν, α(b))]`.
* `Edp_mem_gammaRange`, `one_rcls_mem_gammaRange`: the shifted divided-power classes and the
  shifted weight idempotents are in the image of `γ` (they are `ℒ`-multiples of
  `γ(e_i^{(n)} 1_λ)` and `γ(1_λ)`).
* `upK0_mem_gammaRange_of_isDPProduct`, by induction on a product of divided powers, and then
  `upK0_mem_gammaRange` for every class, since these products span `K₀(Ḣ_{q,π})` (Theorem 11.3,
  `dpSpan_eq_top`).

Hypotheses as in `theorem_11_7_existence`: a ground field, `CScalars`, homogeneous scalars and
the route hypothesis `DegreeLocallyFinite` (through the definition of `γ`).
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands MonoidalCategory

namespace OddMath.QuiverHecke

variable {I : Type*} {X : Type*} [AddCommGroup X] {D : SKM.Datum I X} {k : Type*} [CommRing k]
  {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D} {hc : Sc.Homogeneous}

/-- Left whiskering in `H` is whiskering of diagrams. -/
theorem whiskerLeft_heq_blockHom (s : List I) {t : List I} (b : HEnd D Sc sy hc t) :
    HEq (hObj D Sc sy hc s ◁ b) (blockHom D Sc s t [] b) := by
  change HEq ((pres D Sc).wL (ob D s) b) _
  unfold Presentation.wL
  exact heq_conj _ _ _

/-- Right whiskering in `H` is whiskering of diagrams. -/
theorem whiskerRight_heq_blockHom {s : List I} (t : List I) (a : HEnd D Sc sy hc s) :
    HEq (a ▷ hObj D Sc sy hc t) (blockHom D Sc [] s t a) := by
  change HEq ((pres D Sc).wR a (ob D t)) _
  unfold Presentation.wR
  exact heq_conj _ _ _

theorem blockHom_heq_blockOf {l t r w : List I} (hw : l ++ t ++ r = w)
    (f : End ((pres D Sc).obj (ob D t))) : HEq (blockHom D Sc l t r f) (blockOf D Sc hw f) := by
  subst hw; rfl

/-- A functor preserves heterogeneous equality of morphisms. -/
theorem map_heq {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C') {Y Y' Z Z' : C}
    (hY : Y = Y') (hZ : Z = Z') {f : Y ⟶ Z} {f' : Y' ⟶ Z'} (hf : HEq f f') :
    HEq (F.map f) (F.map f') := by
  subst hY hZ; obtain rfl := eq_of_heq hf; rfl

open BicategoryStruct in
/-- **`α` of a tail product is the horizontal composite**: for `a` even on `s` and `b` on `iᵋ`,
`α_ν(T(a) = a ⊗ b)` is `α(a) ⋆ α(b)` on `E_s 1_{ν'} ∘ E_i^ε 1_ν`, `ν' = wt_ν(iᵋ)`. -/
theorem alpha_tailT_heq (ν : X) {s : List I} {i : I} {ε : ℕ}
    {b : HEnd D Sc sy hc (List.replicate ε i)} {a : HEnd D Sc sy hc s}
    (ha : a ∈ Supercategory.parity (R := k) _ _ 0)
    (hb : b ∈ Supercategory.parity (R := k) _ _ 0) {μ : X}
    (h : SKM.wt D (SKM.wt D ν (upWord (List.replicate ε i))) (upWord s) = μ) :
    HEq ((alpha D Sc ν).map (tailT s b a))
      (TwoSupercategory.hcomp (upProj (sy := sy) (hc := hc) h a)
        (upProj (sy := sy) (hc := hc) (rfl : SKM.wt D ν (upWord (List.replicate ε i)) = _) b)) := by
  have hw := SerreComplex.word_comp sy hc μ (SKM.wt D ν (upWord (List.replicate ε i))) ν
    (upWord s) (upWord (List.replicate ε i)) h rfl
  have hobj : (SKM.pres D Sc).obj (SKM.ob D ν (upWord (s ++ List.replicate ε i))) =
      (SKM.pres D Sc).obj (SKM.K0Relations.word Sc sy hc μ _ (upWord s) h ≫
        SKM.K0Relations.word Sc sy hc _ ν (upWord (List.replicate ε i)) rfl).obj := by
    rw [hw, upWord_append]; rfl
  rw [tailT, ← MonoidalSupercategory.interchange_of_even_left (R := k) ha hb, Functor.map_comp]
  simp only [TwoSupercategory.hcomp]
  refine heq_comp (C := (SKM.pres D Sc).Presented) hobj hobj hobj ?_ ?_
  · refine (map_heq (alpha D Sc ν) rfl rfl (whiskerRight_heq_blockHom _ a)).trans ?_
    refine (alpha_blockOf_heq D Sc ν (l := []) (r := List.replicate ε i) rfl a).trans ?_
    refine HEq.symm ((whiskerRight_heq D Sc sy hc _ _).trans ?_)
    refine whisk_heq _ rfl rfl HEq.rfl ?_ rfl
    exact Obj.ext h.symm rfl
  · refine (map_heq (alpha D Sc ν) rfl rfl
      ((whiskerLeft_heq_blockHom (sy := sy) (hc := hc) s b).trans
        (blockHom_heq_blockOf (List.append_nil _) b))).trans ?_
    refine (alpha_blockOf_heq D Sc ν (l := s) (r := []) (List.append_nil _) b).trans ?_
    refine HEq.symm ((whiskerLeft_heq D Sc sy hc _ _).trans ?_)
    refine whisk_heq _ rfl rfl HEq.rfl ?_ rfl
    rfl

theorem upK0_tailT {s : List I} {i : I} {ε : ℕ} {b : HEnd D Sc sy hc (List.replicate ε i)}
    {a : HEnd D Sc sy hc s} (hb : b ≫ b = b)
    (hb0 : b ∈ homPiece D Sc sy hc (List.replicate ε i) (List.replicate ε i) 0 0)
    (ha : a ≫ a = a) (ha0 : a ∈ homPiece D Sc sy hc s s 0 0) {μ ν : X} (n : ℤ) (p : ZMod 2)
    (h : SKM.wt D (SKM.wt D ν (upWord (List.replicate ε i))) (upWord s) = μ)
    (he : tailT s b a ≫ tailT s b a = tailT s b a)
    (hd : tailT s b a ∈ GradedSupercategory.degree (R := k) _ _ 0)
    (hp' : tailT s b a ∈ Supercategory.parity (R := k) _ _ 0) :
    upK0 Sc sy hc μ ν (K₀.mk (raw he hd hp' n p)) =
      upK0 Sc sy hc μ (SKM.wt D ν (upWord (List.replicate ε i))) (K₀.mk (raw ha ha0.1 ha0.2 n p)) *
        SerreComplex.rcls sy hc (upProj_idem rfl hb) (alpha_mem_degree D Sc sy ν hb0.1)
          (alpha_mem_parity D Sc ν hb0.2) 0 0 := by
  have h' : SKM.wt D ν (upWord (s ++ List.replicate ε i)) = μ := by
    rw [upWord_append, SKM.wt_append, h]
  rw [upK0_raw _ _ _ _ _ h', upK0_raw _ _ _ _ _ h, SerreComplex.rcls, SerreComplex.rcls,
    SerreComplex.rcls, ← MulOpposite.op_mul, SKM.Summands.mk_raw_mul_mk_raw]
  congr 2
  rw [add_zero, add_zero]
  have hw : SKM.K0Relations.word Sc sy hc μ _ (upWord s) h ≫
      SKM.K0Relations.word Sc sy hc _ ν (upWord (List.replicate ε i)) rfl =
      SKM.K0Relations.word Sc sy hc μ ν (upWord (s ++ List.replicate ε i)) h' := by
    rw [SerreComplex.word_comp sy hc μ _ ν (upWord s) (upWord (List.replicate ε i)) h rfl]
    refine Presentation.Bicat.Hom.ext ?_
    change SKM.ob D ν _ = SKM.ob D ν _
    rw [upWord_append]
  exact (SerreComplex.raw_congr (k := k) hw (alpha_tailT_heq ν ha0.2 hb0.2 h).symm
    _ _ _ _ _ _ _ _).symm

section Image

open LaurentPolynomial

variable {k' : Type*} [Field k'] (Q : CoveringQuantum.RootDatum I X) {S : SKM.Scalars Q.toSKM k'}
  (hS : S.Homogeneous) (cs : SKM.CScalars S) (hf : Q.skmSymmetrizer.DegreeLocallyFinite)

/-- The image of `γ` (BE2 Theorem 11.7). -/
abbrev gammaRange : Set (SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS) :=
  Set.range (SerreComplex.gammaInt Q hS cs hf)

variable {Q hS cs hf}

theorem gammaRange.smul_mem (r : LaurentPolynomial Zπ)
    {x : SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS} (hx : x ∈ gammaRange Q hS cs hf) :
    r • x ∈ gammaRange Q hS cs hf := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨r • y, map_smul _ r y⟩

theorem gammaRange.mul_mem {x y : SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS}
    (hx : x ∈ gammaRange Q hS cs hf) (hy : y ∈ gammaRange Q hS cs hf) :
    x * y ∈ gammaRange Q hS cs hf := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact ⟨x * y, map_mul _ x y⟩

theorem gammaRange.add_mem {x y : SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS}
    (hx : x ∈ gammaRange Q hS cs hf) (hy : y ∈ gammaRange Q hS cs hf) :
    x + y ∈ gammaRange Q hS cs hf := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact ⟨x + y, map_add _ x y⟩

theorem gammaRange.zero_mem : (0 : SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS) ∈
    gammaRange Q hS cs hf :=
  ⟨0, map_zero _⟩

theorem gammaRange.neg_mem {x : SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS}
    (hx : x ∈ gammaRange Q hS cs hf) : -x ∈ gammaRange Q hS cs hf := by
  rw [← neg_one_smul (LaurentPolynomial Zπ) x]
  exact gammaRange.smul_mem _ hx

theorem rcls_mem_gammaRange {μ ν : X}
    {f : (show SKM.UGr Q.toSKM S Q.skmSymmetrizer hS from ⟨μ⟩) ⟶ ⟨ν⟩} {e : f ⟶ f}
    (he : e ≫ e = e) (hd : e ∈ GradedSupercategory.degree (R := k') f f 0)
    (hp : e ∈ Supercategory.parity (R := k') f f 0) {n₀ : ℤ} {p₀ : ZMod 2}
    (h₀ : SerreComplex.rcls Q.skmSymmetrizer hS he hd hp n₀ p₀ ∈ gammaRange Q hS cs hf)
    (n : ℤ) (p : ZMod 2) :
    SerreComplex.rcls Q.skmSymmetrizer hS he hd hp n p ∈ gammaRange Q hS cs hf := by
  have hT : ∀ (m : ℤ) (q : ZMod 2),
      SerreComplex.rcls Q.skmSymmetrizer hS he hd hp m q ∈ gammaRange Q hS cs hf →
        ∀ z, SerreComplex.rcls Q.skmSymmetrizer hS he hd hp (m + z) q ∈ gammaRange Q hS cs hf :=
    fun m q hm z => by
      rw [← SerreComplex.T_smul_rcls]
      exact gammaRange.smul_mem _ hm
  have hπ : ∀ (m : ℤ) (q : ZMod 2),
      SerreComplex.rcls Q.skmSymmetrizer hS he hd hp m q ∈ gammaRange Q hS cs hf →
        SerreComplex.rcls Q.skmSymmetrizer hS he hd hp m (q + 1) ∈ gammaRange Q hS cs hf :=
    fun m q hm => by
      rw [← SerreComplex.pi_smul_rcls]
      exact gammaRange.smul_mem _ hm
  have h₁ := hT n₀ p₀ h₀ (n - n₀)
  rw [add_sub_cancel] at h₁
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (p - p₀) with hc | hc
  · rw [sub_eq_zero] at hc
    rwa [hc]
  · have h₂ := hπ n p₀ h₁
    rwa [show p₀ + 1 = p by rw [← hc]; ring] at h₂

theorem Edp_mem_gammaRange (i : I) (n : ℕ) {μ ν : X}
    (hs : SKM.wt Q.toSKM ν (upWord (List.replicate n i)) = μ) (m : ℤ) (p : ZMod 2) :
    SerreComplex.Edp Q.skmSymmetrizer hS i n μ ν hs m p ∈ gammaRange Q hS cs hf := by
  subst hs
  have h₀ : SerreComplex.Edp Q.skmSymmetrizer hS i n _ ν rfl (Q.d i * (n.choose 2 : ℕ))
      (((n.choose 2 : ℕ) : ZMod 2) * Q.parity i) ∈ gammaRange Q hS cs hf := by
    rw [SerreComplex.Edp_congr Q.skmSymmetrizer hS (i := i) rfl (SerreComplex.wt_rep ν n) rfl
      rfl rfl rfl (SerreComplex.wt_rep ν n)]
    exact ⟨_, SerreComplex.gammaInt_edp Q hS cs hf i n ν⟩
  exact rcls_mem_gammaRange _ _ _ h₀ m p

theorem one_rcls_mem_gammaRange {μ ν : X} (h : SKM.wt Q.toSKM ν (upWord ([] : List I)) = μ)
    (he : upProj (sy := Q.skmSymmetrizer) (hc := hS) h (𝟙 _) ≫ upProj h (𝟙 _) = upProj h (𝟙 _))
    (hd : upProj (sy := Q.skmSymmetrizer) (hc := hS) h (𝟙 _) ∈
      GradedSupercategory.degree (R := k') _ _ 0)
    (hp : upProj (sy := Q.skmSymmetrizer) (hc := hS) h (𝟙 _) ∈
      Supercategory.parity (R := k') _ _ 0) (n : ℤ) (p : ZMod 2) :
    SerreComplex.rcls Q.skmSymmetrizer hS he hd hp n p ∈ gammaRange Q hS cs hf := by
  subst h
  refine rcls_mem_gammaRange _ _ _ (n₀ := 0) (p₀ := 0) ?_ n p
  have e : SerreComplex.rcls Q.skmSymmetrizer hS he hd hp 0 0 =
      SKM.K0Relations.cls S Q.skmSymmetrizer hS ν ν [] rfl 0 0 := by
    rw [SerreComplex.cls_eq_raw]
    congr 2
    exact (alpha Q.toSKM S ν).map_id _
  rw [e, SerreComplex.cls_nil]
  exact ⟨_, SerreComplex.gammaInt_one Q hS cs hf ν⟩

theorem dp_rcls_mem_gammaRange (i : I) (r : ℕ) (ν : X)
    (he : upProj (sy := Q.skmSymmetrizer) (hc := hS)
      (rfl : SKM.wt Q.toSKM ν (upWord (List.replicate r i)) = _) (dpIdem Q.toSKM S _ hS i r) ≫
        upProj rfl (dpIdem Q.toSKM S _ hS i r) = upProj rfl (dpIdem Q.toSKM S _ hS i r))
    (hd : upProj (sy := Q.skmSymmetrizer) (hc := hS)
      (rfl : SKM.wt Q.toSKM ν (upWord (List.replicate r i)) = _) (dpIdem Q.toSKM S _ hS i r) ∈
        GradedSupercategory.degree (R := k') _ _ 0)
    (hp : upProj (sy := Q.skmSymmetrizer) (hc := hS)
      (rfl : SKM.wt Q.toSKM ν (upWord (List.replicate r i)) = _) (dpIdem Q.toSKM S _ hS i r) ∈
        Supercategory.parity (R := k') _ _ 0) (n : ℤ) (p : ZMod 2) :
    SerreComplex.rcls Q.skmSymmetrizer hS he hd hp n p ∈ gammaRange Q hS cs hf := by
  have e : SerreComplex.rcls Q.skmSymmetrizer hS he hd hp n p =
      SerreComplex.Edp Q.skmSymmetrizer hS i r _ ν rfl n p := by
    unfold SerreComplex.rcls SerreComplex.Edp
    congr 2
    exact SerreComplex.raw_congr (k := k')
      (A := SerreComplex.UHom Q.toSKM S Q.skmSymmetrizer hS _ ν) rfl
      (heq_of_eq (congrArg (alpha Q.toSKM S ν).map
        (dpIdem_eq_serre (sy := Q.skmSymmetrizer) (hc := hS) i r))) _ _ _ _ _ _ _ _
  rw [e]
  exact Edp_mem_gammaRange i r rfl n p

theorem upK0_mem_gammaRange_of_isDPProduct {t : List I} {e : HEnd Q.toSKM S Q.skmSymmetrizer hS t}
    (h : IsDPProduct t e) (μ ν : X) (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k') _ _ 0)
    (hp : e ∈ Supercategory.parity (R := k') _ _ 0) (n : ℤ) (p : ZMod 2) :
    upK0 S Q.skmSymmetrizer hS μ ν (K₀.mk (raw he hd hp n p)) ∈ gammaRange Q hS cs hf := by
  induction h generalizing μ ν n p with
  | nil =>
    by_cases hw : SKM.wt Q.toSKM ν (upWord ([] : List I)) = μ
    · rw [upK0_raw _ _ _ n p hw]
      exact one_rcls_mem_gammaRange hw _ _ _ n p
    · rw [upK0_raw_of_ne _ _ _ n p hw]
      exact gammaRange.zero_mem
  | @snoc t' e' i r ht ih =>
    by_cases hw : SKM.wt Q.toSKM (SKM.wt Q.toSKM ν (upWord (List.replicate r i))) (upWord t') = μ
    · rw [upK0_tailT (dpIdem_idem _ _ _ _ i r) (dpIdem_mem _ _ _ _ i r) ht.mem_idem.2
        ht.mem_idem.1 n p hw]
      exact gammaRange.mul_mem (ih _ _ _ _ _ n p) (dp_rcls_mem_gammaRange i r ν _ _ _ 0 0)
    · rw [upK0_raw_of_ne _ _ _ n p (by rwa [upWord_append, SKM.wt_append])]
      exact gammaRange.zero_mem

/-- **The class step of BE2 Theorem 11.7, upward words**: the image under `[α_ν]` of every
class of `K₀(Ḣ_{q,π})` lies in the image of `γ`. By Theorem 11.3 (`dpSpan_eq_top`) the classes
of shifted products of divided powers span `K₀(Ḣ_{q,π})`, and `α` sends such a product to a
product of divided-power classes `[E_i^{(a)} 1_λ]`. -/
theorem upK0_mem_gammaRange (μ ν : X) (x : K₀ (HKar Q.toSKM S Q.skmSymmetrizer hS)) :
    upK0 S Q.skmSymmetrizer hS μ ν x ∈ gammaRange Q hS cs hf := by
  have hx : x ∈ dpSpan Q.toSKM S Q.skmSymmetrizer hS := by
    rw [dpSpan_eq_top]; trivial
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨t, e, h, n, p, rfl⟩ := hy
    exact upK0_mem_gammaRange_of_isDPProduct h μ ν _ _ _ n p
  | zero => rw [map_zero]; exact gammaRange.zero_mem
  | add y z _ _ hy hz => rw [map_add]; exact gammaRange.add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact gammaRange.neg_mem hy

end Image

end OddMath.QuiverHecke
