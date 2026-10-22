/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.DownwardClasses
import OddMath.QuiverHecke.UpwardImage

/-!
# Downward classes lie in the image of `γ`

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, class step for
downward words. The class map `[α'_ν] : K₀(Ḣ_{q,π}) → K₀(𝔘̇(𝔤))` (`downK0`) takes values in
the image of `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` (`downK0_mem_gammaRange`).

* `downK0_tailT`: `ω` carries the horizontal composite `α(a) ⋆ α(b)` of even 2-morphisms to
  `ω α(a) ⋆ ω α(b)`, so the class of `Q^n Π^p (s iᵋ, a ⊗ b)` goes to
  `[Q^{-n} Π^p (F_s, ω α(a))] · [(F_i^ε 1_{-ν}, ω α(b))]`.
* `Fdp_mem_gammaRange`: the shifted divided-power classes `[Q^m Π^p F_i^{(n)} 1_λ]` are in the
  image of `γ` (they are `ℒ`-multiples of `γ(f_i^{(n)} 1_λ)`).
* `downK0_mem_gammaRange_of_isDPProduct`, by induction on a product of divided powers, and then
  `downK0_mem_gammaRange` for every class, by Theorem 11.3 (`dpSpan_eq_top`).

Hypotheses as in `upK0_mem_gammaRange`.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands

namespace OddMath.QuiverHecke

variable {I : Type*} {X : Type*} [AddCommGroup X] {D : SKM.Datum I X} {k : Type*} [CommRing k]
  {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D} {hc : Sc.Homogeneous}

theorem downK0_tailT {s : List I} {i : I} {ε : ℕ} {b : HEnd D Sc sy hc (List.replicate ε i)}
    {a : HEnd D Sc sy hc s} (hb : b ≫ b = b)
    (hb0 : b ∈ homPiece D Sc sy hc (List.replicate ε i) (List.replicate ε i) 0 0)
    (ha : a ≫ a = a) (ha0 : a ∈ homPiece D Sc sy hc s s 0 0) {μ ν : X} (n : ℤ) (p : ZMod 2)
    (h : SKM.wt D (SKM.wt D ν (upWord (List.replicate ε i))) (upWord s) = μ)
    (he : tailT s b a ≫ tailT s b a = tailT s b a)
    (hd : tailT s b a ∈ GradedSupercategory.degree (R := k) _ _ 0)
    (hp' : tailT s b a ∈ Supercategory.parity (R := k) _ _ 0) :
    downK0 Sc sy hc μ ν (K₀.mk (raw he hd hp' n p)) =
      downK0 Sc sy hc μ (SKM.wt D ν (upWord (List.replicate ε i)))
          (K₀.mk (raw ha ha0.1 ha0.2 n p)) *
        MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc)
          (a := SKM.K0Relations.weight Sc sy hc (-SKM.wt D ν (upWord (List.replicate ε i))))
          (b := SKM.K0Relations.weight Sc sy hc (-ν))
          (SerreComplex.chevSummand sy hc (upProj_idem rfl hb)
            (alpha_mem_degree D Sc sy ν hb0.1) (alpha_mem_parity D Sc ν hb0.2) 0 0)) := by
  have h' : SKM.wt D ν (upWord (s ++ List.replicate ε i)) = μ := by
    rw [upWord_append, SKM.wt_append, h]
  rw [downK0_raw _ _ _ _ _ h', downK0_raw _ _ _ _ _ h, ← MulOpposite.op_mul,
    SKM.Summands.mk_raw_mul_mk_raw]
  congr 2
  rw [add_zero, add_zero]
  have hw : SKM.K0Relations.word Sc sy hc μ _ (upWord s) h ≫
      SKM.K0Relations.word Sc sy hc _ ν (upWord (List.replicate ε i)) rfl =
      SKM.K0Relations.word Sc sy hc μ ν (upWord (s ++ List.replicate ε i)) h' := by
    rw [SerreComplex.word_comp sy hc μ _ ν (upWord s) (upWord (List.replicate ε i)) h rfl]
    refine Presentation.Bicat.Hom.ext ?_
    change SKM.ob D ν _ = SKM.ob D ν _
    rw [upWord_append]
  refine (SerreComplex.raw_congr (k := k) ((SKM.chevHomObj_comp _ _).symm.trans
    (congrArg SKM.chevHomObj hw)) ?_ _ _ _ _ _ _ _ _).symm
  exact (chevHom_hcomp_heq sy hc _ _ (alpha_mem_parity D Sc _ ha0.2)
    (alpha_mem_parity D Sc ν hb0.2)).symm.trans
    (chevHom_heq sy hc hw (alpha_tailT_heq ν ha0.2 hb0.2 h).symm)

section Image

variable {k' : Type*} [Field k'] {Q : CoveringQuantum.RootDatum I X} {S : SKM.Scalars Q.toSKM k'}
  {hS : S.Homogeneous} {cs : SKM.CScalars S} {hf : Q.skmSymmetrizer.DegreeLocallyFinite}

theorem Fdp_mem_gammaRange (i : I) (n : ℕ) {μ ν : X}
    (hs : SKM.wt Q.toSKM ν (upWord (List.replicate n i)) = μ) (m : ℤ) (p : ZMod 2) :
    SerreComplex.Fdp Q.skmSymmetrizer hS i n μ ν hs m p ∈ gammaRange Q hS cs hf := by
  subst hs
  have h₀ : SerreComplex.Fdp Q.skmSymmetrizer hS i n _ ν rfl (-(Q.d i * (n.choose 2 : ℕ))) 0 ∈
      gammaRange Q hS cs hf := by
    rw [SerreComplex.Fdp_congr Q.skmSymmetrizer hS (i := i) rfl
      (by rw [neg_neg, SerreComplex.wt_rep]) (neg_neg ν).symm rfl rfl rfl
      (SerreComplex.wt_rep (-(-ν)) n)]
    exact ⟨_, SerreComplex.gammaInt_fdp Q hS cs hf i n (-ν)⟩
  exact rcls_mem_gammaRange _ _ _ h₀ m p

theorem dp_chev_mem_gammaRange (i : I) (r : ℕ) (ν : X)
    (hb0 : dpIdem Q.toSKM S Q.skmSymmetrizer hS i r ∈
      homPiece Q.toSKM S Q.skmSymmetrizer hS (List.replicate r i) (List.replicate r i) 0 0)
    (m : ℤ) (p : ZMod 2) :
    MulOpposite.op (K₀Ring.mk (B := SKM.UDot Q.toSKM S Q.skmSymmetrizer hS)
      (a := SKM.K0Relations.weight S Q.skmSymmetrizer hS
        (-SKM.wt Q.toSKM ν (upWord (List.replicate r i))))
      (b := SKM.K0Relations.weight S Q.skmSymmetrizer hS (-ν))
      (SerreComplex.chevSummand Q.skmSymmetrizer hS (upProj_idem rfl (dpIdem_idem _ _ _ _ i r))
        (alpha_mem_degree Q.toSKM S Q.skmSymmetrizer ν hb0.1)
        (alpha_mem_parity Q.toSKM S ν hb0.2) m p)) ∈ gammaRange Q hS cs hf := by
  have e : MulOpposite.op (K₀Ring.mk (B := SKM.UDot Q.toSKM S Q.skmSymmetrizer hS)
      (a := SKM.K0Relations.weight S Q.skmSymmetrizer hS
        (-SKM.wt Q.toSKM ν (upWord (List.replicate r i))))
      (b := SKM.K0Relations.weight S Q.skmSymmetrizer hS (-ν))
      (SerreComplex.chevSummand Q.skmSymmetrizer hS (upProj_idem rfl (dpIdem_idem _ _ _ _ i r))
        (alpha_mem_degree Q.toSKM S Q.skmSymmetrizer ν hb0.1)
        (alpha_mem_parity Q.toSKM S ν hb0.2) m p)) =
      SerreComplex.Fdp Q.skmSymmetrizer hS i r _ ν rfl m p := by
    unfold SerreComplex.Fdp
    congr 2
    exact SerreComplex.raw_congr (k := k') rfl
      (heq_of_eq (by
        unfold upProj SerreComplex.dpProj
        rw [dpIdem_eq_serre (sy := Q.skmSymmetrizer) (hc := hS) i r])) _ _ _ _ _ _ _ _
  rw [e]
  exact Fdp_mem_gammaRange i r rfl m p

theorem one_chev_mem_gammaRange {μ ν : X} (h : SKM.wt Q.toSKM ν (upWord ([] : List I)) = μ)
    (he : upProj (sy := Q.skmSymmetrizer) (hc := hS) h (𝟙 _) ≫ upProj h (𝟙 _) = upProj h (𝟙 _))
    (hd : upProj (sy := Q.skmSymmetrizer) (hc := hS) h (𝟙 _) ∈
      GradedSupercategory.degree (R := k') _ _ 0)
    (hp : upProj (sy := Q.skmSymmetrizer) (hc := hS) h (𝟙 _) ∈
      Supercategory.parity (R := k') _ _ 0) (n : ℤ) (p : ZMod 2) :
    MulOpposite.op (K₀Ring.mk (B := SKM.UDot Q.toSKM S Q.skmSymmetrizer hS)
      (a := SKM.K0Relations.weight S Q.skmSymmetrizer hS (-μ))
      (b := SKM.K0Relations.weight S Q.skmSymmetrizer hS (-ν))
      (SerreComplex.chevSummand Q.skmSymmetrizer hS he hd hp n p)) ∈ gammaRange Q hS cs hf := by
  subst h
  refine rcls_mem_gammaRange _ _ _ (n₀ := 0) (p₀ := 0) ?_ n p
  have hy : SOp.unsop ((SKM.chevHom (sy := Q.skmSymmetrizer) (hc := hS) _ _).map
      (upProj (sy := Q.skmSymmetrizer) (hc := hS)
        (rfl : SKM.wt Q.toSKM ν (upWord ([] : List I)) = _) (𝟙 _))) = 𝟙 _ := by
    unfold upProj
    erw [CategoryTheory.Functor.map_id (alpha Q.toSKM S ν)]
    exact congrArg SOp.unsop ((SKM.chevHom _ _).map_id _)
  have key : ∀ x, x = SKM.K0Relations.cls S Q.skmSymmetrizer hS (-ν) (-ν) [] rfl 0 0 →
      x ∈ gammaRange Q hS cs hf := fun x hx => by
    rw [hx, SerreComplex.cls_nil]
    exact ⟨_, SerreComplex.gammaInt_one Q hS cs hf (-ν)⟩
  apply key
  rw [SerreComplex.cls_eq_raw]
  refine SerreComplex.rcls_transport Q.skmSymmetrizer hS rfl
    (SKM.chevMap_obj Q.toSKM ν _) _ _ ?_ _ _ _ _ _ _ 0 0
  rw [hy]
  exact congr_arg_heq (fun o => 𝟙 ((SKM.pres Q.toSKM S).obj o)) (SKM.chevMap_obj Q.toSKM ν _)

theorem downK0_mem_gammaRange_of_isDPProduct {t : List I}
    {e : HEnd Q.toSKM S Q.skmSymmetrizer hS t} (h : IsDPProduct t e) (μ ν : X) (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k') _ _ 0)
    (hp : e ∈ Supercategory.parity (R := k') _ _ 0) (n : ℤ) (p : ZMod 2) :
    downK0 S Q.skmSymmetrizer hS μ ν (K₀.mk (raw he hd hp n p)) ∈ gammaRange Q hS cs hf := by
  induction h generalizing μ ν n p with
  | nil =>
    by_cases hw : SKM.wt Q.toSKM ν (upWord ([] : List I)) = μ
    · rw [downK0_raw _ _ _ n p hw]
      exact one_chev_mem_gammaRange hw _ _ _ (-n) p
    · rw [downK0_raw_of_ne _ _ _ n p hw]
      exact gammaRange.zero_mem
  | @snoc t' e' i r ht ih =>
    by_cases hw : SKM.wt Q.toSKM (SKM.wt Q.toSKM ν (upWord (List.replicate r i))) (upWord t') = μ
    · rw [downK0_tailT (dpIdem_idem _ _ _ _ i r) (dpIdem_mem _ _ _ _ i r) ht.mem_idem.2
        ht.mem_idem.1 n p hw]
      exact gammaRange.mul_mem (ih _ _ _ _ _ n p)
        (dp_chev_mem_gammaRange i r ν (dpIdem_mem _ _ _ _ i r) 0 0)
    · rw [downK0_raw_of_ne _ _ _ n p (by rwa [upWord_append, SKM.wt_append])]
      exact gammaRange.zero_mem

/-- **The class step of BE2 Theorem 11.7, downward words**: the image under `[α'_ν]` of every
class of `K₀(Ḣ_{q,π})` lies in the image of `γ`. By Theorem 11.3 (`dpSpan_eq_top`) the classes
of shifted products of divided powers span `K₀(Ḣ_{q,π})`, and `α' = ω ∘ α` sends such a product
to a product of divided-power classes `[F_i^{(a)} 1_λ]`. -/
theorem downK0_mem_gammaRange (μ ν : X) (x : K₀ (HKar Q.toSKM S Q.skmSymmetrizer hS)) :
    downK0 S Q.skmSymmetrizer hS μ ν x ∈ gammaRange Q hS cs hf := by
  have hx : x ∈ dpSpan Q.toSKM S Q.skmSymmetrizer hS := by
    rw [dpSpan_eq_top]; trivial
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨t, e, h, n, p, rfl⟩ := hy
    exact downK0_mem_gammaRange_of_isDPProduct h μ ν _ _ _ n p
  | zero => rw [map_zero]; exact gammaRange.zero_mem
  | add y z _ _ hy hz => rw [map_add]; exact gammaRange.add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact gammaRange.neg_mem hy

end Image

end OddMath.QuiverHecke
