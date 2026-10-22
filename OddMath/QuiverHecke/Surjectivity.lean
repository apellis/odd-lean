/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.TopClass
import OddMath.QuiverHecke.CornerLocal

/-!
# BE2 Theorem 11.7, surjectivity

Brundan–Ellis, arXiv:1701.04133v2, Theorem 11.7, surjectivity of `γ`, by induction on the width
of words.

* `exists_top_retract`: decompositions `1 = ∑ z_j` of `E_s` and `1 = ∑ z′_l` of `E_t` into even
  degree-zero idempotents give `1 = ∑ α′(z′_l) α(z_j)` on `E_s F_t 1_{-ν}`, so an indecomposable
  summand of `Q^n Π^b E_s F_t 1_{-ν}` is a summand of one of the top summands.
* `top_mem_gammaPre`: the top step. An indecomposable summand of full width differs from its top
  summand, whose class lies in the image of `γ` (`topProj_mem_gammaRange`), by classes of
  summands of words with two letters fewer (`top_sub_mem_closure_low`).
* `indec_mem_gammaPre`: the width induction, after sorting words (`exists_retract_sorted`).
* `theorem_11_7_surjective`: every class of `K₀(𝔘̇(𝔤))` lies in the image of `γ`, since every
  indecomposable 1-morphism is a summand of a shifted word.

Hypotheses: those of `theorem_11_7_existence` (a ground field, `CScalars`, homogeneous scalars,
and the route hypothesis `Symmetrizer.DegreeLocallyFinite`, which gives finite-dimensional
Hom-spaces for the Krull–Schmidt arguments). No bar-consistency or nondegeneracy hypothesis.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands
open StringDiagrams.KrullSchmidt CategoryTheory.Idempotents

namespace OddMath.QuiverHecke

variable {I : Type*} {X : Type*} [AddCommGroup X] {D : SKM.Datum I X} {k : Type*} [Field k]
  {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D} {hc : Sc.Homogeneous}

/-- **Decomposing a word of `H`**: the identity of `E_s` is a sum of even degree-zero
idempotents with indecomposable summands. -/
theorem exists_indec_idempotents (s : List I) :
    ∃ (J : Type) (_ : Fintype J) (z : J → End (hObj D Sc sy hc s)) (hz : ∀ j, z j ≫ z j = z j)
      (hz0 : ∀ j, z j ∈ homPiece D Sc sy hc s s 0 0),
      (∀ j, IsIndec (RZ (k := k) (hz j) (hz0 j))) ∧ ∑ j, z j = 𝟙 _ := by
  obtain ⟨J, _, Z, ι, π, hi, hs, -, ht⟩ := SKM.Summands.exists_decomposition k
    (unitRaw (k := k) (A := HGr D Sc sy hc) (hObj D Sc sy hc s) 0 0)
  refine ⟨J, inferInstance, fun a => evR (π a ≫ ι a), fun a => retract_idem (ι a) (π a) (hs a),
    fun a => ⟨retract_degree (ι a) (π a), retract_parity (ι a) (π a)⟩, fun a => ?_, ?_⟩
  · exact IsIndec.of_iso (retractIso (ι a) (π a) (hs a)) (hi a)
  · rw [← evR_sum, ht]
    rfl


section Top

variable (ν : X) (s t : List I) {μ : X} (hw : SKM.wt D (-ν) (upWord s ++ SKM.dnWord t) = μ)
  {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)} (hz : z ≫ z = z)
  (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
  (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0) (n : ℤ) (b : ZMod 2)

/-- The image `E` of the top idempotent on `Q^n Π^b E_s F_t 1_{-ν}`. -/
abbrev topSummand :
    SKM.K0Relations.weight Sc sy hc μ ⟶ SKM.K0Relations.weight Sc sy hc (-ν) :=
  raw (topProj_props ν s t hw hz hz' hz0 hz0').1 (topProj_props ν s t hw hz hz' hz0 hz0').2.1
    (topProj_props ν s t hw hz hz' hz0 hz0').2.2 n b

/-- The top idempotent as an endomorphism of the shifted word. -/
abbrev topShifted :
    SKM.K0Relations.shifted Sc sy hc μ (-ν) _ hw n b ⟶
      SKM.K0Relations.shifted Sc sy hc μ (-ν) _ hw n b :=
  projector (topProj_props ν s t hw hz hz' hz0 hz0').2.1
    (topProj_props ν s t hw hz hz' hz0 hz0').2.2 n b

/-- The inclusion of `E` into the shifted word. -/
def topI : topSummand ν s t hw hz hz' hz0 hz0' n b ⟶
    SKM.K0Relations.completed Sc sy hc μ (-ν) _ hw n b where
  f := (topSummand ν s t hw hz hz' hz0 hz0' n b).p
  comm := by
    erw [Category.comp_id, (topSummand ν s t hw hz hz' hz0 hz0' n b).idem]

/-- The projection of the shifted word onto `E`. -/
def topP : SKM.K0Relations.completed Sc sy hc μ (-ν) _ hw n b ⟶
    topSummand ν s t hw hz hz' hz0 hz0' n b where
  f := (topSummand ν s t hw hz hz' hz0 hz0' n b).p
  comm := by
    erw [Category.id_comp, (topSummand ν s t hw hz hz' hz0 hz0' n b).idem]

theorem topI_topP : topI ν s t hw hz hz' hz0 hz0' n b ≫ topP ν s t hw hz hz' hz0 hz0' n b =
    𝟙 _ :=
  Karoubi.hom_ext _ _ (topSummand ν s t hw hz hz' hz0 hz0' n b).idem

theorem topP_topI : topP ν s t hw hz hz' hz0 hz0' n b ≫ topI ν s t hw hz hz' hz0 hz0' n b =
    (SKM.K0Relations.inclusion Sc sy hc μ (-ν)).map (topShifted ν s t hw hz hz' hz0 hz0' n b) :=
  Karoubi.hom_ext _ _ (topSummand ν s t hw hz hz' hz0 hz0' n b).idem

theorem sval_topShifted :
    SKM.sval (topShifted ν s t hw hz hz' hz0 hz0' n b) = SKM.topEps (Sc := Sc) sy hc ν s t z z' :=
  rfl

end Top

section TopSum

variable (ν : X) (s t : List I) {μ : X} (hw : SKM.wt D (-ν) (upWord s ++ SKM.dnWord t) = μ)
  (n : ℤ) (b : ZMod 2)

/-- The underlying endomorphism of an endomorphism of a shifted word, additively. -/
def svalHom : (SKM.K0Relations.shifted Sc sy hc μ (-ν) (upWord s ++ SKM.dnWord t) hw n b ⟶
      SKM.K0Relations.shifted Sc sy hc μ (-ν) (upWord s ++ SKM.dnWord t) hw n b) →+
    End ((SKM.pres D Sc).obj (SKM.ob D (-ν) (upWord s ++ SKM.dnWord t))) where
  toFun f := SKM.sval f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The top idempotents of decompositions of `E_s` and `E_t` sum to the identity.** -/
theorem sum_topShifted {J J' : Type} [Fintype J] [Fintype J'] {z : J → End (hObj D Sc sy hc s)}
    {z' : J' → End (hObj D Sc sy hc t)} (hz : ∀ j, z j ≫ z j = z j)
    (hz' : ∀ l, z' l ≫ z' l = z' l) (hz0 : ∀ j, z j ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : ∀ l, z' l ∈ homPiece D Sc sy hc t t 0 0) (hsz : ∑ j, z j = 𝟙 _)
    (hsz' : ∑ l, z' l = 𝟙 _) :
    ∑ x : J × J', topShifted ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b = 𝟙 _ := by
  refine SKM.shifted_ext ?_
  change svalHom (sy := sy) (hc := hc) ν s t hw n b (∑ x : J × J', _) = 1
  rw [map_sum]
  change ∑ x : J × J', SKM.dnMap sy hc ν s t (z' x.2) * SKM.upMap sy hc ν s t (z x.1) = 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  change ∑ l, ∑ j, SKM.dnMap sy hc ν s t (z' l) * SKM.upMap sy hc ν s t (z j) = 1
  rw [← Finset.sum_mul_sum, ← map_sum, ← map_sum]
  change SKM.dnMap sy hc ν s t (∑ l, z' l) * SKM.upMap sy hc ν s t (∑ j, z j) = 1
  rw [hsz, hsz']
  change SKM.dnE Sc ν (upWord s) t 1 * SKM.upE Sc (-ν) s (SKM.dnWord t) 1 = 1
  rw [SKM.dnE_one, SKM.upE_one, one_mul]

theorem homFinite_weight (cs : SKM.CScalars Sc) (hf : sy.DegreeLocallyFinite) (μ ν : X) :
    HomFinite k (SKM.K0Relations.weight Sc sy hc μ ⟶ SKM.K0Relations.weight Sc sy hc ν) := by
  let a : SKM.UGr D Sc sy hc := ⟨μ⟩
  let b : SKM.UGr D Sc sy hc := ⟨ν⟩
  have := SKM.UGr.degreeHomFinite sy cs hc hf a b
  exact inferInstanceAs (HomFinite k (GSKar k (a ⟶ b)))

/-- **An indecomposable summand of `Q^n Π^b E_s F_t 1_{-ν}` is a summand of one of the top
summands** `E_{jl}` of the top idempotents `α′(z′_l) α(z_j)`, for decompositions `1 = ∑ z_j` and
`1 = ∑ z′_l` into even degree-zero idempotents. -/
theorem exists_top_retract (cs : SKM.CScalars Sc) (hf : sy.DegreeLocallyFinite) {J J' : Type}
    [Fintype J] [Fintype J'] {z : J → End (hObj D Sc sy hc s)}
    {z' : J' → End (hObj D Sc sy hc t)} (hz : ∀ j, z j ≫ z j = z j)
    (hz' : ∀ l, z' l ≫ z' l = z' l) (hz0 : ∀ j, z j ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : ∀ l, z' l ∈ homPiece D Sc sy hc t t 0 0) (hsz : ∑ j, z j = 𝟙 _)
    (hsz' : ∑ l, z' l = 𝟙 _)
    {Z : SKM.K0Relations.weight Sc sy hc μ ⟶ SKM.K0Relations.weight Sc sy hc (-ν)} (hZ : IsIndec Z)
    (ι : Z ⟶ SKM.K0Relations.completed Sc sy hc μ (-ν) _ hw n b)
    (π : SKM.K0Relations.completed Sc sy hc μ (-ν) _ hw n b ⟶ Z) (h : ι ≫ π = 𝟙 Z) :
    ∃ x : J × J', ∃ v : topSummand ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b ⟶ Z,
      (ι ≫ topP ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b) ≫ v = 𝟙 Z := by
  have := homFinite_weight (hc := hc) cs hf μ (-ν)
  obtain ⟨x, -, v, hv⟩ := SKM.Summands.exists_retract_of_sum k hZ Finset.univ
    (fun x : J × J' => ι ≫ topP ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b)
    (fun x => topI ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b ≫ π) (by
      simp only [Category.assoc]
      simp only [← Category.assoc (topP _ _ _ _ _ _ _ _ _ _), topP_topI]
      rw [← Preadditive.comp_sum, ← Preadditive.sum_comp, ← Functor.map_sum,
        sum_topShifted ν s t hw n b hz hz' hz0 hz0' hsz hsz', CategoryTheory.Functor.map_id,
        Category.id_comp, h])
  exact ⟨x, v, hv⟩

end TopSum

section Image

variable {k' : Type*} [Field k'] {Q : CoveringQuantum.RootDatum I X} {S : SKM.Scalars Q.toSKM k'}
  {hS : S.Homogeneous} {cs : SKM.CScalars S} {hf : Q.skmSymmetrizer.DegreeLocallyFinite}

variable (Q hS cs hf) in
/-- The image of `γ`, as an additive subgroup. -/
def gammaSub : AddSubgroup (SKM.K0Relations.Grothendieck S Q.skmSymmetrizer hS) where
  carrier := gammaRange Q hS cs hf
  add_mem' := gammaRange.add_mem
  zero_mem' := gammaRange.zero_mem
  neg_mem' := gammaRange.neg_mem

variable (Q hS cs hf) in
/-- The classes of the completed hom category `μ → ν` whose image lies in the image of `γ`. -/
def gammaPre (μ ν : X) : AddSubgroup (K₀ (SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
    SKM.K0Relations.weight S Q.skmSymmetrizer hS ν)) :=
  (gammaSub Q hS cs hf).comap ((MulOpposite.opAddEquiv.toAddMonoidHom).comp
    (K₀Ring.of (SKM.K0Relations.weight S Q.skmSymmetrizer hS μ)
      (SKM.K0Relations.weight S Q.skmSymmetrizer hS ν)))

/-- **The top step of the width induction (BE2, arXiv:1701.04133v2, proof of Theorem 11.7,
surjectivity).** If the classes of all indecomposable summands of shifted words with at least two
letters fewer than `E_s F_t 1_{-ν}` lie in the image of `γ`, so do the classes of the
indecomposable summands of `Q^n Π^b E_s F_t 1_{-ν}`. -/
theorem top_mem_gammaPre (ν : X) (s t : List I) {μ : X}
    (hw : SKM.wt Q.toSKM (-ν) (upWord s ++ SKM.dnWord t) = μ) (n : ℤ) (b : ZMod 2)
    {Z : SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
      SKM.K0Relations.weight S Q.skmSymmetrizer hS (-ν)} (hZ : IsIndec Z)
    (ι : Z ⟶ SKM.K0Relations.completed S Q.skmSymmetrizer hS μ (-ν) _ hw n b)
    (π : SKM.K0Relations.completed S Q.skmSymmetrizer hS μ (-ν) _ hw n b ⟶ Z) (h : ι ≫ π = 𝟙 Z)
    (IH : ∀ Y, IsIndec Y →
      SKM.LowWidth Q.skmSymmetrizer hS μ (-ν) (upWord s ++ SKM.dnWord t).length Y →
        K₀.mk Y ∈ gammaPre Q hS cs hf μ (-ν)) :
    K₀.mk Z ∈ gammaPre Q hS cs hf μ (-ν) := by
  by_cases hlow : SKM.LowWidth Q.skmSymmetrizer hS μ (-ν) (upWord s ++ SKM.dnWord t).length Z
  · exact IH Z hZ hlow
  obtain ⟨J, _, z, hz, hz0, hind, hsz⟩ := exists_indec_idempotents (k := k') (Sc := S)
    (sy := Q.skmSymmetrizer) (hc := hS) s
  obtain ⟨J', _, z', hz', hz0', hind', hsz'⟩ := exists_indec_idempotents (k := k') (Sc := S)
    (sy := Q.skmSymmetrizer) (hc := hS) t
  obtain ⟨x, v, hv⟩ := exists_top_retract ν s t hw n b cs hf hz hz' hz0 hz0' hsz hsz' hZ ι π h
  obtain ⟨_, _, hE⟩ := localCorner_of_isIndec (hz x.1) (hz0 x.1) (hind x.1)
  obtain ⟨_, _, hE'⟩ := localCorner_of_isIndec (hz' x.2) (hz0' x.2) (hind' x.2)
  have hcl := SKM.top_sub_mem_closure_low cs Q.skmSymmetrizer hS hf (hz x.1) (hz' x.2) (hz0 x.1)
    (hz0' x.2) hE hE' _ (sval_topShifted ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b)
    (topI ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b)
    (topP ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b)
    (topI_topP ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b)
    (topP_topI ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b) hZ _ v hv hlow
  have hlowE : K₀.mk (topSummand ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b) -
      K₀.mk Z ∈ gammaPre Q hS cs hf μ (-ν) := by
    refine (AddSubmonoid.closure_le (S := (gammaPre Q hS cs hf μ (-ν)).toAddSubmonoid)).2 ?_ hcl
    rintro _ ⟨Y, hY, hYlow, rfl⟩
    exact IH Y hY hYlow
  have hE₀ : K₀.mk (topSummand ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b) ∈
      gammaPre Q hS cs hf μ (-ν) :=
    topProj_mem_gammaRange ν s t hw (hz x.1) (hz' x.2) (hz0 x.1) (hz0' x.2) n b
  have := sub_mem hE₀ hlowE
  rwa [sub_sub_cancel] at this

theorem top_mem_gammaPre' (ν : X) (s t : List I) {u : List (SKM.Letter I)}
    (e : u = upWord s ++ SKM.dnWord t) {μ : X} (hu : SKM.wt Q.toSKM (-ν) u = μ) (n : ℤ)
    (b : ZMod 2) {Z : SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
      SKM.K0Relations.weight S Q.skmSymmetrizer hS (-ν)} (hZ : IsIndec Z)
    (ι : Z ⟶ SKM.K0Relations.completed S Q.skmSymmetrizer hS μ (-ν) u hu n b)
    (π : SKM.K0Relations.completed S Q.skmSymmetrizer hS μ (-ν) u hu n b ⟶ Z) (h : ι ≫ π = 𝟙 Z)
    (IH : ∀ Y, IsIndec Y → SKM.LowWidth Q.skmSymmetrizer hS μ (-ν) u.length Y →
        K₀.mk Y ∈ gammaPre Q hS cs hf μ (-ν)) :
    K₀.mk Z ∈ gammaPre Q hS cs hf μ (-ν) := by
  subst e
  exact top_mem_gammaPre ν s t hu n b hZ ι π h IH

/-- **The width induction (BE2, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity).** The
class of every indecomposable summand of a shifted word `Q^m Π^a E_w 1_ν` lies in the image of
`γ`. -/
theorem indec_mem_gammaPre {μ ν : X} (N : ℕ) :
    ∀ (w : List (SKM.Letter I)) (hw : SKM.wt Q.toSKM ν w = μ) (m : ℤ) (a : ZMod 2),
      w.length ≤ N → ∀ (Z : SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
        SKM.K0Relations.weight S Q.skmSymmetrizer hS ν), IsIndec Z →
      ∀ (ι : Z ⟶ SKM.K0Relations.completed S Q.skmSymmetrizer hS μ ν w hw m a)
        (π : SKM.K0Relations.completed S Q.skmSymmetrizer hS μ ν w hw m a ⟶ Z),
        ι ≫ π = 𝟙 Z → K₀.mk Z ∈ gammaPre Q hS cs hf μ ν := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw m a hN Z hZ ι π h
    obtain ⟨u, hu, n, b, ⟨s, t, rfl⟩, hlen, -, ι', π', h'⟩ :=
      SKM.exists_retract_sorted (cs := cs) (hc := hS) (hf := hf) hZ ι π h
    obtain ⟨ν₀, rfl⟩ : ∃ ν₀, ν = -ν₀ := ⟨-ν, (neg_neg ν).symm⟩
    refine top_mem_gammaPre' ν₀ s t (by rw [SKM.dnWord_eq_map]; rfl) hu n b hZ ι' π' h' ?_
    rintro Y hY ⟨v, hv, n', b', hv2, f, g, hfg⟩
    exact ih v.length (by omega) v hv n' b' le_rfl Y hY f g hfg

/-- The shifted identity of a word is the shifted word. -/
theorem isRetract_unitRaw_completed {μ ν : X} (w : List (SKM.Letter I))
    (hw : SKM.wt Q.toSKM ν w = μ) (n : ℤ) (p : ZMod 2) :
    IsRetract (unitRaw (k := k') (SKM.K0Relations.word S Q.skmSymmetrizer hS μ ν w hw) n p :
        SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
          SKM.K0Relations.weight S Q.skmSymmetrizer hS ν)
      (SKM.K0Relations.completed S Q.skmSymmetrizer hS μ ν w hw n p) := by
  refine ⟨⟨𝟙 _, ?_⟩, ⟨𝟙 _, ?_⟩, ?_⟩
  · erw [unitRaw_p, Category.id_comp, Category.id_comp]
    rfl
  · erw [unitRaw_p, Category.id_comp, Category.id_comp]
    rfl
  · exact Karoubi.hom_ext _ _ ((Category.id_comp _).trans (unitRaw_p (k := k') _ n p).symm)

include cs hf in
/-- Every indecomposable 1-morphism `μ → ν` of `𝔘̇(𝔤)` is a summand of a shifted word. -/
theorem exists_word_retract {μ ν : X} {Y : SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
      SKM.K0Relations.weight S Q.skmSymmetrizer hS ν} (hY : IsIndec Y) :
    ∃ (w : List (SKM.Letter I)) (hw : SKM.wt Q.toSKM ν w = μ) (n : ℤ) (p : ZMod 2),
      IsRetract Y (SKM.K0Relations.completed S Q.skmSymmetrizer hS μ ν w hw n p) := by
  have := homFinite_weight (hc := hS) cs hf μ ν
  obtain ⟨J, _, f, n, p, u, v, huv⟩ := sum_unitRaw (k := k') Y
  obtain ⟨j, -, v', hv'⟩ := exists_retract_of_sum k' hY Finset.univ u v huv
  have hR : IsRetract Y (unitRaw (k := k') (f j) (n j) (p j) :
      SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
        SKM.K0Relations.weight S Q.skmSymmetrizer hS ν) := ⟨u j, v', hv'⟩
  generalize f j = g at hR
  have hw : SKM.wt Q.toSKM ν (g.obj.word.map SKM.Col.l) = μ :=
    (congrArg Obj.start (SKM.homObj_normal g)).symm.trans g.start_eq
  have hg : g = SKM.K0Relations.word S Q.skmSymmetrizer hS μ ν _ hw :=
    Presentation.Bicat.Hom.ext (SKM.homObj_normal g)
  rw [hg] at hR
  exact ⟨_, hw, n j, p j, hR.trans (isRetract_unitRaw_completed _ hw _ _)⟩

include cs hf in
/-- Every class of the completed hom category `μ → ν` lies over the image of `γ`. -/
theorem mem_gammaPre {μ ν : X} (x : K₀ (SKM.K0Relations.weight S Q.skmSymmetrizer hS μ ⟶
      SKM.K0Relations.weight S Q.skmSymmetrizer hS ν)) :
    x ∈ gammaPre Q hS cs hf μ ν := by
  have := homFinite_weight (hc := hS) cs hf μ ν
  induction x using K₀.induction_on with
  | mk X =>
    refine mk_mem_of_indec_retracts k' _ X fun Y hY _ _ _ => ?_
    obtain ⟨w, hw, n, p, ι, π, h⟩ := exists_word_retract (cs := cs) (hf := hf) hY
    exact indec_mem_gammaPre w.length w hw n p le_rfl Y hY ι π h
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | neg x hx => exact neg_mem hx

variable (Q hS cs hf) in
include cs hf in
/-- **BE2 Theorem 11.7, surjectivity** (arXiv:1701.04133v2): the homomorphism
`γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` of `theorem_11_7_existence` is surjective. Hypotheses: a ground
field, the scalar hypotheses of §9, and the route hypothesis `DegreeLocallyFinite` (finitely
many colours in each degree; it gives the finite-dimensional Hom-spaces used for Krull–Schmidt),
as for existence. -/
theorem theorem_11_7_surjective : Function.Surjective (SerreComplex.gammaInt Q hS cs hf) := by
  intro y
  change y ∈ gammaRange Q hS cs hf
  induction y using MulOpposite.rec' with
  | _ y =>
    induction y using K₀Ring.induction_on with
    | zero => exact gammaRange.zero_mem
    | add x y hx hy => exact gammaRange.add_mem hx hy
    | of a b x =>
      obtain ⟨⟨⟨⟨⟨⟨⟨μ⟩⟩⟩⟩⟩⟩⟩ := a
      obtain ⟨⟨⟨⟨⟨⟨⟨ν⟩⟩⟩⟩⟩⟩⟩ := b
      exact mem_gammaPre (cs := cs) (hf := hf) (μ := μ) (ν := ν) x

end Image

end OddMath.QuiverHecke
