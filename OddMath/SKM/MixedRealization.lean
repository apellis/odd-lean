import OddMath.SKM.MixedFibres
import OddMath.SKM.PsiLeftImages

/-! # Ordinary source branches for mixed matching degrees

BE2, arXiv:1701.04133v2, §8 and Theorem 10.3: source-branch expansions
realize the generator-table degree and its finite fibres. Derived left cups and
caps retain their scalar source anchors; no scalar-free global morphism equality
is asserted.
-/

noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord

variable {I X : Type*} [AddCommGroup X] (D : Datum I X)

/-- The ordinary layer branch occurring in the source expression for an extended
shape. Left cups and caps use precisely the branches of `etaPDiagram` and
`epsPDiagram`; their scalar prefactors do not affect degree. -/
def shapeSourceLayers (ν : X) : XShape I → List (LayerData I)
  | .gen g => [([], g, [])]
  | .lcup i => if 0 < D.h i ν then dcupL i (D.h i ν - 1).toNat
      else etaL i (-D.h i ν).toNat ++ lcrossL i i
  | .lcap i => if D.h i ν < 0 then dcapL i (-D.h i ν - 1).toNat
      else lcrossL i i ++ epsL i (D.h i ν).toNat

/-- Expand the source branches at each layer's actual right-region weight. -/
def tableSourceLayers (μ : X) (L : List (XLayer I)) : List (LayerData I) :=
  L.flatMap fun x => (shapeSourceLayers D (wt D μ x.2.2) x.2.1).map (whL x.1 x.2.2)

theorem shapeSourceLayers_chain (ν : X) (g : XShape I) :
    SChain g.dom (shapeSourceLayers D ν g) g.cod := by
  cases g with
  | gen g => exact ⟨by simp [XShape.dom], by simp [XShape.cod]⟩
  | lcup i =>
    simp only [shapeSourceLayers]
    split_ifs
    · exact sChain_dcupL i _
    · exact (sChain_etaL i _).append (sChain_lcrossL i i)
  | lcap i =>
    simp only [shapeSourceLayers]
    split_ifs
    · exact sChain_dcapL i _
    · exact (sChain_lcrossL i i).append (sChain_epsL i _)

/-- The left-cup expansion is the ordinary diagram in the existing source
expression, with exactly its source scalar prefactor. -/
theorem etaPDiagram_sourceLayers {k : Type*} [CommRing k]
    {Sc : Scalars D k} (cs : CScalars Sc) (i : I) (μ : X) :
    ∃ r : k, etaPDiagram cs i μ = r •
      dg D μ (shapeSourceLayers D μ (.lcup i)) (shapeSourceLayers_chain D μ (.lcup i)) := by
  simp only [etaPDiagram, shapeSourceLayers]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The analogous source-expression anchor for the derived left cap. -/
theorem epsPDiagram_sourceLayers {k : Type*} [CommRing k]
    {Sc : Scalars D k} (cs : CScalars Sc) (i : I) (μ : X) :
    ∃ r : k, epsPDiagram cs i μ = r •
      dg D μ (shapeSourceLayers D μ (.lcap i)) (shapeSourceLayers_chain D μ (.lcap i)) := by
  simp only [epsPDiagram, shapeSourceLayers]
  split_ifs <;> exact ⟨_, rfl⟩

theorem tableSourceLayers_chain (μ : X) {a b : List (Letter I)}
    {L : List (XLayer I)} (h : XChain a L b) :
    SChain a (tableSourceLayers D μ L) b := by
  induction L generalizing a with
  | nil => exact h
  | cons x L ih =>
    obtain ⟨rfl, ht⟩ := h
    exact ((shapeSourceLayers_chain D (wt D μ x.2.2) x.2.1).whisk x.1 x.2.2).append (ih ht)

theorem tableSourceLayers_degree (sy : Symmetrizer D) (μ : X) (L : List (XLayer I)) :
    gsum D sy μ (tableSourceLayers D μ L) = tableDegree D sy μ L := by
  have hshape (ν : X) (g : XShape I) :
      gsum D sy ν (shapeSourceLayers D ν g) =
        tableDegree D sy ν [([], g, [])] := by
    cases g with
    | gen g => simp [shapeSourceLayers, gsum, tableDegree]
    | lcup i =>
      rw [tableDegree_etaP_source]
      simp only [shapeSourceLayers]
      split_ifs <;> rfl
    | lcap i =>
      rw [tableDegree_epsP_source]
      simp only [shapeSourceLayers]
      split_ifs <;> rfl
  have hwh (K : List (LayerData I)) (u v : List (Letter I)) :
      gsum D sy μ (K.map (whL u v)) = gsum D sy (wt D μ v) K := by
    simp [gsum, Function.comp_def, whL, wt_append]
  induction L with
  | nil => rfl
  | cons x L ih =>
    change gsum D sy μ ((shapeSourceLayers D (wt D μ x.2.2) x.2.1).map
      (whL x.1 x.2.2) ++ tableSourceLayers D μ L) = _
    rw [gsum_append, hwh, hshape, ih]
    simp [tableDegree]

/-- A fitting mixed decorated move list gives its existing extended layer chain. -/
theorem matching_dLay_chain {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R)
    (ds : List (DTMove I)) (hd : DTMove.tmoves ds = R) : XChain a (dLay a ds) b := by
  have hf := (tFits_shift a.length (tStart a) R).1 hR.1
  have h := (shiftD_spec (dualW a) a.length (length_dualW a) ds (tStart_letters a)
    (by rw [tmoves_map_shiftD, hd]; exact hf)).2.1
  simpa only [hd, hR.2] using h

/-- Ordinary source branches realize the fixed serializer's generator-table degree.
These are branch expansions, not a false literal `map ofL = dLay` assertion in the
presence of derived left cups or caps. -/
theorem mixed_labelled_source_degree_finite (sy : Symmetrizer D) (μ : X)
    (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R)
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S)
    (q : {R // R ∈ M} → ℕ → ℕ × ℕ)
    (hq : ∀ R j, j ∈ leftEnds₂ a R.val → OnStrand₂ a R.val j (q R j))
    (τ : ∀ R : {R // R ∈ M}, (MatchingStrand a R.val → ℕ) → List (DTMove I))
    (hτ : ∀ R c, Decorates₂ a R.val (q R) (strandCounts c) (τ R c)) :
    let T := Σ R : {R // R ∈ M}, MatchingStrand a R.val → ℕ
    ∃ (L : T → List (LayerData I)) (hL : ∀ t, SChain a (L t) b),
      (∀ t, Diagram.degree (gdeg D sy) (mkD D μ (L t) (hL t)) =
        tableDegree D sy μ (dLay a (τ t.1 t.2))) ∧
      ∀ z : ℤ, Set.Finite {t : T |
        Diagram.degree (gdeg D sy) (mkD D μ (L t) (hL t)) = z} := by
  let T := Σ R : {R // R ∈ M}, MatchingStrand a R.val → ℕ
  let L (t : T) := tableSourceLayers D μ (dLay a (τ t.1 t.2))
  have hL (t : T) : SChain a (L t) b := tableSourceLayers_chain D μ
    (matching_dLay_chain (hM t.1 t.1.property) _ (hτ t.1 t.2).1)
  have hd (t : T) : Diagram.degree (gdeg D sy) (mkD D μ (L t) (hL t)) =
      tableDegree D sy μ (dLay a (τ t.1 t.2)) := by
    rw [degree_gdeg_mkD]
    exact tableSourceLayers_degree D sy μ _
  refine ⟨L, hL, hd, fun z => ?_⟩
  simpa only [hd] using mixed_labelled_degree_finite D sy μ a b M hM huniq q hq τ hτ z

end OddMath.SKM
