import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorDotObservation
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossClasses

/-! # The literal crossing layers on the canonical quotient observation

SwappedVacuumCoordinates §§5–7. On the canonical global quotient
observation `tensorMatrixQuotientObservation`, the literal equal-colour and
distinct-colour crossing layers of the full chosen action
`(P).swappedGens a leftward` multiply the observed class on the right by the
original affine crossing `sourceCoefficientHom 1` of `layerDiagram`.

The proof is one generic pair square (`TensorDotObservation.pair_observation`),
stated for an arbitrary entry factoring through an equality-transport
conjugate of a cell heterogeneously equal to the whiskered ELV crossing.
It is instantiated with:

* the literal layer entry `tensorOriginalWordEntry_layer`;
* the coherence `tensorOriginalWordLayer_sameCross_transport` and
  `tensorOriginalWordLayer_cross_transport`;
* the chart identification `tensorPathValueChart_pair_heq`;
* the contextual crossing class square `TensorLayerClasses.cross_class_square`.

The observed input class is the only hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorCrossObservationHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C

open private OddMath.QuiverHecke.ELVOld.ReservoirLayerCells.crossCell_heq
  OddMath.QuiverHecke.ELVOld.ReservoirLayerCells.crossFunctor_heq
  from OddMath.QuiverHecke.CyclotomicAction.ELVReservoirLayerCells

namespace TensorDotObservation

section Pair
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "W" => elvRouquierData D Tw cutoff N ΛR
local notation "Hx" x => probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x

/-- An equality-transport conjugate of a cell, composed after an entry. -/
theorem comp_heq₂ {x x' : X} (e : x = x') {S U A V B : Hx x} {S' M M' : Hx x'}
    (hS : HEq S S') (hA : HEq A M) (hB : HEq B M') (h₁ : U = A) (h₂ : V = B)
    (g : S ⟶ U) (f : S' ⟶ M) (hg : HEq (g ≫ eqToHom h₁) f) (R : A ⟶ B) (R' : M ⟶ M')
    (hR : HEq R R') : HEq (g ≫ eqToHom h₁ ≫ R ≫ eqToHom h₂.symm) (f ≫ R') := by
  subst e
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hA
  obtain rfl := eq_of_heq hB
  subst h₁
  subst h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg ⊢
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hR
  rfl

omit [AddCommGroup X] [Fintype I] in
theorem cross_word_source (ν η : List I) (i j : I) :
    (PowerWordLayerClasses.domWord ν η (.cross i j)).reverse =
      PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η := by
  simp [PowerWordLayerClasses.domWord, Shape.dom, List.reverse_append,
    PowerWordContexts.extendedWord_eq, List.append_assoc]

/-- The contextual pair vector is its evaluated pair-chart vector, read as a word. -/
theorem crossVector_heq (ν η : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (G : Hx (PowerWordWeightContexts.contextWeight D xu η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E j h₁ ≫ (W).E i h₂ ≫ TensorHomContexts.context D Tw cutoff L ΛR xu η)
    (s : List I) (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D xu η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β.1)) :
    HEq (TensorLayerClasses.crossVector D Sc cutoff L m ΛP ΛR ν η i j h₁ h₂ G f s β hs z)
      ((((TensorHomContexts.pairChart D Tw m cutoff L ΛP ΛR ν η i j h₁ h₂).hom β).total
        (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β.1))
          (((f.total R₀) β).total (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β.1) z)) := by
  show HEq (reindex D Sc cutoff L (cross_word_source ν η i j).symm _ _) _
  exact reindex_heq D Sc cutoff L _ _ _

/-- **Generic pair square.** An entry `out` which is a whole-Hom entry `g`
followed by an equality-transport conjugate of a cell heterogeneously equal to
the whiskered ELV crossing has, on the evaluated regular-probe vector, the
input class multiplied by the original affine crossing. -/
theorem pair_observation (ν η : List I) (i j : I) {xj xu xi : X}
    {h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj} {h₂ : xj + D.α i = xu}
    {h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi} {h₄ : xi + D.α j = xu}
    {x : X} (e : x = PowerWordWeightContexts.contextWeight D xu η)
    {S Fp Fq A B : Hx x} (g : S ⟶ Fp) (out : S ⟶ Fq)
    (h₁t : Fp = A) (h₂t : Fq = B) (Raw : A ⟶ B)
    (hout : out = g ≫ eqToHom h₁t ≫ Raw ≫ eqToHom h₂t.symm)
    (hA : HEq A (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E j h₁ ≫ (W).E i h₂ ≫ TensorHomContexts.context D Tw cutoff L ΛR xu η))
    (hB : HEq B (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E i h₃ ≫ (W).E j h₄ ≫ TensorHomContexts.context D Tw cutoff L ΛR xu η))
    (hRaw : HEq Raw ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
      (W).cross i j h₁ h₂ h₃ h₄) ▷ TensorHomContexts.context D Tw cutoff L ΛR xu η))
    (td tc : List I)
    (hwp : td.reverse = PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η)
    (hwq : tc.reverse = PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η)
    (χp : Fp.obj R₀ ⟶ PowerWordWeight.wordFamily D Tw cutoff L ΛR x td.reverse)
    (χq : Fq.obj R₀ ⟶ PowerWordWeight.wordFamily D Tw cutoff L ΛR x tc.reverse)
    (hχp : HEq χp (TensorHomContexts.pairChart D Tw m cutoff L ΛP ΛR ν η i j h₁ h₂).hom)
    (hχq : HEq χq (TensorHomContexts.pairChart D Tw m cutoff L ΛP ΛR ν η j i h₃ h₄).hom)
    (htd : PowerWordLayerClasses.domWord ν η (.cross i j) = td)
    (htc : PowerWordLayerClasses.codWord ν η (.cross i j) = tc)
    (s : List I) (β₀ : WeightBlocks D ΛR x) (hs : (s.reverse : Multiset I) = β₀.1)
    (z₀ : ((S.obj R₀) β₀).obj (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β₀.1))
    (y : coefficientObj D Sc s ⟶
      coefficientObj D Sc (PowerWordLayerClasses.domWord ν η (.cross i j)))
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s td
        ((χp β₀).total (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β₀.1)
          (((g.total R₀) β₀).total (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β₀.1) z₀)) =
      tensorTargetWordQuotientEquiv D Sc cutoff L s htd
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.domWord ν η (.cross i j))).mkQ y)) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s tc
        ((χq β₀).total (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β₀.1)
          (((out.total R₀) β₀).total (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β₀.1) z₀)) =
      tensorTargetWordQuotientEquiv D Sc cutoff L s htc
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.codWord ν η (.cross i j))).mkQ
            (y ≫ sourceCoefficientHom D Sc 1
              (ContextualOldGenerators.layerDiagram D Sc η.reverse (.cross i j) ν.reverse))) := by
  obtain ⟨S', f, hS, hf⟩ := exists_transport D Sc m cutoff L ΛP ΛR e hA (g ≫ eqToHom h₁t)
  obtain ⟨z', hz⟩ := exists_vector D Sc m cutoff L ΛP ΛR e hS β₀ _ z₀
  have hFp := (heq_of_eq h₁t).trans hA
  have hFq := (heq_of_eq h₂t).trans hB
  have hin := (eval_heq D Sc m cutoff L ΛP ΛR e hS hFp g f
    ((comp_eqToHom_heq' D Sc m cutoff L ΛP ΛR g h₁t).symm.trans hf) hwp χp _ hχp β₀ _ z₀ z' hz).trans
      (crossVector_heq D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂ S' f s ⟨β₀.1, β₀.2.trans e⟩ hs z').symm
  have hy' : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s
      (PowerWordLayerClasses.domWord ν η (.cross i j))
      (TensorLayerClasses.crossVector D Sc cutoff L m ΛP ΛR ν η i j h₁ h₂ S' f s
        ⟨β₀.1, β₀.2.trans e⟩ hs z') =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s
        (PowerWordLayerClasses.domWord ν η (.cross i j))).mkQ y := by
    apply (tensorTargetWordQuotientEquiv D Sc cutoff L s htd).injective
    exact (coordinate_heq D Sc cutoff L s htd.symm _ _ hin).symm.trans hy
  have hsq := TensorLayerClasses.cross_class_square D Sc cutoff L m ΛP ΛR ν η i j h₁ h₂ h₃ h₄
    S' f s ⟨β₀.1, β₀.2.trans e⟩ hs z' y hy'
  have hout' : HEq out (f ≫ ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
      (W).cross i j h₁ h₂ h₃ h₄) ▷ TensorHomContexts.context D Tw cutoff L ΛR xu η)) := by
    rw [hout]
    exact comp_heq₂ D Sc m cutoff L ΛP ΛR e hS hA hB h₁t h₂t g f hf Raw _ hRaw
  have hV := (eval_heq D Sc m cutoff L ΛP ΛR e hS hFq out _ hout' hwq χq _ hχq β₀ _ z₀ z' hz).trans
    (crossVector_heq D Sc m cutoff L ΛP ΛR ν η j i h₃ h₄ S' _ s ⟨β₀.1, β₀.2.trans e⟩ hs z').symm
  have hc := coordinate_heq D Sc cutoff L s htc.symm _ _ hV
  rw [hsq] at hc
  exact hc

end Pair

end TensorDotObservation

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "Q" => interpretation D Sc m cutoff N ΛP ΛR hP hR
  (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)

section Same
variable (ν : X) (u v : List (Letter I)) (i : I)
  {c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
  (pL : SPath (SKM.lay D ν u (.cross i i) v).left (0,cS) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.cross i i) v).right
    (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]))
  false (0,c) hv (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _))
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "Aℓ" => SKM.lay D ν u (SKM.Shape.cross i i) v
local notation "νR" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.right (SKM.lay D ν u (SKM.Shape.cross i i) v))))
local notation "ηL" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.left (SKM.lay D ν u (SKM.Shape.cross i i) v))))

omit [CommRing k] [Fintype I] in
/-- The literal equal-colour crossing layer word, read through its outer contexts. -/
theorem tensorSameCrossLayer_domWord :
    PowerWordLayerClasses.domWord νR ηL (.cross i i) =
      ((((Aℓ).left : List (Col I X)) ++ [Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]),
        Col.mk (up i) (SKM.wt D ν v)]) ++ ((Aℓ).right : List (Col I X))).map (fun a => a.l.2) := by
  simp [PowerWordLayerClasses.domWord, Shape.dom]

omit [CommRing k] [Fintype I] in
theorem tensorSameCrossLayer_codWord :
    PowerWordLayerClasses.codWord νR ηL (.cross i i) =
      ((((Aℓ).left : List (Col I X)) ++ [Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]),
        Col.mk (up i) (SKM.wt D ν v)]) ++ ((Aℓ).right : List (Col I X))).map (fun a => a.l.2) := by
  simp [PowerWordLayerClasses.codWord, Shape.cod]

omit [CommRing k] [Fintype I] in
private theorem samePathWord :
    (((((Aℓ).left : List (Col I X)) ++ [Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]),
        Col.mk (up i) (SKM.wt D ν v)]) ++ ((Aℓ).right : List (Col I X))).map (fun a => a.l.2)).reverse =
      PowerWordContexts.extendedWord ((νR ++ [i]) ++ [i]) ηL := by
  rw [PowerWordContexts.extendedWord_eq]
  simp

include hv hw pL hl pR hr in
/-- **Equal-colour crossing on the quotient observation.** The literal
equal-colour crossing layer of the full chosen action multiplies the
canonical observed class on the right by the original affine crossing,
including its half-turn sign, in the outer contexts read off the layer. -/
theorem tensorMatrixQuotientObservation_sameCross
    (a : (P).CrossCoeff) (leftward : (P).LeftwardData)
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) =
      (Aℓ).cod.endR)
    (hp : ∀ c ∈ (Aℓ).dom.word, c.l.1 = true)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) (Aℓ).dom)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord νR ηL (.cross i i)))
    (hy : tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom)
        (hEnd.trans (SKM.lay_valid D ν u (.cross i i) v).endR_eq) p hp x =
      tensorTargetWordQuotientEquiv D Sc cutoff L s
        (tensorSameCrossLayer_domWord D ν u v i)
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.domWord νR ηL (.cross i i))).mkQ y)) :
    tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) hEnd p hp
        (((Q ((P).swappedGens a leftward)).res (Aℓ).cod)
          ((Q ((P).swappedGens a leftward)).op (Aℓ)
            ((Q ((P).swappedGens a leftward)).ext (Aℓ).dom x))) =
      tensorTargetWordQuotientEquiv D Sc cutoff L s
        (tensorSameCrossLayer_codWord D ν u v i)
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.codWord νR ηL (.cross i i))).mkQ
            (y ≫ sourceCoefficientHom D Sc 1
              (ContextualOldGenerators.layerDiagram D Sc (List.reverse ηL) (.cross i i)
                (List.reverse νR)))) := by
  have hA := SKM.lay_valid D ν u (.cross i i) v
  have hE := tensorOriginalWordEntry_layer D Sc m cutoff ΛP ΛR L hP hR s
    ((P).swappedGens a leftward) (Aℓ) hA hEnd p p hp hp x
  obtain ⟨h₁, h₂, hT⟩ := tensorOriginalWordLayer_sameCross_transport D Sc m cutoff ΛP ΛR L hP hR
    ν u v i hv hw pL hl pR hr
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom) p hp)
    (tensorRowTargetIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom) p hp) a leftward
  have hout : tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) hEnd p hp
        (((Q ((P).swappedGens a leftward)).res (Aℓ).cod)
          ((Q ((P).swappedGens a leftward)).op (Aℓ)
            ((Q ((P).swappedGens a leftward)).ext (Aℓ).dom x))) =
      tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom)
        (hEnd.trans hA.endR_eq) p hp x ≫ eqToHom h₁ ≫
        tensorLayerSameCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr a ≫
          eqToHom h₂.symm := by
    rw [hE]
    exact congrArg _ hT
  have hRaw := (heq_of_eq (tensorLayerSameCrossRaw_eq D Sc m cutoff L ΛP ΛR hP hR
    ν u v i hv hw pL hl pR hr a)).trans
      (crossCell_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i i _ _ _ _)
  exact TensorDotObservation.pair_observation D Sc m cutoff L ΛP ΛR νR ηL i i
    (ReservoirContexts.word_weight D ΛR pL hl) _ _ h₁ h₂ _ hout
    (crossFunctor_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i i _ _)
    (crossFunctor_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i i _ _) hRaw _ _
    (samePathWord D ν u v i) (samePathWord D ν u v i) _ _
    (tensorPathValueChart_pair_heq D Sc m cutoff ΛP ΛR L p hp νR ηL i i _ _
      ((samePathWord D ν u v i).trans (PowerWordContexts.extendedWord_eq _ _)))
    (tensorPathValueChart_pair_heq D Sc m cutoff ΛP ΛR L p hp νR ηL i i _ _
      ((samePathWord D ν u v i).trans (PowerWordContexts.extendedWord_eq _ _)))
    (tensorSameCrossLayer_domWord D ν u v i) (tensorSameCrossLayer_codWord D ν u v i)
    s (tensorSourceWordBlock D ΛP ΛR s) rfl
    (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s) y hy

end Same

section Distinct
variable (ν : X) (u v : List (Letter I)) (i j : I)
  {c : I →₀ ℕ}
  (hv₁ : StepValid (true,i) false (0,c))
  (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
  (hw₁ : StepValid (true,j) false (0,c))
  (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
  (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
    nextSector (true,i) false (nextSector (true,j) false (0,c)))
  (pL : SPath (SKM.lay D ν u (.cross i j) v).left (0,cS) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.cross i j) v).right
    (0,c - Finsupp.single j 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).right, a.l.1 = true)
local notation "ps" => SPath.two (c₁ := Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]))
  (c₂ := Col.mk (up j) (SKM.wt D ν v)) false false hv₁ hv₂ hs
local notation "pt" => SPath.two (c₁ := Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]))
  (c₂ := Col.mk (up i) (SKM.wt D ν v)) false false hw₁ hw₂ rfl
local notation "p" => SPath.append (SPath.append pL ps) pR
local notation "q" => SPath.append (SPath.append pL pt) pR
local notation "Aℓ" => SKM.lay D ν u (SKM.Shape.cross i j) v
local notation "νR" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.right (SKM.lay D ν u (SKM.Shape.cross i j) v))))
local notation "ηL" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.left (SKM.lay D ν u (SKM.Shape.cross i j) v))))

omit [CommRing k] [Fintype I] in
/-- The literal distinct-colour crossing source word. -/
theorem tensorCrossLayer_domWord :
    PowerWordLayerClasses.domWord νR ηL (.cross i j) =
      ((((Aℓ).left : List (Col I X)) ++ [Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]),
        Col.mk (up j) (SKM.wt D ν v)]) ++ ((Aℓ).right : List (Col I X))).map (fun a => a.l.2) := by
  simp [PowerWordLayerClasses.domWord, Shape.dom]

omit [CommRing k] [Fintype I] in
/-- The literal distinct-colour crossing target word. -/
theorem tensorCrossLayer_codWord :
    PowerWordLayerClasses.codWord νR ηL (.cross i j) =
      ((((Aℓ).left : List (Col I X)) ++ [Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]),
        Col.mk (up i) (SKM.wt D ν v)]) ++ ((Aℓ).right : List (Col I X))).map (fun a => a.l.2) := by
  simp [PowerWordLayerClasses.codWord, Shape.cod]

omit [CommRing k] [Fintype I] in
private theorem crossSourcePathWord :
    (((((Aℓ).left : List (Col I X)) ++ [Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]),
        Col.mk (up j) (SKM.wt D ν v)]) ++ ((Aℓ).right : List (Col I X))).map (fun a => a.l.2)).reverse =
      PowerWordContexts.extendedWord ((νR ++ [j]) ++ [i]) ηL := by
  rw [PowerWordContexts.extendedWord_eq]
  simp

omit [CommRing k] [Fintype I] in
private theorem crossTargetPathWord :
    (((((Aℓ).left : List (Col I X)) ++ [Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]),
        Col.mk (up i) (SKM.wt D ν v)]) ++ ((Aℓ).right : List (Col I X))).map (fun a => a.l.2)).reverse =
      PowerWordContexts.extendedWord ((νR ++ [i]) ++ [j]) ηL := by
  rw [PowerWordContexts.extendedWord_eq]
  simp

include hv₁ hv₂ hw₁ hw₂ hs pL hl pR hr in
/-- **Distinct-colour crossing on the quotient observation.** The literal
distinct-colour crossing layer of the full chosen action multiplies the
canonical observed class on the right by the original affine crossing,
in the outer contexts read off the layer. -/
theorem tensorMatrixQuotientObservation_cross (hij : i ≠ j)
    (a : (P).CrossCoeff) (leftward : (P).LeftwardData)
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) =
      (Aℓ).cod.endR)
    (hp : ∀ c ∈ (Aℓ).dom.word, c.l.1 = true) (hq : ∀ c ∈ (Aℓ).cod.word, c.l.1 = true)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) (Aℓ).dom)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord νR ηL (.cross i j)))
    (hy : tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom)
        (hEnd.trans (SKM.lay_valid D ν u (.cross i j) v).endR_eq) p hp x =
      tensorTargetWordQuotientEquiv D Sc cutoff L s
        (tensorCrossLayer_domWord D ν u v i j)
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.domWord νR ηL (.cross i j))).mkQ y)) :
    tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) hEnd q hq
        (((Q ((P).swappedGens a leftward)).res (Aℓ).cod)
          ((Q ((P).swappedGens a leftward)).op (Aℓ)
            ((Q ((P).swappedGens a leftward)).ext (Aℓ).dom x))) =
      tensorTargetWordQuotientEquiv D Sc cutoff L s
        (tensorCrossLayer_codWord D ν u v i j)
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.codWord νR ηL (.cross i j))).mkQ
            (y ≫ sourceCoefficientHom D Sc 1
              (ContextualOldGenerators.layerDiagram D Sc (List.reverse ηL) (.cross i j)
                (List.reverse νR)))) := by
  have hA := SKM.lay_valid D ν u (.cross i j) v
  have hE := tensorOriginalWordEntry_layer D Sc m cutoff ΛP ΛR L hP hR s
    ((P).swappedGens a leftward) (Aℓ) hA hEnd p q hp hq x
  obtain ⟨h₁, h₂, hT⟩ := tensorOriginalWordLayer_cross_transport D Sc m cutoff ΛP ΛR L hP hR
    ν u v i j hv₁ hv₂ hw₁ hw₂ hs pL hl pR hr
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom) p hp)
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) q hq)
    (tensorRowTargetIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom) p hp)
    (tensorRowTargetIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) q hq)
    a leftward
  have hout : tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) hEnd q hq
        (((Q ((P).swappedGens a leftward)).res (Aℓ).cod)
          ((Q ((P).swappedGens a leftward)).op (Aℓ)
            ((Q ((P).swappedGens a leftward)).ext (Aℓ).dom x))) =
      tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom)
        (hEnd.trans hA.endR_eq) p hp x ≫ eqToHom h₁ ≫
        tensorLayerCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i j hv₁ hv₂ hw₁ hw₂ hs
          pL hl pR hr a ≫ eqToHom h₂.symm := by
    rw [hE]
    exact congrArg _ hT
  have hRaw := (heq_of_eq (tensorLayerCrossRaw_eq D Sc m cutoff L ΛP ΛR hP hR
    ν u v i j hv₁ hv₂ hw₁ hw₂ hs pL hl pR hr a hij)).trans
      (crossCell_heq D Sc m cutoff L ΛP ΛR pL hl _ hr i j _ _ _ _)
  exact TensorDotObservation.pair_observation D Sc m cutoff L ΛP ΛR νR ηL i j
    (ReservoirContexts.word_weight D ΛR pL hl) _ _ h₁ h₂ _ hout
    (crossFunctor_heq D Sc m cutoff L ΛP ΛR pL hl _ hr i j _ _)
    (crossFunctor_heq D Sc m cutoff L ΛP ΛR pL hl _ hr j i _ _) hRaw _ _
    (crossSourcePathWord D ν u v i j) (crossTargetPathWord D ν u v i j) _ _
    (tensorPathValueChart_pair_heq D Sc m cutoff ΛP ΛR L p hp νR ηL i j _ _
      ((crossSourcePathWord D ν u v i j).trans (PowerWordContexts.extendedWord_eq _ _)))
    (tensorPathValueChart_pair_heq D Sc m cutoff ΛP ΛR L q hq νR ηL j i _ _
      ((crossTargetPathWord D ν u v i j).trans (PowerWordContexts.extendedWord_eq _ _)))
    (tensorCrossLayer_domWord D ν u v i j) (tensorCrossLayer_codWord D ν u v i j)
    s (tensorSourceWordBlock D ΛP ΛR s) rfl
    (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s) y hy

end Distinct
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
