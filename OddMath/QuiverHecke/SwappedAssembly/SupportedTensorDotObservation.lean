import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorLayerChartTransport
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorDotClasses
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorPathChartCoherence
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorWordObservation

/-! # The literal dot layer on the canonical quotient observation

SwappedVacuumCoordinates §§5–7. On the canonical global quotient
observation `tensorMatrixQuotientObservation`, the literal dot layer of the
full chosen action `(P).swappedGens a leftward` multiplies the observed
class on the right by the original affine dot `sourceCoefficientHom 1` of
`layerDiagram`. The proof composes:

* the literal layer entry `tensorOriginalWordEntry_layer`;
* the equality-transport coherence `tensorOriginalWordLayer_dot_transport`;
* the global/local chart identification `tensorPathValueChart_dot_heq`;
* the contextual dot class square `TensorLayerClasses.dot_class_square`.

No generator comparison, faithfulness or expansion premise is supplied;
the observed input class is the only hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorDotObservationHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C

namespace TensorDotObservation

section Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "W" => elvRouquierData D Tw cutoff N ΛR
local notation "Hx" x => probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x

/-- A whole-Hom arrow transports along an equality of its outer weight. -/
theorem exists_transport {x x' : X} (e : x = x') {S F : Hx x} {M : Hx x'}
    (hF : HEq F M) (g : S ⟶ F) : ∃ (S' : Hx x') (f : S' ⟶ M), HEq S S' ∧ HEq g f := by
  subst e
  obtain rfl := eq_of_heq hF
  exact ⟨S, g, HEq.rfl, HEq.rfl⟩

/-- A source vector transports along an equality of its outer weight. -/
theorem exists_vector {x x' : X} (e : x = x') {S : Hx x} {S' : Hx x'} (hS : HEq S S')
    (β : WeightBlocks D ΛR x) (o : ContentCategory D Tw cutoff N β.1)
    (z : ((S.obj R₀) β).obj o) :
    ∃ z' : ((S'.obj R₀) (⟨β.1, β.2.trans e⟩ : WeightBlocks D ΛR x')).obj o, HEq z z' := by
  subst e
  obtain rfl := eq_of_heq hS
  exact ⟨z, HEq.rfl⟩

/-- Evaluation of a whole-Hom arrow through a chart, on a block, object and
vector, depends only on the heterogeneously equal data. -/
theorem eval_heq {x x' : X} (e : x = x') {G F : Hx x} {G' M : Hx x'}
    (hG : HEq G G') (hF : HEq F M) (ψ : G ⟶ F) (f : G' ⟶ M) (hψ : HEq ψ f)
    {w w' : List I} (hw : w = w')
    (χ : F.obj R₀ ⟶ PowerWordWeight.wordFamily D Tw cutoff L ΛR x w)
    (χ' : M.obj R₀ ⟶ PowerWordWeight.wordFamily D Tw cutoff L ΛR x' w')
    (hχ : HEq χ χ') (β : WeightBlocks D ΛR x) (o : ContentCategory D Tw cutoff N β.1)
    (z : ((G.obj R₀) β).obj o)
    (z' : ((G'.obj R₀) (⟨β.1, β.2.trans e⟩ : WeightBlocks D ΛR x')).obj o) (hz : HEq z z') :
    HEq ((χ β).total o (((ψ.total R₀) β).total o z))
      ((χ' ⟨β.1, β.2.trans e⟩).total o (((f.total R₀) ⟨β.1, β.2.trans e⟩).total o z')) := by
  subst e
  obtain rfl := eq_of_heq hG
  obtain rfl := eq_of_heq hF
  obtain rfl := eq_of_heq hψ
  subst hw
  obtain rfl := eq_of_heq hχ
  obtain rfl := eq_of_heq hz
  rfl

/-- The equality-transport conjugate of a layer cell, composed after an entry. -/
theorem comp_heq {x x' : X} (e : x = x') {S F₁ F₂ : Hx x} {S' M : Hx x'}
    (hS : HEq S S') (hF : HEq F₂ M) (h₁ h₂ : F₁ = F₂) (g : S ⟶ F₁) (f : S' ⟶ M)
    (hg : HEq (g ≫ eqToHom h₁) f) (R : F₂ ⟶ F₂) (R' : M ⟶ M) (hR : HEq R R') :
    HEq (g ≫ eqToHom h₁ ≫ R ≫ eqToHom h₂.symm) (f ≫ R') := by
  subst e
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hF
  subst h₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg ⊢
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hR
  rfl

theorem comp_eqToHom_heq' {x : X} {S F₁ F₂ : Hx x} (g : S ⟶ F₁) (h : F₁ = F₂) :
    HEq (g ≫ eqToHom h) g := by
  subst h
  simp

theorem postE_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y') {F : Hx x} {F' : Hx x'}
    (hF : HEq F F') : HEq (F ≫ (W).E i h) (F' ≫ (W).E i h') := by
  cases hx
  cases hy
  cases hF
  rfl

theorem postDot_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y') {F : Hx x} {F' : Hx x'}
    (hF : HEq F F') : HEq (F ◁ (W).dot i h) (F' ◁ (W).dot i h') := by
  cases hx
  cases hy
  cases hF
  rfl

theorem context_input_heq {x y : X} (h : x = y) (η : List I) :
    HEq (TensorHomContexts.context D Tw cutoff L ΛR x η)
      (TensorHomContexts.context D Tw cutoff L ΛR y η) := by cases h; rfl

theorem compose_heq {x x' y y' : X} (hx : x = x') (hy : y = y') {F : Hx x} {F' : Hx x'}
    {K : elvWeightSpace D Tw cutoff N ΛR x ⟶ elvWeightSpace D Tw cutoff N ΛR y}
    {K' : elvWeightSpace D Tw cutoff N ΛR x' ⟶ elvWeightSpace D Tw cutoff N ΛR y'}
    (hF : HEq F F') (hK : HEq K K') : HEq (F ≫ K) (F' ≫ K') := by
  cases hx
  cases hy
  cases hF
  cases hK
  rfl

theorem whisker_heq {x x' y y' : X} (hx : x = x') (hy : y = y') {F G : Hx x} {F' G' : Hx x'}
    {K : elvWeightSpace D Tw cutoff N ΛR x ⟶ elvWeightSpace D Tw cutoff N ΛR y}
    {K' : elvWeightSpace D Tw cutoff N ΛR x' ⟶ elvWeightSpace D Tw cutoff N ΛR y'}
    (hF : HEq F F') (hG : HEq G G') (hK : HEq K K') {a : F ⟶ G} {a' : F' ⟶ G'}
    (ha : HEq a a') : HEq (a ▷ K) (a' ▷ K') := by
  cases hx
  cases hy
  cases hF
  cases hG
  cases hK
  cases ha
  rfl

/-- A copy of the canonical reversed-word reindexing used by `dotVector`. -/
def reindex {s t : List I} (h : s = t) (w : OldCategory D Tw cutoff) :
    (powerWordModule D Tw cutoff L s).obj w →ₗ[k] (powerWordModule D Tw cutoff L t).obj w := by
  subst t
  exact LinearMap.id

omit [Fintype I] in
theorem reindex_heq {s t : List I} (h : s = t) (w : OldCategory D Tw cutoff)
    (v : (powerWordModule D Tw cutoff L s).obj w) : HEq (reindex D Sc cutoff L h w v) v := by
  subst t
  rfl

omit [AddCommGroup X] [Fintype I] in
theorem dot_word (ν η : List I) (i : I) :
    (PowerWordLayerClasses.domWord ν η (.dot i)).reverse =
      PowerWordContexts.extendedWord (ν ++ [i]) η := by
  simp [PowerWordLayerClasses.domWord, Shape.dom, List.reverse_append,
    PowerWordContexts.extendedWord_eq, List.append_assoc]

/-- The contextual dot vector is its evaluated chart vector, read as a word. -/
theorem dotVector_heq (ν η : List I) (i : I)
    (G : Hx (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
    (s : List I)
    (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D
      (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β.1)) :
    HEq (TensorLayerClasses.dotVector D Sc cutoff L m ΛP ΛR ν η i G f s β hs z)
      ((((TensorHomContexts.dotChart D Tw m cutoff L ΛP ΛR ν η i).hom β).total
        (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β.1))
          (((f.total R₀) β).total (⟨⟨s.reverse⟩, hs⟩ : ContentCategory D Tw cutoff N β.1) z)) := by
  show HEq (reindex D Sc cutoff L (dot_word ν η i).symm _ _) _
  exact reindex_heq D Sc cutoff L _ _ _

omit [Fintype I] in
/-- Coordinates of heterogeneously equal vectors at equal target words agree
up to the canonical target-word quotient transport. -/
theorem coordinate_heq (s : List I) {t t' : List I} (ht : t = t')
    (V : (powerWordModule D Tw cutoff L t.reverse).obj (OldCategory.mk s.reverse))
    (V' : (powerWordModule D Tw cutoff L t'.reverse).obj (OldCategory.mk s.reverse))
    (hV : HEq V V') :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t V =
      tensorTargetWordQuotientEquiv D Sc cutoff L s ht.symm
        (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t' V') := by
  subst ht
  obtain rfl := eq_of_heq hV
  rfl

omit [Fintype I] in
/-- The middle weight of a two-word dot, read from its right word. -/
theorem midWeight {r : List (SKM.Col I X)} {cR cM : I →₀ ℕ}
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    ReservoirWord.weight D ΛR cM =
      PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]) :=
  h.symm.trans ((congrArg (fun x => x + D.α i) (TensorReservoirWords.path_weight D ΛR pR hr)).trans
    (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i))

omit [Fintype I] in
/-- The endpoint weight of a two-word dot, in contextual form. -/
theorem endWeight {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    ReservoirWord.weight D ΛR cL = PowerWordWeightContexts.contextWeight D
      (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
      ((l.map (fun a => a.l.2)).reverse) :=
  (ReservoirContexts.word_weight D ΛR pL hl).trans
    (congrArg (fun x => PowerWordWeightContexts.contextWeight D x ((l.map (fun a => a.l.2)).reverse))
      (midWeight D ΛR pR hr i h))

/-- The raw two-word dot Hom is the contextual dot Hom. -/
theorem rawHom_heq {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    HEq (ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h)
      (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ((r.map (fun a => a.l.2)).reverse) ≫
        (W).E i (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i) ≫
        TensorHomContexts.context D Tw cutoff L ΛR
          (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
          ((l.map (fun a => a.l.2)).reverse)) := by
  have hm := postE_heq D Sc m cutoff L ΛP ΛR i (TensorReservoirWords.path_weight D ΛR pR hr)
    (midWeight D ΛR pR hr i h) h
    (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i)
    (TensorReservoirWords.pathHom_heq D Tw m cutoff L ΛP ΛR pR hr)
  have hk := (ReservoirContexts.word_heq D Tw cutoff L ΛR pL hl).trans
    (context_input_heq D Sc cutoff L ΛR (midWeight D ΛR pR hr i h)
      ((l.map (fun a => a.l.2)).reverse))
  exact compose_heq D Sc m cutoff L ΛP ΛR (midWeight D ΛR pR hr i h)
    (endWeight D ΛR pL hl pR hr i h) hm hk

/-- The raw two-word dot cell is the contextual dot cell. -/
theorem raw_heq {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    HEq (ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h)
      ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ((r.map (fun a => a.l.2)).reverse) ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i)) ▷
        TensorHomContexts.context D Tw cutoff L ΛR
          (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
          ((l.map (fun a => a.l.2)).reverse)) := by
  have hp := TensorReservoirWords.pathHom_heq D Tw m cutoff L ΛP ΛR pR hr
  have hx := TensorReservoirWords.path_weight D ΛR pR hr
  have hy := midWeight D ΛR pR hr i h
  have hm := postE_heq D Sc m cutoff L ΛP ΛR i hx hy h
    (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i) hp
  have ha := postDot_heq D Sc m cutoff L ΛP ΛR i hx hy h
    (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i) hp
  have hk := (ReservoirContexts.word_heq D Tw cutoff L ΛR pL hl).trans
    (context_input_heq D Sc cutoff L ΛR hy ((l.map (fun a => a.l.2)).reverse))
  exact whisker_heq D Sc m cutoff L ΛP ΛR hy (endWeight D ΛR pL hl pR hr i h) hm hm hk ha

end Generic

end TensorDotObservation

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "W" => elvRouquierData D Tw cutoff N ΛR
local notation "Q" => interpretation D Sc m cutoff N ΛP ΛR hP hR
  (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)

local notation "colApp" =>
  @HAppend.hAppend (List (Col I X)) (List (Col I X)) (List (Col I X)) instHAppendOfAppend

section Dot
variable (ν : X) (u v : List (Letter I)) (i : I)
  {c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (pL : SPath (SKM.lay D ν u (.dot i) v).left (0,cS) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.dot i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.dot i) v).right (0,c - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.dot i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _)
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "edge" => ProbeReservoir.reservoirVacuumEdge (P) i c hv
local notation "Aℓ" => SKM.lay D ν u (SKM.Shape.dot i) v
local notation "νR" => (List.reverse (List.map (fun (a : SKM.Col I X) => Prod.snd (SKM.Col.l a)) (Layer.right (SKM.lay D ν u (SKM.Shape.dot i) v))))
local notation "ηL" => (List.reverse (List.map (fun (a : SKM.Col I X) => Prod.snd (SKM.Col.l a)) (Layer.left (SKM.lay D ν u (SKM.Shape.dot i) v))))

omit [CommRing k] [Fintype I] in
/-- The literal dot layer source word, read through its outer contexts. -/
theorem tensorDotLayer_domWord :
    PowerWordLayerClasses.domWord νR ηL (.dot i) =
      (colApp (colApp (Aℓ).left [Col.mk (up i) (SKM.wt D ν v)]) (Aℓ).right).map (fun a => a.l.2) := by
  simp [PowerWordLayerClasses.domWord, Shape.dom]

omit [CommRing k] [Fintype I] in
/-- The literal dot layer target word, read through its outer contexts. -/
theorem tensorDotLayer_codWord :
    PowerWordLayerClasses.codWord νR ηL (.dot i) =
      (colApp (colApp (Aℓ).left [Col.mk (up i) (SKM.wt D ν v)]) (Aℓ).right).map (fun a => a.l.2) := by
  simp [PowerWordLayerClasses.codWord, Shape.cod]

omit [CommRing k] [Fintype I] in
private theorem dotPathWord :
    ((colApp (colApp (Aℓ).left [Col.mk (up i) (SKM.wt D ν v)]) (Aℓ).right).map (fun a => a.l.2)).reverse =
      (νR ++ [i]) ++ ηL := by
  simp

private theorem dotRawHom_heq :
    HEq (ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i edge)
      (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR νR ≫
        (W).E i (PowerWordWeight.wordWeight_append D ΛR νR i) ≫
        TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL) :=
  TensorDotObservation.rawHom_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i edge

private theorem dotRaw_heq (a : (P).CrossCoeff) :
    HEq (tensorLayerDotRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a)
      ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR νR ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR νR i)) ▷
        TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL) :=
  (heq_of_eq (tensorLayerDotRaw_eq D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a)).trans
    (TensorDotObservation.raw_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i edge)

include hl hr in
/-- **Dot layer on the quotient observation.** The literal dot layer of the full
chosen action multiplies the canonical observed class on the right by the
original affine dot, in the outer contexts read off the layer. -/
theorem tensorMatrixQuotientObservation_dot
    (a : (P).CrossCoeff) (leftward : (P).LeftwardData)
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) =
      (Aℓ).cod.endR)
    (hp : ∀ c ∈ (Aℓ).dom.word, c.l.1 = true)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) (Aℓ).dom)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord νR ηL (.dot i)))
    (hy : tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom)
        (hEnd.trans (SKM.lay_valid D ν u (.dot i) v).endR_eq) p hp x =
      tensorTargetWordQuotientEquiv D Sc cutoff L s
        (tensorDotLayer_domWord D ν u v i)
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.domWord νR ηL (.dot i))).mkQ y)) :
    tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) hEnd p hp
        (((Q ((P).swappedGens a leftward)).res (Aℓ).cod)
          ((Q ((P).swappedGens a leftward)).op (Aℓ)
            ((Q ((P).swappedGens a leftward)).ext (Aℓ).dom x))) =
      tensorTargetWordQuotientEquiv D Sc cutoff L s
        (tensorDotLayer_codWord D ν u v i)
        ((PowerWordQuotientCoordinates.kernel D Sc cutoff L s
          (PowerWordLayerClasses.codWord νR ηL (.dot i))).mkQ
            (y ≫ sourceCoefficientHom D Sc 1
              (ContextualOldGenerators.layerDiagram D Sc (List.reverse ηL) (.dot i) (List.reverse νR)))) := by
  have hA := SKM.lay_valid D ν u (.dot i) v
  -- the literal layer entry, and its equality-transport form
  have hE := tensorOriginalWordEntry_layer D Sc m cutoff ΛP ΛR L hP hR s
    ((P).swappedGens a leftward) (Aℓ) hA hEnd p p hp hp x
  have hT₀ := tensorOriginalWordLayer_dot_transport D Sc m cutoff ΛP ΛR L hP hR
    ν u v i hv pL hl pR hr
  have hT₁ := hT₀ (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom) p hp)
  have hT₂ := hT₁ (tensorRowTargetIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom) p hp)
  obtain ⟨h₁, h₂, hT⟩ := hT₂ a leftward
  have hL : tensorOriginalWordLayer D Sc m cutoff ΛP ΛR L hP hR s ((P).swappedGens a leftward)
      (Aℓ) p p hp hp = eqToHom h₁ ≫
        tensorLayerDotRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a ≫ eqToHom h₂.symm :=
    hT
  -- transport to the contextual weight of the local dot chart
  have e : ReservoirWord.weight D ΛR cS = PowerWordWeightContexts.contextWeight D
      (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL :=
    TensorDotObservation.endWeight D ΛR pL hl pR hr i edge
  have hM := dotRawHom_heq D Sc m cutoff ΛP ΛR L hP hR s ν u v i hv pL hl pR hr
  let entry := tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).dom)
    (hEnd.trans hA.endR_eq) p hp x
  obtain ⟨S', f, hS, hf⟩ := TensorDotObservation.exists_transport D Sc m cutoff L ΛP ΛR e hM
    (entry ≫ eqToHom h₁)
  let β₀ := tensorSourceWordBlock D ΛP ΛR s
  let o₀ := PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl
  obtain ⟨z', hz⟩ := TensorDotObservation.exists_vector D Sc m cutoff L ΛP ΛR e hS β₀ o₀
    (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)
  have hpath := (tensorPathValueChart_dot_heq D Sc m cutoff ΛP ΛR L p hp νR ηL i
    (dotPathWord D ν u v i))
  have hw : ((colApp (colApp (Aℓ).left [Col.mk (up i) (SKM.wt D ν v)]) (Aℓ).right).map
      (fun a => a.l.2)).reverse = PowerWordContexts.extendedWord (νR ++ [i]) ηL :=
    (dotPathWord D ν u v i).trans (PowerWordContexts.extendedWord_eq _ _).symm
  have hF : HEq (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hp)
      (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR νR ≫
        (W).E i (PowerWordWeight.wordWeight_append D ΛR νR i) ≫
        TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL) :=
    (heq_of_eq h₁).trans hM
  -- the input class, read at the local dot chart
  have hin := TensorDotObservation.eval_heq D Sc m cutoff L ΛP ΛR e hS hF entry f
    ((TensorDotObservation.comp_eqToHom_heq' D Sc m cutoff L ΛP ΛR entry h₁).symm.trans hf) hw
    (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hp).hom
    (TensorHomContexts.dotChart D Tw m cutoff L ΛP ΛR νR ηL i).hom hpath β₀ o₀
    (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s) z' hz
  have hin' := hin.trans (TensorDotObservation.dotVector_heq D Sc m cutoff L ΛP ΛR νR ηL i S' f s
    ⟨β₀.1, β₀.2.trans e⟩ rfl z').symm
  have hy' : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s
      (PowerWordLayerClasses.domWord νR ηL (.dot i))
      (TensorLayerClasses.dotVector D Sc cutoff L m ΛP ΛR νR ηL i S' f s
        ⟨β₀.1, β₀.2.trans e⟩ rfl z') =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s
        (PowerWordLayerClasses.domWord νR ηL (.dot i))).mkQ y := by
    apply (tensorTargetWordQuotientEquiv D Sc cutoff L s
      (tensorDotLayer_domWord D ν u v i)).injective
    exact (TensorDotObservation.coordinate_heq D Sc cutoff L s
      (tensorDotLayer_domWord D ν u v i).symm _ _ hin').symm.trans hy
  have hsq := TensorLayerClasses.dot_class_square D Sc cutoff L m ΛP ΛR νR ηL i S' f s
    ⟨β₀.1, β₀.2.trans e⟩ rfl z' y hy'
  -- the output class
  have hR := dotRaw_heq D Sc m cutoff ΛP ΛR L hP hR s ν u v i hv pL hl pR hr a
  have hout : HEq (tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s (a := (Aℓ).cod) hEnd p hp
        (((Q ((P).swappedGens a leftward)).res (Aℓ).cod)
          ((Q ((P).swappedGens a leftward)).op (Aℓ)
            ((Q ((P).swappedGens a leftward)).ext (Aℓ).dom x))))
      (f ≫ ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR νR ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR νR i)) ▷
        TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL)) := by
    rw [hE, hL]
    exact TensorDotObservation.comp_heq D Sc m cutoff L ΛP ΛR e hS hM h₁ h₂ entry f hf _ _ hR
  have hV := (TensorDotObservation.eval_heq D Sc m cutoff L ΛP ΛR e hS hF _ _ hout hw
    (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hp).hom
    (TensorHomContexts.dotChart D Tw m cutoff L ΛP ΛR νR ηL i).hom hpath β₀ o₀
    (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s) z' hz).trans
      (TensorDotObservation.dotVector_heq D Sc m cutoff L ΛP ΛR νR ηL i S' _ s
        ⟨β₀.1, β₀.2.trans e⟩ rfl z').symm
  have hc := TensorDotObservation.coordinate_heq D Sc cutoff L s
    (tensorDotLayer_codWord D ν u v i).symm _ _ hV
  rw [hsq] at hc
  exact hc

end Dot
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
