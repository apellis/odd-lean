import OddMath.QuiverHecke.CyclotomicAction.TensorWord
import OddMath.QuiverHecke.CyclotomicAction.TensorWords
import OddMath.QuiverHecke.CyclotomicAction.ReservoirClosure
import OddMath.QuiverHecke.CyclotomicAction.WeightDenominators
import OddMath.SKM.RouquierHomPostPowers
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.WeightedPower

/-!
# Reservoir layers

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Actual reservoir-word cells in tensor quotient coordinates

SwappedVacuumCoordinates §§2–7: retain the selected tensor Hom, both
actual reservoir words and the given middle generator at its original
weight vertices, then attach its whole cell to the chosen tensor chart.
No complete swapped factor, boundary-support or faithfulness premise is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.ReservoirLayerCells
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => elvRouquierData D Tw cutoff N ΛR

private def atHom {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x) :
    probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR y := h ▸ F

private def atCell {x y : X} (h : x = y)
    {F G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    (a : F ⟶ G) : atHom D Sc m cutoff L ΛP ΛR h F ⟶ atHom D Sc m cutoff L ΛP ΛR h G := by
  cases h
  exact a

private theorem atHom_heq {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x) :
    HEq (atHom D Sc m cutoff L ΛP ΛR h F) F := by cases h; rfl

private theorem atCell_heq {x y : X} (h : x = y)
    {F G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    (a : F ⟶ G) : HEq (atCell D Sc m cutoff L ΛP ΛR h a) a := by cases h; rfl

private theorem context_input_heq {x y : X} (h : x = y) (η : List I) :
    HEq (TensorHomContexts.context D Tw cutoff L ΛR x η)
      (TensorHomContexts.context D Tw cutoff L ΛR y η) := by cases h; rfl

private theorem postE_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    {F' : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x'}
    (hF : HEq F F') : HEq (F ≫ (W).E i h) (F' ≫ (W).E i h') := by
  cases hx
  cases hy
  cases hF
  rfl

private theorem postDot_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    {F' : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x'}
    (hF : HEq F F') : HEq (F ◁ (W).dot i h) (F' ◁ (W).dot i h') := by
  cases hx
  cases hy
  cases hF
  rfl

private theorem pairFunctor_heq (i j : I) {x x' xj xu : X} (hx : x = x')
    (h₁ : x + D.α j = xj) (h₂ : xj + D.α i = xu) (h₁' : x' + D.α j = xj)
    {F : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    {F' : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x'}
    (hF : HEq F F') :
    HEq (F ≫ (W).E j h₁ ≫ (W).E i h₂) (F' ≫ (W).E j h₁' ≫ (W).E i h₂) := by
  cases hx
  cases hF
  rfl

private theorem postCross_heq (i j : I) {x x' xj xu xi : X} (hx : x = x')
    (h₁ : x + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : x + D.α i = xi) (h₄ : xi + D.α j = xu)
    (h₁' : x' + D.α j = xj) (h₃' : x' + D.α i = xi)
    {F : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    {F' : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x'}
    (hF : HEq F F') :
    HEq (F ◁ (W).cross i j h₁ h₂ h₃ h₄) (F' ◁ (W).cross i j h₁' h₂ h₃' h₄) := by
  cases hx
  cases hF
  rfl

private theorem compose_heq {x x' y y' : X} (hx : x = x') (hy : y = y')
    {F : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    {F' : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x'}
    {K : elvWeightSpace D Tw cutoff N ΛR x ⟶ elvWeightSpace D Tw cutoff N ΛR y}
    {K' : elvWeightSpace D Tw cutoff N ΛR x' ⟶ elvWeightSpace D Tw cutoff N ΛR y'}
    (hF : HEq F F') (hK : HEq K K') : HEq (F ≫ K) (F' ≫ K') := by
  cases hx
  cases hy
  cases hF
  cases hK
  rfl

private theorem whisker_heq {x x' y y' : X} (hx : x = x') (hy : y = y')
    {F G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x}
    {F' G' : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR x'}
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

private theorem heq_square {C : Type*} [Category* C] {A A' B B' : C}
    (hA : A = A') (hB : B = B') (a : A ⟶ B) (b : A' ⟶ B') (h : HEq a b) :
    a ≫ eqToHom hB = eqToHom hA ≫ b := by
  subst A' B'
  cases h
  simp

omit [Fintype I] in
private theorem dotMidWeight {r : List (SKM.Col I X)} {cR cM : I →₀ ℕ}
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    ReservoirWord.weight D ΛR cM = PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]) :=
  h.symm.trans ((congrArg (fun x => x + D.α i) (TensorReservoirWords.path_weight D ΛR pR hr)).trans
    (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i))

omit [Fintype I] in
private theorem dotEndWeight {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    ReservoirWord.weight D ΛR cL = PowerWordWeightContexts.contextWeight D
      (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
      ((l.map (fun a => a.l.2)).reverse) :=
  (ReservoirContexts.word_weight D ΛR pL hl).trans
    (congrArg (fun x => PowerWordWeightContexts.contextWeight D x ((l.map (fun a => a.l.2)).reverse))
      (dotMidWeight D ΛR pR hr i h))

/-- The literal selected tensor Hom, actual right word, given middle E
and actual left word, before changing the endpoint's weight presentation. -/
def dotRawHom {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR (ReservoirWord.weight D ΛR cL) :=
  (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR pR hr ≫ (W).E i h) ≫
    ReservoirWord.word (W) ΛR pL hl

/-- The actual two-whiskered factor dot of the two reservoir-word charts. -/
def dotRaw {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    End (dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h) :=
  (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR pR hr ◁ (W).dot i h) ▷
    ReservoirWord.word (W) ΛR pL hl

private theorem dotFunctor_heq {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    HEq (dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h)
      (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ((r.map (fun a => a.l.2)).reverse) ≫
        (W).E i (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i) ≫
        TensorHomContexts.context D Tw cutoff L ΛR
          (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
          ((l.map (fun a => a.l.2)).reverse)) := by
  have hm := postE_heq D Sc m cutoff L ΛP ΛR i (TensorReservoirWords.path_weight D ΛR pR hr)
    (dotMidWeight D ΛR pR hr i h) h (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i)
    (TensorReservoirWords.pathHom_heq D Tw m cutoff L ΛP ΛR pR hr)
  have hk := (ReservoirContexts.word_heq D Tw cutoff L ΛR pL hl).trans
    (context_input_heq D Sc cutoff L ΛR (dotMidWeight D ΛR pR hr i h) ((l.map (fun a => a.l.2)).reverse))
  exact compose_heq D Sc m cutoff L ΛP ΛR (dotMidWeight D ΛR pR hr i h)
    (dotEndWeight D ΛR pL hl pR hr i h) hm hk

private theorem dotCell_heq {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    HEq (dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h)
      ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ((r.map (fun a => a.l.2)).reverse) ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i)) ▷
        TensorHomContexts.context D Tw cutoff L ΛR
          (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
          ((l.map (fun a => a.l.2)).reverse)) := by
  have hp := TensorReservoirWords.pathHom_heq D Tw m cutoff L ΛP ΛR pR hr
  have hx := TensorReservoirWords.path_weight D ΛR pR hr
  have hy := dotMidWeight D ΛR pR hr i h
  have hm := postE_heq D Sc m cutoff L ΛP ΛR i hx hy h
    (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i) hp
  have ha := postDot_heq D Sc m cutoff L ΛP ΛR i hx hy h
    (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i) hp
  have hk := (ReservoirContexts.word_heq D Tw cutoff L ΛR pL hl).trans
    (context_input_heq D Sc cutoff L ΛR hy ((l.map (fun a => a.l.2)).reverse))
  exact whisker_heq D Sc m cutoff L ΛP ΛR hy (dotEndWeight D ΛR pL hl pR hr i h) hm hm hk ha

/-- The same actual two-word dot Hom at its proved original-weight endpoint. -/
def dotHomAt {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :=
  atHom D Sc m cutoff L ΛP ΛR (dotEndWeight D ΛR pL hl pR hr i h)
    (dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h)

/-- The actual raw factor dot transported only through the proved endpoint weight. -/
def dotAt {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    End (dotHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h) :=
  atCell D Sc m cutoff L ΛP ΛR (dotEndWeight D ΛR pL hl pR hr i h)
    (dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h)

/-- The actual two-word Hom has the precise chosen tensor-context functor. -/
theorem dotHomAt_eq {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    dotHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h =
      TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ((r.map (fun a => a.l.2)).reverse) ≫
        (W).E i (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i) ≫
        TensorHomContexts.context D Tw cutoff L ΛR
          (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
          ((l.map (fun a => a.l.2)).reverse) :=
  eq_of_heq ((atHom_heq D Sc m cutoff L ΛP ΛR _ _).trans
    (dotFunctor_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i h))

/-- The literal actual-word dot cell is the chosen contextual dot through
the derived whole-functor chart; no generator-comparison premise is supplied. -/
theorem dot_square {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM) :
    dotAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h ≫
        eqToHom (dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h) =
      eqToHom (dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h) ≫
        ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ((r.map (fun a => a.l.2)).reverse) ◁
          (W).dot i (PowerWordWeight.wordWeight_append D ΛR ((r.map (fun a => a.l.2)).reverse) i)) ▷
          TensorHomContexts.context D Tw cutoff L ΛR
            (PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse ++ [i]))
            ((l.map (fun a => a.l.2)).reverse)) := by
  exact heq_square _ _ _ _ ((atCell_heq D Sc m cutoff L ΛP ΛR _ _).trans
    (dotCell_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i h))

section DotClass
variable {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
  (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
  (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)
local notation "ν" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) r))
local notation "η" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) l))

/-- The actual two-word dot entry has its original affine layer quotient
class on every source vector. Only its input class is prescribed. -/
theorem dot_class_square (i : I)
    (h : ReservoirWord.weight D ΛR cR + D.α i = ReservoirWord.weight D ΛR cM)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (f : G ⟶ dotHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h)
    (s : List I) (β : WeightBlocks D ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj (WeightTensorVacuum.regularProbe D Tw m ΛP)) β).obj
      (⟨⟨s.reverse⟩,hs⟩ : ContentCategory D Tw cutoff N β.1))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord ν η (.dot i)))
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.dot i))
      (TensorLayerClasses.dotVector D Sc cutoff L m ΛP ΛR ν η i G
        (f ≫ eqToHom (dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h)) s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.dot i))).mkQ y) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.dot i))
      (TensorLayerClasses.dotVector D Sc cutoff L m ΛP ΛR ν η i G
        ((f ≫ dotAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h) ≫
          eqToHom (dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h)) s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.dot i))).mkQ
        (y ≫ sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc (List.reverse η) (.dot i) (List.reverse ν))) := by
  have he : (f ≫ dotAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h) ≫
      eqToHom (dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h) =
      (f ≫ eqToHom (dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h)) ≫
        ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
          (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)) ▷
          TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η) := by
    rw [Category.assoc, dot_square]
    simp only [Category.assoc]
  rw [he]
  exact TensorLayerClasses.dot_class_square D Sc cutoff L m ΛP ΛR ν η i G
    (f ≫ eqToHom (dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h)) s β hs z y hy
end DotClass

omit [Fintype I] in
private theorem sourceEdge {r : List (SKM.Col I X)} {cR : I →₀ ℕ}
    (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true) (i : I) {x : X}
    (h : ReservoirWord.weight D ΛR cR + D.α i = x) :
    PowerWordWeight.wordWeight D ΛR ((r.map (fun a => a.l.2)).reverse) + D.α i = x :=
  (congrArg (fun x => x + D.α i) (TensorReservoirWords.path_weight D ΛR pR hr)).symm.trans h

section Cross
variable {l r : List (SKM.Col I X)} {cL cM cR : I →₀ ℕ}
  (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
  (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)
local notation "ν" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) r))
local notation "η" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) l))
local notation "xR" => ReservoirWord.weight D ΛR cR
local notation "xM" => ReservoirWord.weight D ΛR cM

/-- The actual selected right word, original-vertex pair of E functors,
and actual outer word of a crossing source. -/
def crossRawHom (i j : I) {xj : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM) :
    probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR (ReservoirWord.weight D ΛR cL) :=
  (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR pR hr ≫ (W).E j h₁ ≫ (W).E i h₂) ≫
    ReservoirWord.word (W) ΛR pL hl

/-- The prescribed factor crossing, with both actual reservoir words.
The given original weight vertices and pair associator are unchanged. -/
def crossRaw (i j : I) {xj xi : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM)
    (h₃ : xR + D.α i = xi) (h₄ : xi + D.α j = xM) :
    crossRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ ⟶
      crossRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr j i h₃ h₄ :=
  (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR pR hr ◁ (W).cross i j h₁ h₂ h₃ h₄) ▷
    ReservoirWord.word (W) ΛR pL hl

private theorem crossFunctor_heq (i j : I) {xj : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM) :
    HEq (crossRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂)
      (TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
        (W).E j (sourceEdge D ΛR pR hr j h₁) ≫ (W).E i h₂ ≫
        TensorHomContexts.context D Tw cutoff L ΛR xM η) := by
  have hm := pairFunctor_heq D Sc m cutoff L ΛP ΛR i j (TensorReservoirWords.path_weight D ΛR pR hr)
    h₁ h₂ (sourceEdge D ΛR pR hr j h₁) (TensorReservoirWords.pathHom_heq D Tw m cutoff L ΛP ΛR pR hr)
  exact compose_heq D Sc m cutoff L ΛP ΛR rfl (ReservoirContexts.word_weight D ΛR pL hl) hm
    (ReservoirContexts.word_heq D Tw cutoff L ΛR pL hl)

private theorem crossCell_heq (i j : I) {xj xi : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM)
    (h₃ : xR + D.α i = xi) (h₄ : xi + D.α j = xM) :
    HEq (crossRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ h₃ h₄)
      ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
        (W).cross i j (sourceEdge D ΛR pR hr j h₁) h₂ (sourceEdge D ΛR pR hr i h₃) h₄) ▷
        TensorHomContexts.context D Tw cutoff L ΛR xM η) := by
  have hp := TensorReservoirWords.pathHom_heq D Tw m cutoff L ΛP ΛR pR hr
  have hx := TensorReservoirWords.path_weight D ΛR pR hr
  have hs := pairFunctor_heq D Sc m cutoff L ΛP ΛR i j hx h₁ h₂ (sourceEdge D ΛR pR hr j h₁) hp
  have ht := pairFunctor_heq D Sc m cutoff L ΛP ΛR j i hx h₃ h₄ (sourceEdge D ΛR pR hr i h₃) hp
  have ha := postCross_heq D Sc m cutoff L ΛP ΛR i j hx h₁ h₂ h₃ h₄
    (sourceEdge D ΛR pR hr j h₁) (sourceEdge D ΛR pR hr i h₃) hp
  exact whisker_heq D Sc m cutoff L ΛP ΛR rfl (ReservoirContexts.word_weight D ΛR pL hl)
    hs ht (ReservoirContexts.word_heq D Tw cutoff L ΛR pL hl) ha

/-- The actual crossing source Hom at its proved outer-context endpoint. -/
def crossHomAt (i j : I) {xj : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM) :=
  atHom D Sc m cutoff L ΛP ΛR (ReservoirContexts.word_weight D ΛR pL hl)
    (crossRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂)

/-- The same actual crossing cell through only the proved endpoint transport. -/
def crossAt (i j : I) {xj xi : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM)
    (h₃ : xR + D.α i = xi) (h₄ : xi + D.α j = xM) :
    crossHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ ⟶
      crossHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr j i h₃ h₄ :=
  atCell D Sc m cutoff L ΛP ΛR (ReservoirContexts.word_weight D ΛR pL hl)
    (crossRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ h₃ h₄)

/-- The actual two-word pair Hom has the exact chosen tensor-context functor. -/
theorem crossHomAt_eq (i j : I) {xj : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM) :
    crossHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ =
      TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
        (W).E j (sourceEdge D ΛR pR hr j h₁) ≫ (W).E i h₂ ≫
        TensorHomContexts.context D Tw cutoff L ΛR xM η :=
  eq_of_heq ((atHom_heq D Sc m cutoff L ΛP ΛR _ _).trans
    (crossFunctor_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂))

/-- The literal actual-word crossing and its pair associator give the
chosen tensor-context crossing through the derived functor charts. -/
theorem cross_square (i j : I) {xj xi : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM)
    (h₃ : xR + D.α i = xi) (h₄ : xi + D.α j = xM) :
    crossAt D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ h₃ h₄ ≫
        eqToHom (crossHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr j i h₃ h₄) =
      eqToHom (crossHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂) ≫
        ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
          (W).cross i j (sourceEdge D ΛR pR hr j h₁) h₂ (sourceEdge D ΛR pR hr i h₃) h₄) ▷
          TensorHomContexts.context D Tw cutoff L ΛR xM η) := by
  exact heq_square _ _ _ _ ((atCell_heq D Sc m cutoff L ΛP ΛR _ _).trans
    (crossCell_heq D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ h₃ h₄))
/-- The actual two-word crossing entry has its signed original affine
layer quotient class on every source vector, with only an input-class premise. -/
theorem cross_class_square (i j : I) {xj xi : X} (h₁ : xR + D.α j = xj) (h₂ : xj + D.α i = xM)
    (h₃ : xR + D.α i = xi) (h₄ : xi + D.α j = xM)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D xM η))
    (f : G ⟶ crossHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂)
    (s : List I) (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D xM η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj (WeightTensorVacuum.regularProbe D Tw m ΛP)) β).obj
      (⟨⟨s.reverse⟩,hs⟩ : ContentCategory D Tw cutoff N β.1))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord ν η (.cross i j)))
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.cross i j))
      (TensorLayerClasses.crossVector D Sc cutoff L m ΛP ΛR ν η i j (sourceEdge D ΛR pR hr j h₁) h₂ G
        (f ≫ eqToHom (crossHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂)) s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.cross i j))).mkQ y) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.cross i j))
      (TensorLayerClasses.crossVector D Sc cutoff L m ΛP ΛR ν η j i (sourceEdge D ΛR pR hr i h₃) h₄ G
        ((f ≫ crossAt D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ h₃ h₄) ≫
          eqToHom (crossHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr j i h₃ h₄)) s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.cross i j))).mkQ
        (y ≫ sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc (List.reverse η) (.cross i j) (List.reverse ν))) := by
  have he : (f ≫ crossAt D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂ h₃ h₄) ≫
      eqToHom (crossHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr j i h₃ h₄) =
      (f ≫ eqToHom (crossHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂)) ≫
        ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
          (W).cross i j (sourceEdge D ΛR pR hr j h₁) h₂ (sourceEdge D ΛR pR hr i h₃) h₄) ▷
          TensorHomContexts.context D Tw cutoff L ΛR xM η) := by
    rw [Category.assoc, cross_square]
    simp only [Category.assoc]
  rw [he]
  exact TensorLayerClasses.cross_class_square D Sc cutoff L m ΛP ΛR ν η i j
    (sourceEdge D ΛR pR hr j h₁) h₂ (sourceEdge D ΛR pR hr i h₃) h₄ G
    (f ≫ eqToHom (crossHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i j h₁ h₂)) s β hs z y hy

end Cross

end OddMath.QuiverHecke.ELV.ReservoirLayerCells
end

end

section

/-! # The prescribed post-Hom unit at a reservoir content block

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
evaluate the actual content-shifted post-Hom dotted unit, retaining its
output shift comparison and selected whole-weight successor chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor CyclotomicAction
universe u
local instance reservoirPostUnitHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

/-- The chosen dotted post-unit evaluates to the literal whole-weight
unit/dot word, after its prescribed adjacent-shift comparison. -/
theorem postCup_total
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : X → PiSCat.{u,u,u+1} k)
    (W : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) (β : I →₀ ℕ) (muP : X) {a b : X} (h : a + D.α i = b)
    (r : ℕ) (Z : SKM.homWeightSector T (W).obj muP a) (N : T (-muP)) :
    (SKM.homContentPostCup T W i β muP h r Z).total N ≫
      (SKM.homContentPostTargetIso T W i β muP h Z).hom.total N =
    ((W.adj i h).unit ≫ SKM.rouquierPower (W.dot i h) r ▷ W.F i h).total (Z.obj N) := by
  have hh := congrArg (fun f => f.total N)
    (SKM.homContentPostCup_coordinates T W i β muP h r Z)
  simp only [PiSCat.rightUnitor_inv, PiSCat.associator_inv, Category.id_comp] at hh
  erw [Superfunctor.comp_total, Superfunctor.comp_total] at hh
  erw [Superfunctor.comp_total]
  convert hh using 1; rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ : X) (hc : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (T : X → PiSCat.{u,u,u+1} k) (i : I) (β : I →₀ ℕ) (muP : X)
  {a b : X} (h : a + D.α i = b)
local notation "W" => elvRouquierFamily D Sc cutoff bound Λ hc

/-- The exact post-Hom cup at every reservoir output block is the given
stored-content unit column. The source Hom object and probe module are
arbitrary; no unit compatibility premise is supplied. -/
theorem reservoirPostCup_block (r : ℕ) (Z : SKM.homWeightSector T (W).obj muP a)
    (N : T (-muP)) (δ : WeightBlocks D Λ a) :
    ((SKM.homContentPostCup T W i β muP h r Z).total N) δ ≫
      ((SKM.homContentPostTargetIso T W i β muP h Z).hom.total N) δ ≫
        eqToHom (elvWeightFollowing_obj D Sc cutoff bound i Λ h δ (Z.obj N)) =
    unitDotColumn (elvBlockAppend D Sc cutoff bound i Λ h δ)
      (elvBlockGridDot_supernatural D Sc cutoff bound i Λ h δ) ((Z.obj N) δ) r := by
  have hp := congrFun (postCup_total T W i β muP h r Z N) δ
  change ((SKM.homContentPostCup T W i β muP h r Z).total N) δ ≫
      ((SKM.homContentPostTargetIso T W i β muP h Z).hom.total N) δ =
    ((((W).adj i h).unit ≫ SKM.rouquierPower ((W).dot i h) r ▷ (W).F i h).total (Z.obj N)) δ at hp
  have ht := congrArg (fun f => f ≫
    eqToHom (elvWeightFollowing_obj D Sc cutoff bound i Λ h δ (Z.obj N))) hp
  simpa only [Category.assoc] using
    ht.trans (elvWeightUnitPower_following_coordinates D Sc cutoff bound Λ i h (Z.obj N) δ r)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The chosen reservoir post-unit in canonical append coordinates

SwappedActionAssembly F2: remove the stored successor content only by
its actual content equality, retaining the raw unit and every dot power.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicAction
universe u
local instance postStandardHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The ordinary canonical append has exactly the given last-dot family. -/
theorem canonicalAppendDot_supernatural (β : Multiset I) (i : I) :
    IsSupernatural k (D.parity i)
      (contentAppendToComponent D Sc cutoff bound (β := β) rfl rfl (dotE D Sc [i] 0)) :=
  contentAppendTo_supernatural D Sc cutoff bound rfl rfl (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The stored upper-loop object agrees with canonical append/restrict.
No equivalence is chosen beyond the specified successor-content equality. -/
theorem storedAppendUpper_obj (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff bound β) :
    (restriction (contentAppendTo D Sc cutoff bound β [i] γ hγ)).obj
        ((induction (contentAppendTo D Sc cutoff bound β [i] γ hγ)).obj M) =
      (restriction (contentAppend D Sc cutoff bound β [i])).obj
        ((induction (contentAppend D Sc cutoff bound β [i])).obj M) := by
  subst γ
  rfl

/-- Every stored dotted unit column becomes the native dotted unit under
this literal target chart. -/
theorem storedAppendUnit_column (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff bound β) (r : ℕ) :
    unitDotColumn (contentAppendTo D Sc cutoff bound β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M r ≫
      eqToHom (storedAppendUpper_obj D Sc cutoff bound β i γ hγ M) =
    (adjunction (contentAppend D Sc cutoff bound β [i])).unit.app M ≫
      restrictedDotEnd (contentAppend D Sc cutoff bound β [i])
        (canonicalAppendDot_supernatural D Sc cutoff bound β i) M ^ r := by
  subst γ
  simp only [eqToHom_refl, Category.comp_id]
  convert unitDotColumn_eq_restrictedDotEnd (contentAppend D Sc cutoff bound β [i])
    (canonicalAppendDot_supernatural D Sc cutoff bound β i) M r using 1; rfl

variable (Λ : X) (hc : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (T : X → PiSCat.{u,u,u+1} k) (i : I) (β : I →₀ ℕ) (muP : X)
  {a b : X} (h : a + D.α i = b)
local notation "W" => elvRouquierFamily D Sc cutoff bound Λ hc

/-- The actual content-shifted post-Hom cup is the native reservoir unit
and raw restricted-dot power at every source block. -/
theorem reservoirPostCup_canonical (r : ℕ) (Z : SKM.homWeightSector T (W).obj muP a)
    (N : T (-muP)) (δ : WeightBlocks D Λ a) :
    ((SKM.homContentPostCup T W i β muP h r Z).total N) δ ≫
      ((SKM.homContentPostTargetIso T W i β muP h Z).hom.total N) δ ≫
      eqToHom (elvWeightFollowing_obj D Sc cutoff bound i Λ h δ (Z.obj N)) ≫
      eqToHom (storedAppendUpper_obj D Sc cutoff bound δ.1 i
        (blockSucc D Λ i h δ).1 (elvBlockSucc_content_eq D i Λ h δ) ((Z.obj N) δ)) =
    (adjunction (contentAppend D Sc cutoff bound δ.1 [i])).unit.app ((Z.obj N) δ) ≫
      restrictedDotEnd (contentAppend D Sc cutoff bound δ.1 [i])
        (canonicalAppendDot_supernatural D Sc cutoff bound δ.1 i) ((Z.obj N) δ) ^ r := by
  rw [← storedAppendUnit_column D Sc cutoff bound δ.1 i
    (blockSucc D Λ i h δ).1 (elvBlockSucc_content_eq D i Λ h δ) ((Z.obj N) δ) r]
  rw [← reservoirPostCup_block D Sc cutoff bound Λ hc T i β muP h r Z N δ]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Degrees of the chosen reservoir closures over a graded base ring

BE (1.13)–(1.14), closure dependency G8, over a commutative `K`-algebra `R` graded by `𝒜`.
The represented unit and cap closure coefficients of the weighted content kernels lie in degree
`2 dᵢ (r + s + 1)` of the truncated quotient over `K`
(`weightedContentUnitClosureCoefficient_degreeOver`,
`weightedContentCapClosureCoefficient_degreeOver`), and so do the reconstructed source
coefficients of the chosen positive and negative reservoir closures
(`ReservoirClosures.positiveCoefficient_mem_degreeOver`,
`ReservoirClosures.negativeCoefficient_mem_degreeOver`).

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.WeightedKernel` and
`OddMath.QuiverHecke.CyclotomicAction.ReservoirClosure`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section
set_option backward.dsimp.instances true

open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams

namespace OddMath.QuiverHecke.ELV

open CyclotomicAction BalancedInduction CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- Identities have degree zero in the old quotient, over a graded base. -/
theorem oldId_mem_degreeOver (v : OldCategory D Sc cutoff) :
    𝟙 v ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v v 0 := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  exact id_mem_degree (R := K) v

/-- Truncation preserves degrees, over a graded base. -/
theorem truncateOld_mem_degreeOver {v w : OldCategory D Sc cutoff} {n : ℤ} {f : v ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    (truncateOld D Sc cutoff N v.word w.word f :
        (oldTruncateFunctor D Sc cutoff N).obj v ⟶ (oldTruncateFunctor D Sc cutoff N).obj w) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
        ((oldTruncateFunctor D Sc cutoff N).obj v) ((oldTruncateFunctor D Sc cutoff N).obj w)
        n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ha

/-- Parity projections preserve degrees of the truncated quotient, over a graded base. -/
theorem truncatedProj_mem_degreeOver {v w : TruncatedCategory D Sc cutoff N} {n : ℤ}
    (p : ZMod 2) {f : v ⟶ w} (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n) :
    proj R p f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  have hf' : f ∈ degree (R := K) v w n := hf
  rw [← Supercategory.proj_restrictScalars K R (TruncatedCategory D Sc cutoff N) p f]
  exact proj_mem_degree (R := K) p hf'

/-- Source degree follows from the total action on every represented identity, over a graded
base. -/
theorem ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation (β : Multiset I)
    (η : ModuleCentre.Centre D Sc cutoff N β) (d : ℤ)
    (h : ∀ w : ContentCategory D Sc cutoff N β,
      (η.total (contentRepresentable D Sc cutoff N β w)).total w (𝟙 w) ∈
        truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj d) :
    ModuleCentre.reconstruct D Sc cutoff N β η ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N β d := by
  intro p w
  rw [ModuleCentre.reconstruct_app_eq_proj_total, ModuleCentre.reconstruct_total_evaluate]
  exact truncatedProj_mem_degreeOver D sy 𝒜 Sc hP cutoff N p (h w)

variable (i : I)

/-- The represented unit closure coefficient has the positive source degree, over a graded
base. -/
theorem weightedContentUnitClosureCoefficient_degreeOver (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) :
    weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  refine weightedContentUnitClosureCoefficient_induction D Sc cutoff N i
    (P := fun β w r s f => f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
      (2 * sy.d i * (r + s + 1 : ℕ))) ?_ β hh w r s
  intro l hh r s
  have h := positiveKernelClosure_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨l⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

/-- The represented cap closure coefficient has the same source degree, over a graded base. -/
theorem weightedContentCapClosureCoefficient_degreeOver (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) :
    weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  refine weightedContentCapClosureCoefficient_induction D Sc cutoff N i
    (P := fun β w r s f => f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
      (2 * sy.d i * (r + s + 1 : ℕ))) ?_ β hh w r s
  intro l hh r s
  have h := negativeKernelClosure_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨l⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

namespace ReservoirClosures

variable (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (γ : WeightBlocks D Λ x₁)

/-- The represented positive-weight value has the positive closure degree, over a graded
base. -/
theorem positiveRepresentedValue_degreeOver (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) :
    positiveRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r s w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold positiveRepresentedValue
  exact weightedContentCapClosureCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1 _ w r s

/-- The represented negative-weight value has the same degree, over a graded base. -/
theorem negativeRepresentedValue_degreeOver (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) :
    negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r s w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold negativeRepresentedValue
  exact weightedContentUnitClosureCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1 _ w r s

attribute [local irreducible] positive negative positiveContent negativeContent
  positiveRepresentedValue negativeRepresentedValue

/-- The reconstructed coefficient of the chosen positive closure has its strictly positive
source degree on every output block, over a graded base. -/
theorem positiveCoefficient_mem_degreeOver (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s) ∈ _
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  by_cases hγ : ∃ β₁, blockSucc D Λ i h₁ β₁ = γ
  · rcases hγ with ⟨β₁, rfl⟩
    have he := positiveContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh r s
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
    change ((positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂
      (blockSucc D Λ i h₁ β₁) hh r s).total
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
    erw [he]
    change (𝟙 w ≫ positiveRepresentedValue D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) hh r s w) ∈ _
    rw [Category.id_comp]
    exact positiveRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff
      (blockSucc D Λ i h₁ β₁) hh r s w
  · rw [positiveContent_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s,
      supernatural_zero_total, SVec.zero_apply]
    exact zero_mem _

/-- The reconstructed coefficient of the chosen negative closure has the same strictly positive
source degree, over a graded base. -/
theorem negativeCoefficient_mem_degreeOver (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s) ∈ _
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  by_cases hγ : ∃ β₁, blockSucc D Λ i h₁ β₁ = γ
  · rcases hγ with ⟨β₁, rfl⟩
    have he := negativeContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh r s
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
    change ((negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂
      (blockSucc D Λ i h₁ β₁) hh r s).total
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
    erw [he]
    change (𝟙 w ≫ negativeRepresentedValue D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) hh r s w) ∈ _
    rw [Category.id_comp]
    exact negativeRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff
      (blockSucc D Λ i h₁ β₁) hh r s w
  · rw [negativeContent_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s,
      supernatural_zero_total, SVec.zero_apply]
    exact zero_mem _

end ReservoirClosures

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Degrees of the chosen reservoir boundary contractions over a graded base ring

SwappedHomInversion §4 (7), over a commutative `K`-algebra `R` graded by `𝒜`. The window
contractions of the finite kernel inverses have the difference degrees `2 dᵢ (n - m)` and
`2 dᵢ (m - n)` (`positiveKernelBoundary_degreeOver`, `negativeKernelBoundary_degreeOver`), and
so do their represented content coefficients and the reconstructed source coefficients of the
chosen reservoir boundaries (`ReservoirBoundaries.positiveCoefficient_mem_degreeOver`,
`ReservoirBoundaries.negativeCoefficient_mem_degreeOver`).

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.KernelEntryDegrees`,
`OddMath.QuiverHecke.CyclotomicAction.WeightedKernel` and
`OddMath.QuiverHecke.CyclotomicAction.ReservoirClosure`.
-/

noncomputable section
set_option backward.dsimp.instances true

open CategoryTheory Opposite StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams
open OddMath.IntegerMatrix

namespace OddMath.QuiverHecke.ELV

open CyclotomicAction BalancedInduction CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

namespace CyclotomicCrossingTensor

/-- The positive inverse window row has degree `-2 dᵢ m`, over a graded base. -/
theorem positiveKernelWindowInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) q) :
    positiveKernelWindowInverse D Sc cutoff i v t hh m y ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (q - 2 * sy.d i * m.val) := by
  exact (Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh hy) (some m)

/-- Inserting window column `m` gives inverse degree `-2 dᵢ m`, over a graded base. -/
theorem negativeKernelWindowInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t q) :
    negativeKernelWindowInverse D Sc cutoff i v t hh m y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (q - 2 * sy.d i * m.val) := by
  classical
  change (negativeKernelEquiv D Sc cutoff i v t hh).symm
    (Pi.single (some m) y) ∈ _
  apply negativeKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
  apply (Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  by_cases ha : a = some m
  · subst a
    simp only [Pi.single_eq_same]
    change y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t
      (q - 2 * sy.d i * m.val + 2 * sy.d i * m.val)
    simpa only [sub_add_cancel] using hy
  · rw [Pi.single_eq_of_ne ha]
    exact zero_mem _

/-- All positive contractions have the difference degree, over a graded base. -/
theorem positiveKernelBoundary_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (n : ℕ) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t q) :
    positiveKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (q + 2 * sy.d i * ((n : ℤ) - m.val)) := by
  have h := positiveKernelWindowInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh m
    (unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t n hy)
  have he : q + 2 * sy.d i * n - 2 * sy.d i * m.val =
      q + 2 * sy.d i * ((n : ℤ) - m.val) := by ring
  simpa only [positiveKernelBoundary, LinearMap.comp_apply, he] using h

/-- All negative contractions have the difference degree, over a graded base. -/
theorem negativeKernelBoundary_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (n : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t q) :
    negativeKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (q + 2 * sy.d i * ((m : ℤ) - n.val)) := by
  have h := capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t m
    (negativeKernelWindowInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh n hy)
  have he : q - 2 * sy.d i * n.val + 2 * sy.d i * m =
      q + 2 * sy.d i * ((m : ℤ) - n.val) := by ring
  simpa only [negativeKernelBoundary, LinearMap.comp_apply, he] using h

end CyclotomicCrossingTensor

variable (i : I)

/-- The represented unit boundary coefficient has the difference degree, over a graded base. -/
theorem weightedContentUnitBoundaryCoefficient_degreeOver (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ) :
    weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((s : ℤ) - r.val)) := by
  refine weightedContentUnitBoundaryCoefficient_induction D Sc cutoff N i
    (P := fun β w r s f => f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
      (2 * sy.d i * ((s : ℤ) - r.val))) ?_ β hh w r s
  intro l hh r s
  have h := positiveKernelBoundary_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨l⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

/-- The represented cap boundary coefficient has the difference degree, over a graded base. -/
theorem weightedContentCapBoundaryCoefficient_degreeOver (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r : ℕ) (s : Fin (contentCapCount D cutoff i β)) :
    weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((r : ℤ) - s.val)) := by
  refine weightedContentCapBoundaryCoefficient_induction D Sc cutoff N i
    (P := fun β w r s f => f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
      (2 * sy.d i * ((r : ℤ) - s.val))) ?_ β hh w r s
  intro l hh r s
  have h := negativeKernelBoundary_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨l⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

namespace ReservoirBoundaries

variable (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (γ : WeightBlocks D Λ x₁)

/-- The represented positive boundary has the difference degree, over a graded base. -/
theorem positiveRepresentedValue_degreeOver (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) :
    positiveRepresentedValue D Sc cutoff N Λ hcutoff i γ hh j r hj w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((r : ℤ) - j)) := by
  unfold positiveRepresentedValue
  exact weightedContentCapBoundaryCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1
    _ w r
      ⟨j, by simpa only [contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj⟩

/-- The represented negative boundary has the same difference degree, over a graded base. -/
theorem negativeRepresentedValue_degreeOver (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) :
    negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((r : ℤ) - j)) := by
  unfold negativeRepresentedValue
  exact weightedContentUnitBoundaryCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1
    _ w
      ⟨j, by simpa only [contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj⟩ r

attribute [local irreducible] positive negative positiveContent negativeContent
  positiveRepresentedValue negativeRepresentedValue

/-- The reconstructed source coefficient of the chosen positive boundary has the difference
degree, over a graded base. -/
theorem positiveCoefficient_mem_degreeOver (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) :
    positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh j r ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1 (2 * sy.d i * ((r : ℤ) - j)) := by
  have hpos : 0 < D.h i x₁ := by omega
  obtain ⟨β₁, rfl⟩ := elvWeightPredecessor_of_positive_height D cutoff i Λ h₁ (hcutoff i) hpos γ
  change ModuleCentre.reconstruct D Sc cutoff N (blockSucc D Λ i h₁ β₁).1
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ (blockSucc D Λ i h₁ β₁) hh j r) ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N (blockSucc D Λ i h₁ β₁).1
        (2 * sy.d i * ((r : ℤ) - j))
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  have he := positiveContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh j r hj
    (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
  change ((positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂
    (blockSucc D Λ i h₁ β₁) hh j r).total
    (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
  erw [he]
  change (𝟙 w ≫ positiveRepresentedValue D Sc cutoff N Λ hcutoff i
    (blockSucc D Λ i h₁ β₁) hh j r hj w) ∈ _
  rw [Category.id_comp]
  exact positiveRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff
    (blockSucc D Λ i h₁ β₁) hh j r hj w

/-- The reconstructed source coefficient of the chosen negative boundary has the difference
degree, including blocks without a predecessor, over a graded base. -/
theorem negativeCoefficient_mem_degreeOver (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1 (2 * sy.d i * ((r : ℤ) - j)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j) ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1 (2 * sy.d i * ((r : ℤ) - j))
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  have he := negativeContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j hj
    (contentRepresentable D Sc cutoff N γ.1 w) w (𝟙 w)
  change ((negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j).total
    (contentRepresentable D Sc cutoff N γ.1 w)).total w (𝟙 w) = _ at he
  erw [he]
  change (𝟙 w ≫ negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w) ∈ _
  rw [Category.id_comp]
  exact negativeRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff γ hh r j hj w

end ReservoirBoundaries

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The chosen reservoir contractions in the content coefficient ideal over a graded base

SwappedHomInversion §4, condition (J), over a commutative `K`-algebra `R` graded by `𝒜` in
degrees `0, …, b`. The chosen principal closures and the off-window finite boundaries act
through source coefficients of strictly positive degree in the truncated quotient over `K`, so
their post-whiskering actions, with arbitrary morphisms on either side and after native
Hom-sector charts, lie in level one of the jointly nilpotent coefficient ideal
`ELV.contentModuleCoefficientIdealOver`
(`ReservoirClosures.positiveDirectClosure_evaluate_memOver`,
`ReservoirClosures.negativeDirectClosure_evaluate_memOver`,
`ReservoirBoundaries.positiveDirectBoundary_evaluate_memOver`,
`ReservoirBoundaries.negativeDirectBoundary_evaluate_memOver`).

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.ReservoirClosure` and
`OddMath.QuiverHecke.CyclotomicAction.ReservoirClosure`.
-/

noncomputable section

open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath.Diagrams

namespace OddMath.QuiverHecke.ELV

open SwappedAssembly CyclotomicAction

universe u

local instance reservoirIdealOverHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₁)

namespace ReservoirClosures

/-- The positive closure belongs to the source coefficient grading over a graded base. -/
theorem positiveContent_mem_coeffGradingOver (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) :=
  ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    positiveCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh r s,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

/-- The negative closure has the same coefficient degree over a graded base. -/
theorem negativeContent_mem_coeffGradingOver (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) :=
  ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    negativeCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh r s,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

variable [Finite I] (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (T : PiSCat R)

/-- Arbitrary Hom-sector morphisms may surround the positive closure, over a graded base. -/
theorem positiveContent_sandwich_memOver (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact positiveContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh r s

/-- Arbitrary Hom-sector morphisms may surround the negative closure, over a graded base. -/
theorem negativeContent_sandwich_memOver (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact negativeContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh r s

/-- The whole-weight positive closure action, projected to one output content and surrounded
by arbitrary transformations, lies in the coefficient ideal over a graded base. -/
theorem positiveAction_evaluate_memOver (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    r s (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

/-- The whole-weight negative closure action, projected to one output content and surrounded
by arbitrary transformations, lies in the coefficient ideal over a graded base. -/
theorem negativeAction_evaluate_memOver (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    r s (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The native positive principal contraction, after output projection and arbitrary
surrounding maps, lies in the coefficient ideal over a graded base. -/
theorem positiveDirectClosure_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [positive, Category.assoc] using
    positiveAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh r s a c

/-- The native negative principal contraction, after output projection and arbitrary
surrounding maps, lies in the coefficient ideal over a graded base. -/
theorem negativeDirectClosure_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [negative, Category.assoc] using
    negativeAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh r s a c

end ReservoirClosures

namespace ReservoirBoundaries

/-- The positive finite-window boundary has its difference degree over a graded base. -/
theorem positiveContent_mem_coeffGradingOver (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * ((r : ℤ) - j)) :=
  ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r,
    positiveCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh j r hj,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

/-- The negative finite-window boundary has its difference degree over a graded base. -/
theorem negativeContent_mem_coeffGradingOver (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * ((r : ℤ) - j)) :=
  ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j,
    negativeCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh r j hj,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

variable [Finite I] (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (T : PiSCat R)

/-- Arbitrary transformations can surround the positive off-window coefficient, over a graded
base. -/
theorem positiveContent_sandwich_memOver (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact positiveContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh j r
      hj

/-- Arbitrary transformations can surround the negative off-window coefficient, over a graded
base. -/
theorem negativeContent_sandwich_memOver (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact negativeContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh j r
      hj

/-- The projected positive off-window action lies in the coefficient ideal over a graded
base. -/
theorem positiveAction_evaluate_memOver (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    j r hj hjr (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

/-- The projected negative off-window action lies in the coefficient ideal over a graded
base. -/
theorem negativeAction_evaluate_memOver (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    j r hj hjr (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The native positive off-window contraction has the same ideal membership over a graded
base. -/
theorem positiveDirectBoundary_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (j r : ℕ) (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ((SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).g' j ≫
          SKM.homContentPostCap TF W i betaP muP h₁ r Z) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_boundary TF W i betaP muP h₁ h₂ hh Z j r]
  simpa only [positive] using
    positiveAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh j r hj hjr a c

/-- The native negative off-window contraction has the same ideal membership over a graded
base. -/
theorem negativeDirectBoundary_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (j r : ℕ) (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).g' j) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_boundary TF W i betaP muP h₁ h₂ hh Z r j]
  simpa only [negative] using
    negativeAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh j r hj hjr a c

end ReservoirBoundaries

end OddMath.QuiverHecke.ELV
end

end
