import OddMath.QuiverHecke.CyclotomicAction.ELVTensorLayerClasses
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorReservoirWords
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirContexts

/-! # Actual reservoir-word cells in tensor quotient coordinates

SwappedVacuumCoordinates §§2–7: retain the selected tensor Hom, both
actual reservoir words and the given middle generator at its original
weight vertices, then attach its whole cell to the chosen tensor chart.
No complete swapped factor, boundary-support or faithfulness premise is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirLayerCells
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

end OddMath.QuiverHecke.ELVOld.ReservoirLayerCells
