import OddMath.SKM.RouquierHomDistinctMixedPre

/-!
# The distinct-colour pre/pre mate of the swapped Hom action

Formalizes `docs/Nondegeneracy/SwappedDistinctPreMate.md`, the pre/pre entry
(A9) of `SwappedActionAssembly.md` §5. A factor 2-cell `T : E_d ≫ E_c ⟶ E_b ≫ E_a`
induces, by precomposition, a natural map `L_d L_c ⟶ L_b L_a` of Hom functors.
Its mate along the precomposition adjunctions `L_d ⊣ R_d`, `L_a ⊣ R_a` of two
shifted left adjunctions `F_d ⊣ E_d`, `F_a ⊣ E_a` of parities `σ_d`, `σ_a` is
`homDistinctPreMate`. Its coordinate formula (`homDistinctPreMate_eq`) is
precomposition by the factor left mate `leftCrossMate` of `T`, between the
two shift removals, up to the sign `(-1)^(σ_a + σ_d r + r σ_a + σ_d σ_a)`, for
`T` of any parity `r`. For a common parity `σ_d = σ_a`, as for the distinct-colour
crossings, the four Koszul signs cancel and no sign remains.

Consequently the mate is invertible when the left mate is
(`homDistinctPreMateInv`). For a distinct-colour crossing of a Rouquier family
the invertibility of the left mate is the interface `LeftMateInvertible`. It is
not a consequence of `RouquierMulticolour`, whose field `invNe` inverts the right
mate `crossMate`, and of an arbitrary choice of left adjunctions; it is supplied by
the factor action, which interprets the presented calculus.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section LeftMate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {c₀ m a₁ b₁ : B} {E_d : c₀ ⟶ m} {F_d : m ⟶ c₀} {E_c : m ⟶ b₁}
  {E_b : c₀ ⟶ a₁} {E_a : a₁ ⟶ b₁} {F_a : b₁ ⟶ a₁} {σd σa : ZMod 2}

/-- The left mate of a 2-cell `T : E_d ≫ E_c ⟶ E_b ≫ E_a` along shifted left
adjunctions `F_d ⊣ E_d` and `F_a ⊣ E_a`: the unit of the first, `T`, and the
counit of the second. -/
def leftCrossMate (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa) (T : E_d ≫ E_c ⟶ E_b ≫ E_a) :
    E_c ≫ F_a ⟶ F_d ≫ E_b :=
  (leftUnitor (E_c ≫ F_a)).inv ≫ A_d.unit ▷ (E_c ≫ F_a) ≫
    (associator F_d E_d (E_c ≫ F_a)).hom ≫ F_d ◁ (associator E_d E_c F_a).inv ≫
    F_d ◁ (T ▷ F_a) ≫ F_d ◁ (associator E_b E_a F_a).hom ≫ F_d ◁ (E_b ◁ A_a.counit) ≫
    F_d ◁ (rightUnitor E_b).hom

end LeftMate

section Coherence
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {c₀ m a₁ b₁ w : B}
include k

private theorem coh_one (E_c : m ⟶ b₁) (F_a : b₁ ⟶ a₁) (H : a₁ ⟶ w) :
    (associator E_c F_a H).inv ≫ (leftUnitor (E_c ≫ F_a)).inv ▷ H ≫
      (associator (𝟙 m) E_c F_a).inv ▷ H =
    (leftUnitor (E_c ≫ F_a ≫ H)).inv ≫ (associator (𝟙 m) E_c (F_a ≫ H)).inv ≫
      (associator (𝟙 m ≫ E_c) F_a H).inv := by
  let E_c' := Underlying2.hom1 (R := k) E_c
  let F_a' := Underlying2.hom1 (R := k) F_a
  let H' := Underlying2.hom1 (R := k) H
  have h : (Bicategory.associator E_c' F_a' H').inv ≫
      Bicategory.whiskerRight (Bicategory.leftUnitor (E_c' ≫ F_a')).inv H' ≫
      Bicategory.whiskerRight (Bicategory.associator (𝟙 _) E_c' F_a').inv H' =
    (Bicategory.leftUnitor (E_c' ≫ F_a' ≫ H')).inv ≫
      (Bicategory.associator (𝟙 _) E_c' (F_a' ≫ H')).inv ≫
      (Bicategory.associator (𝟙 _ ≫ E_c') F_a' H').inv := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_two (F_d : m ⟶ c₀) (E_d : c₀ ⟶ m) (E_c : m ⟶ b₁) (F_a : b₁ ⟶ a₁)
    (H : a₁ ⟶ w) :
    (associator (F_d ≫ E_d) E_c F_a).hom ▷ H ≫
      (associator F_d E_d (E_c ≫ F_a)).hom ▷ H ≫
      (associator F_d (E_d ≫ E_c ≫ F_a) H).hom ≫
      F_d ◁ ((associator E_d E_c F_a).inv ▷ H) =
    (associator ((F_d ≫ E_d) ≫ E_c) F_a H).hom ≫
      (associator (F_d ≫ E_d) E_c (F_a ≫ H)).hom ≫
      (associator F_d E_d (E_c ≫ F_a ≫ H)).hom ≫
      F_d ◁ (associator E_d E_c (F_a ≫ H)).inv ≫
      F_d ◁ (associator (E_d ≫ E_c) F_a H).inv := by
  let F_d' := Underlying2.hom1 (R := k) F_d
  let E_d' := Underlying2.hom1 (R := k) E_d
  let E_c' := Underlying2.hom1 (R := k) E_c
  let F_a' := Underlying2.hom1 (R := k) F_a
  let H' := Underlying2.hom1 (R := k) H
  have h : Bicategory.whiskerRight (Bicategory.associator (F_d' ≫ E_d') E_c' F_a').hom H' ≫
      Bicategory.whiskerRight (Bicategory.associator F_d' E_d' (E_c' ≫ F_a')).hom H' ≫
      (Bicategory.associator F_d' (E_d' ≫ E_c' ≫ F_a') H').hom ≫
      Bicategory.whiskerLeft F_d'
        (Bicategory.whiskerRight (Bicategory.associator E_d' E_c' F_a').inv H') =
    (Bicategory.associator ((F_d' ≫ E_d') ≫ E_c') F_a' H').hom ≫
      (Bicategory.associator (F_d' ≫ E_d') E_c' (F_a' ≫ H')).hom ≫
      (Bicategory.associator F_d' E_d' (E_c' ≫ F_a' ≫ H')).hom ≫
      Bicategory.whiskerLeft F_d' (Bicategory.associator E_d' E_c' (F_a' ≫ H')).inv ≫
      Bicategory.whiskerLeft F_d' (Bicategory.associator (E_d' ≫ E_c') F_a' H').inv := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_three (F_d : m ⟶ c₀) (E_b : c₀ ⟶ a₁) (E_a : a₁ ⟶ b₁) (F_a : b₁ ⟶ a₁)
    (H : a₁ ⟶ w) :
    F_d ◁ ((associator E_b E_a F_a).hom ▷ H) ≫ F_d ◁ (associator E_b (E_a ≫ F_a) H).hom =
    F_d ◁ (associator (E_b ≫ E_a) F_a H).hom ≫ F_d ◁ (associator E_b E_a (F_a ≫ H)).hom ≫
      F_d ◁ (E_b ◁ (associator E_a F_a H).inv) := by
  let F_d' := Underlying2.hom1 (R := k) F_d
  let E_b' := Underlying2.hom1 (R := k) E_b
  let E_a' := Underlying2.hom1 (R := k) E_a
  let F_a' := Underlying2.hom1 (R := k) F_a
  let H' := Underlying2.hom1 (R := k) H
  have h : Bicategory.whiskerLeft F_d'
        (Bicategory.whiskerRight (Bicategory.associator E_b' E_a' F_a').hom H') ≫
      Bicategory.whiskerLeft F_d' (Bicategory.associator E_b' (E_a' ≫ F_a') H').hom =
    Bicategory.whiskerLeft F_d' (Bicategory.associator (E_b' ≫ E_a') F_a' H').hom ≫
      Bicategory.whiskerLeft F_d' (Bicategory.associator E_b' E_a' (F_a' ≫ H')).hom ≫
      Bicategory.whiskerLeft F_d'
        (Bicategory.whiskerLeft E_b' (Bicategory.associator E_a' F_a' H').inv) := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_four (F_d : m ⟶ c₀) (E_b : c₀ ⟶ a₁) (H : a₁ ⟶ w) :
    F_d ◁ (associator E_b (𝟙 a₁) H).inv ≫ F_d ◁ ((rightUnitor E_b).hom ▷ H) =
      F_d ◁ (E_b ◁ (leftUnitor H).hom) := by
  let F_d' := Underlying2.hom1 (R := k) F_d
  let E_b' := Underlying2.hom1 (R := k) E_b
  let H' := Underlying2.hom1 (R := k) H
  have h : Bicategory.whiskerLeft F_d' (Bicategory.associator E_b' (𝟙 _) H').inv ≫
      Bicategory.whiskerLeft F_d' (Bicategory.whiskerRight (Bicategory.rightUnitor E_b').hom H') =
    Bicategory.whiskerLeft F_d' (Bicategory.whiskerLeft E_b' (Bicategory.leftUnitor H').hom) := by
    bicategory
  exact congrArg Subtype.val h

end Coherence

section Whisker
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {c₀ m a₁ b₁ w : B} {E_d : c₀ ⟶ m} {F_d : m ⟶ c₀} {E_c : m ⟶ b₁}
  {E_b : c₀ ⟶ a₁} {E_a : a₁ ⟶ b₁} {F_a : b₁ ⟶ a₁} {σd σa : ZMod 2}

/-- The left mate whiskered by `H`, conjugated by associators: the unit word, `T`
precomposed on `F_a ≫ H`, and the counit word. Even coherence only; the unit,
`T` and the counit may have any parity. -/
theorem leftCrossMate_whiskerRight (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa) (T : E_d ≫ E_c ⟶ E_b ≫ E_a)
    (H : a₁ ⟶ w) :
    (associator E_c F_a H).inv ≫ leftCrossMate A_d A_a T ▷ H ≫ (associator F_d E_b H).hom =
    (leftUnitor (E_c ≫ F_a ≫ H)).inv ≫ A_d.unit ▷ (E_c ≫ F_a ≫ H) ≫
      (associator F_d E_d (E_c ≫ F_a ≫ H)).hom ≫
      F_d ◁ (associator E_d E_c (F_a ≫ H)).inv ≫ F_d ◁ (T ▷ (F_a ≫ H)) ≫
      F_d ◁ (associator E_b E_a (F_a ≫ H)).hom ≫ F_d ◁ (E_b ◁ (associator E_a F_a H).inv) ≫
      F_d ◁ (E_b ◁ (A_a.counit ▷ H)) ≫ F_d ◁ (E_b ◁ (leftUnitor H).hom) := by
  unfold leftCrossMate
  simp only [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whisker_assoc (R := k),
    TwoSupercategory.whiskerRight_comp (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% (coh_one (k := k) E_c F_a H), reassoc_of% (coh_two (k := k) F_d E_d E_c F_a H),
    reassoc_of% (coh_three (k := k) F_d E_b E_a F_a H), coh_four (k := k) F_d E_b H]

end Whisker
section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {c₀ m a₁ b₁ w : B} {E_d : c₀ ⟶ m} {F_d : m ⟶ c₀} {E_c : m ⟶ b₁}
  {E_b : c₀ ⟶ a₁} {E_a : a₁ ⟶ b₁} {F_a : b₁ ⟶ a₁} {σd σa : ZMod 2}

/-- The pre/pre mate (A9): the target pre unit at `E_c ≫ R_a H`, the factor 2-cell
`T` precomposed on `R_a H`, and the source pre counit at `H`. -/
def homDistinctPreMate (T : E_d ≫ E_c ⟶ E_b ≫ E_a)
    (adjd : homPre (k := k) (c := w) E_d ⊣ homPre (k := k) F_d ⋙ homParityShift (k := k) σd)
    (adja : homPre (k := k) (c := w) E_a ⊣ homPre (k := k) F_a ⋙ homParityShift (k := k) σa)
    (H : a₁ ⟶ w) :
    E_c ≫ (homParityShift (k := k) σa).obj (F_a ≫ H) ⟶
      (homParityShift (k := k) σd).obj (F_d ≫ E_b ≫ H) :=
  adjd.unit.app (E_c ≫ (homParityShift (k := k) σa).obj (F_a ≫ H)) ≫
    (homPre (k := k) F_d ⋙ homParityShift (k := k) σd).map
      ((associator E_d E_c ((homParityShift (k := k) σa).obj (F_a ≫ H))).inv ≫
        T ▷ (homParityShift (k := k) σa).obj (F_a ≫ H) ≫
        (associator E_b E_a ((homParityShift (k := k) σa).obj (F_a ≫ H))).hom ≫
        E_b ◁ adja.counit.app H)

/-- The coordinate formula of the pre/pre mate (A9): between the two shift removals
it is precomposition by the factor left mate `leftCrossMate`, up to the sign
`(-1)^(σa + σd r + r σa + σd σa)`. The unit and counit of the precomposition
adjunctions are the normalized words of shifted left adjunctions of parities `σd`,
`σa`, and the crossing `T` has parity `r`. For `σd = σa` the sign is `1`. -/
theorem homDistinctPreMate_eq {r : ZMod 2} {T : E_d ≫ E_c ⟶ E_b ≫ E_a}
    (hT : T ∈ parity (R := k) _ _ r)
    {adjd : homPre (k := k) (c := w) E_d ⊣ homPre (k := k) F_d ⋙ homParityShift (k := k) σd}
    {adja : homPre (k := k) (c := w) E_a ⊣ homPre (k := k) F_a ⋙ homParityShift (k := k) σa}
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (hunit : ∀ Y : m ⟶ w, adjd.unit.app Y = (leftUnitor Y).inv ≫ A_d.unit ▷ Y ≫
      (associator F_d E_d Y).hom ≫ ((homParityShiftDatum (k := k) σd).iso (F_d ≫ E_d ≫ Y)).inv)
    (hcounit : ∀ H : a₁ ⟶ w, adja.counit.app H = koszulSign σa σa •
      (E_a ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).hom ≫
        (associator E_a F_a H).inv ≫ A_a.counit ▷ H ≫ (leftUnitor H).hom))
    (H : a₁ ⟶ w) :
    homDistinctPreMate T adjd adja H = sign k (σa + σd * r + r * σa + σd * σa) •
      (E_c ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).hom ≫
        (associator E_c F_a H).inv ≫ leftCrossMate A_d A_a T ▷ H ≫
        (associator F_d E_b H).hom ≫
        ((homParityShiftDatum (k := k) σd).iso (F_d ≫ E_b ≫ H)).inv) := by
  set X := (homParityShift (k := k) σa).obj (F_a ≫ H) with hX
  set φ := ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).hom with hφ
  have hφmem : φ ∈ parity (R := k) _ _ σa :=
    (homParityShiftDatum (k := k) σa).hom_mem (F_a ≫ H)
  obtain ⟨ε, hε⟩ : ∃ ε : E_a ≫ X ⟶ H, adja.counit.app H = ε := ⟨_, rfl⟩
  have hε' : ε = sign k (σa * σa) •
      (E_a ◁ φ ≫ (associator E_a F_a H).inv ≫ A_a.counit ▷ H ≫ (leftUnitor H).hom) := by
    rw [← hε, hcounit, koszulSign_smul (R := k)]
  have hεmem : ε ∈ parity (R := k) _ _ 0 := by
    rw [hε']
    apply Submodule.smul_mem
    have h := comp_mem (comp_mem (comp_mem
      (TwoSupercategory.whiskerLeft_mem E_a hφmem)
      (inv_mem (associator E_a F_a H) (TwoSupercategory.associator_hom_mem (R := k) E_a F_a H)))
      (TwoSupercategory.whiskerRight_mem H A_a.counit_mem))
      (TwoSupercategory.leftUnitor_hom_mem (R := k) H)
    simp only [add_zero, zmod2_add_self] at h
    simpa only [Category.assoc] using h
  set g := (associator E_d E_c X).inv ≫ T ▷ X ≫ (associator E_b E_a X).hom ≫ E_b ◁ ε with hg
  have hgmem : g ∈ parity (R := k) _ _ r := by
    have h := comp_mem (comp_mem (comp_mem
      (inv_mem (associator E_d E_c X) (TwoSupercategory.associator_hom_mem (R := k) E_d E_c X))
      (TwoSupercategory.whiskerRight_mem X hT))
      (TwoSupercategory.associator_hom_mem (R := k) E_b E_a X))
      (TwoSupercategory.whiskerLeft_mem E_b hεmem)
    simp only [add_zero, zero_add] at h
    simpa only [Category.assoc, hg] using h
  -- `g`, with the source shift removal moved to the front
  have hgform : g = (sign k (σa * σa) * sign k (r * σa)) •
      (E_d ◁ E_c ◁ φ ≫ (associator E_d E_c (F_a ≫ H)).inv ≫ T ▷ (F_a ≫ H) ≫
        (associator E_b E_a (F_a ≫ H)).hom ≫ E_b ◁ (associator E_a F_a H).inv ≫
        E_b ◁ (A_a.counit ▷ H) ≫ E_b ◁ (leftUnitor H).hom) := by
    rw [hg, hε']
    simp only [TwoSupercategory.whiskerLeft_smul (R := k),
      TwoSupercategory.whiskerLeft_comp (R := k),
      Linear.comp_smul]
    rw [← TwoSupercategory.associator_naturality_right_assoc (R := k) E_b E_a φ,
      TwoSupercategory.super_interchange_assoc (R := k) hT hφmem, Linear.comp_smul,
      ← TwoSupercategory.associator_inv_naturality_right_assoc (R := k) E_d E_c φ,
      koszulSign_smul (R := k), smul_smul]
  -- removal of the final shift through the target functor
  have hδ' : ((homParityShiftDatum (k := k) σd).iso (F_d ≫ E_d ≫ E_c ≫ X)).inv ≫
      (homParityShift (k := k) σd).map (F_d ◁ g) =
      sign k (σd * r) • (F_d ◁ g ≫
        ((homParityShiftDatum (k := k) σd).iso (F_d ≫ E_b ≫ H)).inv) := by
    rw [(homParityShiftDatum (k := k) σd).inv_naturality
      (TwoSupercategory.whiskerLeft_mem F_d hgmem), smul_smul, sign_mul_self, one_smul]
  unfold homDistinctPreMate
  rw [hunit, hε]
  show (_ ≫ _ ≫ _ ≫ _) ≫ (homParityShift (k := k) σd).map (F_d ◁ g) = _
  simp only [Category.assoc]
  rw [hδ', hgform]
  simp only [TwoSupercategory.whiskerLeft_smul (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    Linear.comp_smul, Linear.smul_comp, Category.assoc, smul_smul]
  rw [A_d.unit_slide (TwoSupercategory.whiskerLeft_mem E_c hφmem)]
  rw [reassoc_of% (leftCrossMate_whiskerRight A_d A_a T H)]
  simp only [smul_smul]
  congr 1
  simp only [← sign_add]
  congr 1
  rcases parity_eq_zero_or_one σd with hd | hd <;>
    rcases parity_eq_zero_or_one σa with ha | ha <;>
    rcases parity_eq_zero_or_one r with hr | hr <;>
    · rw [hd, ha, hr]; decide

/-- The inverse of the pre/pre mate, from an inverse of the factor left mate:
precomposition by `inv (leftCrossMate A_d A_a T)` between the two shift
comparisons, with the same sign. -/
def homDistinctPreMateInv (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa) (T : E_d ≫ E_c ⟶ E_b ≫ E_a)
    [IsIso (leftCrossMate A_d A_a T)] (r : ZMod 2) (H : a₁ ⟶ w) :
    (homParityShift (k := k) σd).obj (F_d ≫ E_b ≫ H) ⟶
      E_c ≫ (homParityShift (k := k) σa).obj (F_a ≫ H) :=
  sign k (σa + σd * r + r * σa + σd * σa) •
    (((homParityShiftDatum (k := k) σd).iso (F_d ≫ E_b ≫ H)).hom ≫
      (associator F_d E_b H).inv ≫ inv (leftCrossMate A_d A_a T) ▷ H ≫
      (associator E_c F_a H).hom ≫
      E_c ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).inv)

/-- `homDistinctPreMateInv` is a two-sided inverse of the pre/pre mate. -/
theorem homDistinctPreMate_inv_products {r : ZMod 2} {T : E_d ≫ E_c ⟶ E_b ≫ E_a}
    (hT : T ∈ parity (R := k) _ _ r)
    {adjd : homPre (k := k) (c := w) E_d ⊣ homPre (k := k) F_d ⋙ homParityShift (k := k) σd}
    {adja : homPre (k := k) (c := w) E_a ⊣ homPre (k := k) F_a ⋙ homParityShift (k := k) σa}
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa) [IsIso (leftCrossMate A_d A_a T)]
    (hunit : ∀ Y : m ⟶ w, adjd.unit.app Y = (leftUnitor Y).inv ≫ A_d.unit ▷ Y ≫
      (associator F_d E_d Y).hom ≫ ((homParityShiftDatum (k := k) σd).iso (F_d ≫ E_d ≫ Y)).inv)
    (hcounit : ∀ H : a₁ ⟶ w, adja.counit.app H = koszulSign σa σa •
      (E_a ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).hom ≫
        (associator E_a F_a H).inv ≫ A_a.counit ▷ H ≫ (leftUnitor H).hom))
    (H : a₁ ⟶ w) :
    homDistinctPreMate T adjd adja H ≫ homDistinctPreMateInv A_d A_a T r H = 𝟙 _ ∧
      homDistinctPreMateInv A_d A_a T r H ≫ homDistinctPreMate T adjd adja H = 𝟙 _ := by
  have hL : leftCrossMate A_d A_a T ▷ H ≫ inv (leftCrossMate A_d A_a T) ▷ H = 𝟙 _ := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), IsIso.hom_inv_id,
      TwoSupercategory.id_whiskerRight (R := k)]
  have hL' : inv (leftCrossMate A_d A_a T) ▷ H ≫ leftCrossMate A_d A_a T ▷ H = 𝟙 _ := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), IsIso.inv_hom_id,
      TwoSupercategory.id_whiskerRight (R := k)]
  have hφ : E_c ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).hom ≫
      E_c ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).inv = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), Iso.hom_inv_id,
      TwoSupercategory.whiskerLeft_id (R := k)]
  have hφ' : E_c ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).inv ≫
      E_c ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).hom = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), Iso.inv_hom_id,
      TwoSupercategory.whiskerLeft_id (R := k)]
  rw [homDistinctPreMate_eq hT A_d A_a hunit hcounit H]
  unfold homDistinctPreMateInv
  constructor
  · simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul,
      Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hL, hφ, Iso.hom_inv_id_assoc]
  · simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul,
      Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hL', reassoc_of% hφ', Iso.hom_inv_id,
      Iso.hom_inv_id_assoc]

/-- The pre/pre mate is invertible as soon as the factor left mate is. -/
theorem homDistinctPreMate_isIso {r : ZMod 2} {T : E_d ≫ E_c ⟶ E_b ≫ E_a}
    (hT : T ∈ parity (R := k) _ _ r)
    {adjd : homPre (k := k) (c := w) E_d ⊣ homPre (k := k) F_d ⋙ homParityShift (k := k) σd}
    {adja : homPre (k := k) (c := w) E_a ⊣ homPre (k := k) F_a ⋙ homParityShift (k := k) σa}
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa) [IsIso (leftCrossMate A_d A_a T)]
    (hunit : ∀ Y : m ⟶ w, adjd.unit.app Y = (leftUnitor Y).inv ≫ A_d.unit ▷ Y ≫
      (associator F_d E_d Y).hom ≫ ((homParityShiftDatum (k := k) σd).iso (F_d ≫ E_d ≫ Y)).inv)
    (hcounit : ∀ H : a₁ ⟶ w, adja.counit.app H = koszulSign σa σa •
      (E_a ◁ ((homParityShiftDatum (k := k) σa).iso (F_a ≫ H)).hom ≫
        (associator E_a F_a H).inv ≫ A_a.counit ▷ H ≫ (leftUnitor H).hom))
    (H : a₁ ⟶ w) : IsIso (homDistinctPreMate T adjd adja H) :=
  let h := homDistinctPreMate_inv_products hT A_d A_a hunit hcounit H
  ⟨⟨_, h.1, h.2⟩⟩

end Mate

section Content
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D)

/-- For distinct colours `i ≠ j`, the left mate of the crossing `E_i E_j ⟶ E_j E_i`
along the chosen left adjunctions `F_i ⊣ E_i` is invertible. This is not implied by
`RouquierMulticolour`, whose `invNe` inverts the right mate `crossMate`, together with
an arbitrary choice of left adjunctions. It holds in the factor 2-representation of
the presented calculus, where the leftward crossing is a two-sided inverse. -/
def LeftMateInvertible (L : RouquierLeftAdjoints (k := k) T) : Prop :=
  ∀ (i j : I), i ≠ j → ∀ {a b c d : X} (h₁ : a + D.α i = b) (h₂ : b + D.α j = d)
    (h₃ : a + D.α j = c) (h₄ : c + D.α i = d),
    IsIso (leftCrossMate (L.adjL i h₁) (L.adjL i h₄) (T.cross j i h₁ h₂ h₃ h₄))

variable [∀ a b : B, PiSupercategory k (a ⟶ b)] (W : X → B) (L : RouquierLeftAdjoints (k := k) T)

/-- The pre/pre mate (A9) of a distinct-colour crossing, along the content-shifted
precomposition adjunctions, is invertible under `LeftMateInvertible`. -/
theorem homContentDistinctPreMate_isIso (hL : LeftMateInvertible T L) {i j : I} (hij : i ≠ j)
    (muM : X) {n₁ n₂ n₃ n₄ : X} (h₁ : -n₁ + D.α i = -n₂) (h₂ : -n₂ + D.α j = -n₄)
    (h₃ : -n₁ + D.α j = -n₃) (h₄ : -n₃ + D.α i = -n₄) (H : homWeightSector T.obj W n₃ muM) :
    IsIso (homDistinctPreMate (T.cross j i h₁ h₂ h₃ h₄) (homContentPreAdjunction T W L i muM h₁)
      (homContentPreAdjunction T W L i muM h₄) H) :=
  have := hL i j hij h₁ h₂ h₃ h₄
  homDistinctPreMate_isIso (T.cross_mem j i h₁ h₂ h₃ h₄) (L.adjL i h₁) (L.adjL i h₄)
    (fun Y => homContentPreAdjunction_unit_app T W i muM h₁ L Y)
    (fun Z => homContentPreAdjunction_counit_app T W i muM h₄ L Z) H

end Content
end OddMath.SKM
