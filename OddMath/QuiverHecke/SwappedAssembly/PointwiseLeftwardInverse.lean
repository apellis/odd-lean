import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedMatrix

/-! # Leftward entries from pointwise augmented inverses

Brundan–Ellis Definition 1.5, (1.13)–(1.14), and
`SwappedActionAssembly.md` (A7): choose the inverse of an augmented matrix
at each input where it is invertible, and zero otherwise. These objectwise
entries form raw `LeftwardData`. Inversion identities are asserted only
at inputs with the corresponding proved local matrix isomorphism.
No invertibility at all raw Hom objects or naturality is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams Supercategory OddMath.SKM Classical

universe u uB vB wB
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB,vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
local instance pointwiseInversePathFintype {w : List (Col I X)} {t s : Sector I} : Fintype (SPath w t s) :=
  Fintype.ofFinite _

/-- The five positive augmented-inverse identities at a single input. -/
def PosInverseAt (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I) (Z : P.H s)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (wd D ν []) t s) (p : SPath (wd D ν [up i, dn i]) t s),
      (P.pathFunctor _r).obj Z ⟶ (P.pathFunctor p).obj Z) : Prop :=
  letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν []) t s)
  (∀ p p', -∑ q, P.sigmaEntry c i i ν p q Z ≫ lc q p' +
      ∑ n ∈ Finset.range (D.h i ν).toNat, ∑ r, P.epsEntry c i n ν p r Z ≫ dc n r p' =
      famDelta (fun x => P.pathFunctor x) p p' Z) ∧
  (∀ q q', ∑ p, lc q p ≫ P.sigmaEntry c i i ν p q' Z =
      -famDelta (fun x => P.pathFunctor x) q q' Z) ∧
  (∀ m : ℕ, (m : ℤ) < D.h i ν → ∀ q r, ∑ p, lc q p ≫ P.epsEntry c i m ν p r Z = 0) ∧
  (∀ n : ℕ, (n : ℤ) < D.h i ν → ∀ r q, ∑ p, dc n r p ≫ P.sigmaEntry c i i ν p q Z = 0) ∧
  (∀ m n : ℕ, (m : ℤ) < D.h i ν → (n : ℤ) < D.h i ν → ∀ r r',
      ∑ p, dc n r p ≫ P.epsEntry c i m ν p r' Z =
        if m = n then famDelta (fun x => P.pathFunctor x) r r' Z else 0)

/-- The five negative augmented-inverse identities at a single input. -/
def NegInverseAt (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I) (Z : P.H s)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (r : SPath (wd D ν []) t s),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z) : Prop :=
  letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν []) t s)
  (∀ q q', -∑ p, lc q p ≫ P.sigmaEntry c i i ν p q' Z +
      ∑ n ∈ Finset.range (-D.h i ν).toNat, ∑ r, dc n q r ≫ P.etaEntry c i n ν r q' Z =
      famDelta (fun x => P.pathFunctor x) q q' Z) ∧
  (∀ p p', ∑ q, P.sigmaEntry c i i ν p q Z ≫ lc q p' =
      -famDelta (fun x => P.pathFunctor x) p p' Z) ∧
  (∀ m : ℕ, (m : ℤ) < -D.h i ν → ∀ r p, ∑ q, P.etaEntry c i m ν r q Z ≫ lc q p = 0) ∧
  (∀ n : ℕ, (n : ℤ) < -D.h i ν → ∀ p r, ∑ q, P.sigmaEntry c i i ν p q Z ≫ dc n q r = 0) ∧
  (∀ m n : ℕ, (m : ℤ) < -D.h i ν → (n : ℤ) < -D.h i ν → ∀ r r',
      ∑ q, P.etaEntry c i m ν r q Z ≫ dc n q r' =
        if m = n then famDelta (fun x => P.pathFunctor x) r r' Z else 0)

/-- The selected positive inverse family in the original summand-path indices. -/
def augPosInverseFamily (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I) (Z : P.H s) :
    ∀ (y : SPath (wd D ν [dn i,up i]) t s ⊕
        (Fin (D.h i ν).toNat × SPath (wd D ν []) t s))
      (p : SPath (wd D ν [up i,dn i]) t s),
      (Sum.elim (fun q => (P.pathFunctor q).obj Z)
        (fun nr => (P.pathFunctor nr.2).obj Z)) y ⟶ (P.pathFunctor p).obj Z :=
  if h : IsIso (P.augPosMat c i ν t s Z) then
    Classical.choose (@exists_famInverse_of_isIso _ _ _ _ _ _ _ _ _ _ _ _ h)
  else fun _ _ => 0

/-- The selected negative inverse family in the original summand-path indices. -/
def augNegInverseFamily (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I) (Z : P.H s) :
    ∀ (q : SPath (wd D ν [dn i,up i]) t s)
      (y : SPath (wd D ν [up i,dn i]) t s ⊕
        (Fin (-D.h i ν).toNat × SPath (wd D ν []) t s)),
      (P.pathFunctor q).obj Z ⟶
        (Sum.elim (fun p => (P.pathFunctor p).obj Z)
          (fun nr => (P.pathFunctor nr.2).obj Z)) y :=
  if h : IsIso (P.augNegMat c i ν t s Z) then
    Classical.choose (@exists_famInverse_of_isIso _ _ _ _ _ _ _ _ _ _ _ _ h)
  else fun _ _ => 0

/-- Raw leftward data chosen separately at each input matrix, with zero
entries when its local inverse does not exist and off the matched weight. -/
def leftwardOfPointwiseAugmentedInverse (c : P.CrossCoeff) : P.LeftwardData where
  lcrossSame i ν {t s} q p Z :=
    if P.wt s = ν then
      if 0 ≤ D.h i ν then -P.augPosInverseFamily c i ν t s Z (.inl q) p
      else P.augNegInverseFamily c i ν t s Z q (.inl p)
    else 0
  dcup i n ν {t s} r p Z :=
    if P.wt s = ν then
      if 0 ≤ D.h i ν then
        if hn : n < (D.h i ν).toNat then
          P.augPosInverseFamily c i ν t s Z (.inr (⟨n,hn⟩,r)) p
        else 0
      else 0
    else 0
  dcap i n ν {t s} q r Z :=
    if P.wt s = ν then
      if D.h i ν < 0 then
        if hn : n < (-D.h i ν).toNat then
          P.augNegInverseFamily c i ν t s Z q (.inr (⟨n,hn⟩,r))
        else 0
      else 0
    else 0

/-- Off-weight normalization of the pointwise selected leftward data. -/
theorem leftwardOfPointwiseAugmentedInverse_vanishesOffWeight (c : P.CrossCoeff) :
    (P.leftwardOfPointwiseAugmentedInverse c).VanishesOffWeight :=
  ⟨fun i ν t s p p' Z hw => by simp [leftwardOfPointwiseAugmentedInverse,hw],
    fun i n ν t s p p' Z hw => by simp [leftwardOfPointwiseAugmentedInverse,hw],
    fun i n ν t s p p' Z hw => by simp [leftwardOfPointwiseAugmentedInverse,hw]⟩

/-- The five positive identities for the selected inverse at one input. -/
theorem posInverseAt_of_isIso (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I)
    (Z : P.H s) [IsIso (P.augPosMat c i ν t s Z)] :
    P.PosInverseAt c i ν t s Z
      (fun q p => -P.augPosInverseFamily c i ν t s Z (.inl q) p)
      (fun n r p => if hn : n < (D.h i ν).toNat then
        P.augPosInverseFamily c i ν t s Z (.inr (⟨n,hn⟩,r)) p else 0) := by
  have key := @exists_famInverse_of_isIso _ _ _ _ _ _ _ _ _ _ _ _
    (inferInstance : IsIso (P.augPosMat c i ν t s Z))
  let b := Classical.choose key
  have hb₁ := (Classical.choose_spec key).1
  have hb₂ := (Classical.choose_spec key).2
  have hb : P.augPosInverseFamily c i ν t s Z = b := by
    simp only [augPosInverseFamily, dite_eq_left (inferInstance : IsIso (P.augPosMat c i ν t s Z))]
    rfl
  rw [hb]
  dsimp only [b]
  refine ⟨fun p p' => ?_, fun q q' => ?_, fun m hm q r => ?_, fun n hn r q => ?_,
    fun m n hm hn r r' => ?_⟩
  · have e := hb₁ p p'
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at e
    dsimp only at e
    rw [← famId_path, ← e, Finset.sum_range]
    simp only [Preadditive.comp_neg, Finset.sum_neg_distrib, neg_neg, Fin.is_lt,
      ↓reduceDIte, Fin.eta]
  · have e := hb₂ (.inl q) (.inl q')
    dsimp only at e
    rw [famId_inl] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib, e, famId_path]
  · have e := hb₂ (.inl q) (.inr (⟨m, by omega⟩, r))
    dsimp only at e
    rw [famId_inl_inr] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib, neg_eq_zero]
    exact e
  · have e := hb₂ (.inr (⟨n, by omega⟩, r)) (.inl q)
    dsimp only at e
    rw [famId_inr_inl] at e
    simp only [show n < (D.h i ν).toNat by omega, ↓reduceDIte]
    exact e
  · have e := hb₂ (.inr (⟨n, by omega⟩, r)) (.inr (⟨m, by omega⟩, r'))
    dsimp only at e
    rw [famId_inr, famId_prod (Yb := fun r => (P.pathFunctor r).obj Z)] at e
    simp only [show n < (D.h i ν).toNat by omega, ↓reduceDIte]
    rw [e]
    by_cases hmn : m = n
    · subst hmn; simp [famId_path]
    · simp only [Fin.mk.injEq, Ne.symm hmn, hmn, ite_false]

/-- The five negative identities for the selected inverse at one input. -/
theorem negInverseAt_of_isIso (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I)
    (Z : P.H s) [IsIso (P.augNegMat c i ν t s Z)] :
    P.NegInverseAt c i ν t s Z
      (fun q p => P.augNegInverseFamily c i ν t s Z q (.inl p))
      (fun n q r => if hn : n < (-D.h i ν).toNat then
        P.augNegInverseFamily c i ν t s Z q (.inr (⟨n,hn⟩,r)) else 0) := by
  have key := @exists_famInverse_of_isIso _ _ _ _ _ _ _ _ _ _ _ _
    (inferInstance : IsIso (P.augNegMat c i ν t s Z))
  let b := Classical.choose key
  have hb₁ := (Classical.choose_spec key).1
  have hb₂ := (Classical.choose_spec key).2
  have hb : P.augNegInverseFamily c i ν t s Z = b := by
    simp only [augNegInverseFamily, dite_eq_left (inferInstance : IsIso (P.augNegMat c i ν t s Z))]
    rfl
  rw [hb]
  dsimp only [b]
  refine ⟨fun q q' => ?_, fun p p' => ?_, fun m hm r p => ?_, fun n hn p r => ?_,
    fun m n hm hn r r' => ?_⟩
  · have e := hb₂ q q'
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at e
    dsimp only at e
    rw [← famId_path, ← e, Finset.sum_range]
    simp only [Preadditive.comp_neg, Finset.sum_neg_distrib, Fin.is_lt, ↓reduceDIte, Fin.eta]
  · have e := hb₁ (.inl p) (.inl p')
    dsimp only at e
    rw [famId_inl] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib] at e
    rw [← famId_path, ← e, neg_neg]
  · have e := hb₁ (.inr (⟨m, by omega⟩, r)) (.inl p)
    dsimp only at e
    rw [famId_inr_inl] at e
    exact e
  · have e := hb₁ (.inl p) (.inr (⟨n, by omega⟩, r))
    dsimp only at e
    rw [famId_inl_inr] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib, neg_eq_zero] at e
    simp only [show n < (-D.h i ν).toNat by omega, ↓reduceDIte]
    exact e
  · have e := hb₁ (.inr (⟨m, by omega⟩, r)) (.inr (⟨n, by omega⟩, r'))
    dsimp only at e
    rw [famId_inr, famId_prod (Yb := fun r => (P.pathFunctor r).obj Z)] at e
    simp only [show n < (-D.h i ν).toNat by omega, ↓reduceDIte]
    rw [e]
    by_cases hmn : m = n
    · subst hmn; simp [famId_path]
    · simp only [Fin.mk.injEq, hmn, ite_false]

/-- The chosen raw leftward entries satisfy the positive inverse identities
where that input's positive augmented matrix is an isomorphism. -/
theorem leftwardOfPointwiseAugmentedInverse_posInverseAt (c : P.CrossCoeff)
    (i : I) (ν : X) (t s : Sector I) (Z : P.H s) (hw : P.wt s = ν)
    (hh : 0 ≤ D.h i ν) [IsIso (P.augPosMat c i ν t s Z)] :
    P.PosInverseAt c i ν t s Z
      (fun q p => (P.leftwardOfPointwiseAugmentedInverse c).lcrossSame i ν q p Z)
      (fun n r p => (P.leftwardOfPointwiseAugmentedInverse c).dcup i n ν r p Z) := by
  simpa only [leftwardOfPointwiseAugmentedInverse,ite_eq_left hw,ite_eq_left hh] using
    P.posInverseAt_of_isIso c i ν t s Z

/-- The chosen raw leftward entries satisfy the negative inverse identities
where that input's negative augmented matrix is an isomorphism. -/
theorem leftwardOfPointwiseAugmentedInverse_negInverseAt (c : P.CrossCoeff)
    (i : I) (ν : X) (t s : Sector I) (Z : P.H s) (hw : P.wt s = ν)
    (hh : D.h i ν < 0) [IsIso (P.augNegMat c i ν t s Z)] :
    P.NegInverseAt c i ν t s Z
      (fun q p => (P.leftwardOfPointwiseAugmentedInverse c).lcrossSame i ν q p Z)
      (fun n q r => (P.leftwardOfPointwiseAugmentedInverse c).dcap i n ν q r Z) := by
  simpa only [leftwardOfPointwiseAugmentedInverse,ite_eq_left hw,ite_eq_left hh,
    ite_eq_right (not_le.mpr hh)] using P.negInverseAt_of_isIso c i ν t s Z

variable {P}

/-- The unwhiskered equal-colour inversion relations at one input object. -/
def LeftwardData.IsInverseAt (L : P.LeftwardData) (c : P.CrossCoeff)
    (t : Sector I) (Z : P.H t) : Prop :=
  ∀ r : SKM.Rel D, relGroup r = .inversion → ¬ IsInvNe r → ∀ {s : Sector I}
    (p : SPath ((SKM.pres D Sc).dom r).word s t)
    (q : SPath ((SKM.pres D Sc).cod r).word s t),
    P.wt t = ((SKM.pres D Sc).dom r).endR →
      compEval (P.swappedGens c L) ((SKM.pres D Sc).rel r) p q Z = 0

/-- The local five identities give the presentation's ten equal-colour
inversion relations at the same input, including height zero. -/
theorem LeftwardData.isInverseAt_of_posInverseAt_negInverseAt
    (c : P.CrossCoeff) (L : P.LeftwardData) (t : Sector I) (Z : P.H t)
    (hpos : ∀ i ν, 0 ≤ D.h i ν → ∀ s, P.wt t = ν → P.PosInverseAt c i ν s t Z
      (fun q p => L.lcrossSame i ν q p Z) (fun n r p => L.dcup i n ν r p Z))
    (hneg : ∀ i ν, D.h i ν < 0 → ∀ s, P.wt t = ν → P.NegInverseAt c i ν s t Z
      (fun q p => L.lcrossSame i ν q p Z) (fun n q r => L.dcap i n ν q r Z)) :
    L.IsInverseAt c t Z := by
  intro r hr hne s p q hw
  let gens := P.swappedGens c L
  cases r with
  | invP₁ i ν hh =>
    show compEval gens (a := SKM.ob D ν [up i, dn i]) (b := SKM.ob D ν [up i, dn i])
      (SKM.relation D Sc (.invP₁ i ν hh)) p q Z = 0
    obtain ⟨h₁, -⟩ := hpos i ν hh s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_sub, compEval_add, compEval_neg, compEval_sum,
      compEval_dg_append gens ν (SKM.sigmaL i i) (SKM.lcrossL i i) (SKM.sChain_sigmaL i i)
        (SKM.sChain_lcrossL i i)]
    rw [Finset.sum_congr rfl fun n _ => compEval_dg_append gens ν (SKM.epsL i n) (SKM.dcupL i n)
      (SKM.sChain_epsL i n) (SKM.sChain_dcupL i n) p q Z]
    rw [compEval_of, sub_eq_zero, compDiag_id_eq_famDelta (_inst := Fintype.ofFinite _),
      ← h₁ p q]
    simp only [gens, compDiag_sigmaL_swappedGens, compDiag_lcrossL_swappedGens,
      compDiag_epsL_swappedGens]
    congr 1
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun r _ => ?_
    rw [compDiag_dcupL_swappedGens c L i n ν (Int.lt_toNat.mp (Finset.mem_range.mp hn))]
  | invP₂ i ν hh =>
    show compEval gens (a := SKM.ob D ν [dn i, up i]) (b := SKM.ob D ν [dn i, up i])
      (SKM.relation D Sc (.invP₂ i ν hh)) p q Z = 0
    obtain ⟨-, h₂, -⟩ := hpos i ν hh s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_add, compEval_dg_append gens ν (SKM.lcrossL i i) (SKM.sigmaL i i)
      (SKM.sChain_lcrossL i i) (SKM.sChain_sigmaL i i), compEval_of,
      compDiag_id_eq_famDelta (_inst := Fintype.ofFinite _)]
    simp only [gens, compDiag_sigmaL_swappedGens, compDiag_lcrossL_swappedGens]
    exact eq_neg_iff_add_eq_zero.mp (h₂ p q)
  | invP₃ i ν m hm =>
    show compEval gens (a := SKM.ob D ν [dn i, up i]) (b := SKM.ob D ν [])
      (SKM.relation D Sc (.invP₃ i ν m hm)) p q Z = 0
    obtain ⟨-, -, h₃, -⟩ := hpos i ν (by omega) s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_dg_append gens ν (SKM.lcrossL i i) (SKM.epsL i m) (SKM.sChain_lcrossL i i)
      (SKM.sChain_epsL i m)]
    simp only [gens, compDiag_epsL_swappedGens, compDiag_lcrossL_swappedGens]
    exact h₃ m hm p q
  | invP₄ i ν n hn =>
    show compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [dn i, up i])
      (SKM.relation D Sc (.invP₄ i ν n hn)) p q Z = 0
    obtain ⟨-, -, -, h₄, -⟩ := hpos i ν (by omega) s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_dg_append gens ν (SKM.dcupL i n) (SKM.sigmaL i i) (SKM.sChain_dcupL i n)
      (SKM.sChain_sigmaL i i)]
    simp only [gens, compDiag_sigmaL_swappedGens, compDiag_dcupL_swappedGens c L i n ν hn]
    exact h₄ n hn p q
  | invP₅ i ν m n hm hn =>
    show compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [])
      (SKM.relation D Sc (.invP₅ i ν m n hm hn)) p q Z = 0
    obtain ⟨-, -, -, -, h₅⟩ := hpos i ν (by omega) s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_sub, compEval_dg_append gens ν (SKM.dcupL i n) (SKM.epsL i m)
      (SKM.sChain_dcupL i n) (SKM.sChain_epsL i m), sub_eq_zero]
    simp only [gens, compDiag_epsL_swappedGens, compDiag_dcupL_swappedGens c L i n ν hn]
    refine (h₅ m n hm hn p q).trans ?_
    split_ifs
    · rw [compEval_of, compDiag_id_eq_famDelta (_inst := Fintype.ofFinite _)]
    · rw [compEval_zero]
  | invM₁ i ν hh =>
    show compEval gens (a := SKM.ob D ν [dn i, up i]) (b := SKM.ob D ν [dn i, up i])
      (SKM.relation D Sc (.invM₁ i ν hh)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_add, compEval_neg, compEval_sum,
      compEval_dg_append gens ν (SKM.lcrossL i i) (SKM.sigmaL i i) (SKM.sChain_lcrossL i i)
        (SKM.sChain_sigmaL i i)]
    rw [Finset.sum_congr rfl fun n _ => compEval_dg_append gens ν (SKM.dcapL i n) (SKM.etaL i n)
      (SKM.sChain_dcapL i n) (SKM.sChain_etaL i n) p q Z]
    rw [compEval_of, sub_eq_zero,
      compDiag_id_eq_famDelta (_inst := Fintype.ofFinite _)]
    simp only [gens, compDiag_sigmaL_swappedGens, compDiag_lcrossL_swappedGens,
      compDiag_etaL_swappedGens]
    rcases lt_or_eq_of_le hh with hlt | heq
    · obtain ⟨h₁, -⟩ := hneg i ν hlt s (hw.trans (SKM.ob_endR D ν _))
      rw [← h₁ p q]
      congr 1
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun r _ => ?_
      rw [compDiag_dcapL_swappedGens c L i n ν (Int.lt_toNat.mp (Finset.mem_range.mp hn))]
    · obtain ⟨-, h₂, -⟩ := hpos i ν heq.ge s (hw.trans (SKM.ob_endR D ν _))
      rw [heq, neg_zero, Int.toNat_zero, Finset.range_zero, Finset.sum_empty, add_zero]
      exact neg_eq_iff_eq_neg.mpr (h₂ p q)
  | invM₂ i ν hh =>
    show compEval gens (a := SKM.ob D ν [up i, dn i]) (b := SKM.ob D ν [up i, dn i])
      (SKM.relation D Sc (.invM₂ i ν hh)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_add, compEval_dg_append gens ν (SKM.sigmaL i i) (SKM.lcrossL i i)
      (SKM.sChain_sigmaL i i) (SKM.sChain_lcrossL i i), compEval_of,
      compDiag_id_eq_famDelta (_inst := Fintype.ofFinite _)]
    simp only [gens, compDiag_sigmaL_swappedGens, compDiag_lcrossL_swappedGens]
    rcases lt_or_eq_of_le hh with hlt | heq
    · obtain ⟨-, h₂, -⟩ := hneg i ν hlt s (hw.trans (SKM.ob_endR D ν _))
      exact eq_neg_iff_add_eq_zero.mp (h₂ p q)
    · obtain ⟨h₁, -⟩ := hpos i ν heq.ge s (hw.trans (SKM.ob_endR D ν _))
      have h := h₁ p q
      rw [heq, Int.toNat_zero, Finset.range_zero, Finset.sum_empty, add_zero] at h
      rw [← h]
      exact add_neg_cancel _
  | invM₃ i ν m hm =>
    show compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [up i, dn i])
      (SKM.relation D Sc (.invM₃ i ν m hm)) p q Z = 0
    obtain ⟨-, -, h₃, -⟩ := hneg i ν (by omega) s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_dg_append gens ν (SKM.etaL i m) (SKM.lcrossL i i) (SKM.sChain_etaL i m)
      (SKM.sChain_lcrossL i i)]
    simp only [gens, compDiag_etaL_swappedGens, compDiag_lcrossL_swappedGens]
    exact h₃ m hm p q
  | invM₄ i ν n hn =>
    show compEval gens (a := SKM.ob D ν [up i, dn i]) (b := SKM.ob D ν [])
      (SKM.relation D Sc (.invM₄ i ν n hn)) p q Z = 0
    obtain ⟨-, -, -, h₄, -⟩ := hneg i ν (by omega) s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_dg_append gens ν (SKM.sigmaL i i) (SKM.dcapL i n) (SKM.sChain_sigmaL i i)
      (SKM.sChain_dcapL i n)]
    simp only [gens, compDiag_sigmaL_swappedGens, compDiag_dcapL_swappedGens c L i n ν hn]
    exact h₄ n hn p q
  | invM₅ i ν m n hm hn =>
    show compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [])
      (SKM.relation D Sc (.invM₅ i ν m n hm hn)) p q Z = 0
    obtain ⟨-, -, -, -, h₅⟩ := hneg i ν (by omega) s (hw.trans (SKM.ob_endR D ν _))
    simp only [SKM.relation]
    rw [compEval_sub, compEval_dg_append gens ν (SKM.etaL i m) (SKM.dcapL i n)
      (SKM.sChain_etaL i m) (SKM.sChain_dcapL i n), sub_eq_zero]
    simp only [gens, compDiag_etaL_swappedGens, compDiag_dcapL_swappedGens c L i n ν hn]
    refine (h₅ m n hm hn p q).trans ?_
    split_ifs
    · rw [compEval_of, compDiag_id_eq_famDelta (_inst := Fintype.ofFinite _)]
    · rw [compEval_zero]
  | invNe₁ => exact absurd trivial hne
  | invNe₂ => exact absurd trivial hne
  | _ => exact absurd hr (by simp [relGroup])

variable (P)

/-- The conditional raw leftward data satisfy all equal-colour inversion
relations at inputs whose augmented matrices have the local inverses. -/
theorem leftwardOfPointwiseAugmentedInverse_isInverseAt (c : P.CrossCoeff)
    (t : Sector I) (Z : P.H t)
    (hpos : ∀ i ν, 0 ≤ D.h i ν → ∀ s, P.wt t = ν →
      IsIso (P.augPosMat c i ν s t Z))
    (hneg : ∀ i ν, D.h i ν < 0 → ∀ s, P.wt t = ν →
      IsIso (P.augNegMat c i ν s t Z)) :
    (P.leftwardOfPointwiseAugmentedInverse c).IsInverseAt c t Z := by
  apply LeftwardData.isInverseAt_of_posInverseAt_negInverseAt
  · intro i ν hh s hw
    let := hpos i ν hh s hw
    exact P.leftwardOfPointwiseAugmentedInverse_posInverseAt c i ν s t Z hw hh
  · intro i ν hh s hw
    let := hneg i ν hh s hw
    exact P.leftwardOfPointwiseAugmentedInverse_negInverseAt c i ν s t Z hw hh

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
