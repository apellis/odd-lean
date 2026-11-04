import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedMatrix

/-! # Augmented matrices between distinct formal sectors

Brundan–Ellis (1.13)–(1.14), `SwappedHomInversion.md` §2: between
distinct sectors there are no dotted identity-window paths. The whole
augmented matrix is therefore the invertible swapping entry (or its
negative), with its literal finite-family indexing retained.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct

section Families
variable {C : Type*} [Category C] [Preadditive C]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A two-sided inverse family gives an isomorphism of the literal finite matrices. -/
theorem isIso_famHom_of_inverse {Xa : α → C} {Yb : β → C}
    (a : ∀ x y, Xa x ⟶ Yb y) (b : ∀ y x, Yb y ⟶ Xa x)
    (hab : ∀ x x', ∑ y, a x y ≫ b y x' = famId Xa x x')
    (hba : ∀ y y', ∑ x, b y x ≫ a x y' = famId Yb y y') :
    IsIso (famHom a) := by
  refine ⟨⟨famHom b, ?_, ?_⟩⟩
  · apply Mat_.hom_ext
    intro i j
    rw [Mat_.comp_apply, Mat_.id_apply]
    change (∑ y, a ((Fintype.equivFin α).symm i) ((Fintype.equivFin β).symm y) ≫
      b ((Fintype.equivFin β).symm y) ((Fintype.equivFin α).symm j)) = _
    rw [Equiv.sum_comp (Fintype.equivFin β).symm
      (fun y => a ((Fintype.equivFin α).symm i) y ≫ b y ((Fintype.equivFin α).symm j)), hab]
    by_cases hij : i = j
    · subst hij; simp
    · rw [famId_of_ne _ (fun h => hij ((Fintype.equivFin α).symm.injective h))]
      simp [hij]
  · apply Mat_.hom_ext
    intro i j
    rw [Mat_.comp_apply, Mat_.id_apply]
    change (∑ x, b ((Fintype.equivFin β).symm i) ((Fintype.equivFin α).symm x) ≫
      a ((Fintype.equivFin α).symm x) ((Fintype.equivFin β).symm j)) = _
    rw [Equiv.sum_comp (Fintype.equivFin α).symm
      (fun x => b ((Fintype.equivFin β).symm i) x ≫ a x ((Fintype.equivFin β).symm j)), hba]
    by_cases hij : i = j
    · subst hij; simp
    · rw [famId_of_ne _ (fun h => hij ((Fintype.equivFin β).symm.injective h))]
      simp [hij]
end Families

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- The positive off-central augmented matrix uses only the local swapping units. -/
theorem isIso_augPosMat_of_ne (c : P.CrossCoeff) (i : I) (ν : X)
    {t s : Sector I} (hts : t ≠ s) (Z : P.H s)
    (hσ : ∀ (p : SPath (wd D ν [up i,dn i]) t s)
      (q : SPath (wd D ν [dn i,up i]) t s), IsIso (P.sigmaEntry c i i ν p q Z)) :
    IsIso (P.augPosMat c i ν t s Z) := by
  classical
  let : Subsingleton (SPath (wd D ν [up i,dn i]) t s) := SPath.subsingleton_upDn_self hts _ _
  let : Subsingleton (SPath (wd D ν [dn i,up i]) t s) := SPath.subsingleton_dnUp_self hts _ _
  let : IsEmpty (SPath (wd D ν []) t s) := SPath.isEmpty_nil_of_ne hts
  let := Fintype.ofFinite (SPath (wd D ν [up i,dn i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν [dn i,up i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν []) t s)
  let (p : SPath (wd D ν [up i,dn i]) t s) (q : SPath (wd D ν [dn i,up i]) t s) :
      IsIso (P.sigmaEntry c i i ν p q Z) := hσ p q
  have hne : Nonempty (SPath (wd D ν [up i,dn i]) t s) ↔
      Nonempty (SPath (wd D ν [dn i,up i]) t s) :=
    SPath.nonempty_dnUp_self_iff hts _ _ _ _
  let a : ∀ (p : SPath (wd D ν [up i,dn i]) t s)
      (y : SPath (wd D ν [dn i,up i]) t s ⊕
        (Fin (D.h i ν).toNat × SPath (wd D ν []) t s)),
      (P.pathFunctor p).obj Z ⟶ (Sum.elim (fun q => (P.pathFunctor q).obj Z)
        (fun nr => (P.pathFunctor nr.2).obj Z)) y := fun p y => match y with
    | .inl q => P.sigmaEntry c i i ν p q Z
    | .inr nr => P.epsEntry c i nr.1 ν p nr.2 Z
  let b : ∀ y p, (Sum.elim (fun q => (P.pathFunctor q).obj Z)
      (fun nr : Fin (D.h i ν).toNat × SPath (wd D ν []) t s =>
        (P.pathFunctor nr.2).obj Z)) y ⟶ (P.pathFunctor p).obj Z :=
    fun y p => match y with
    | .inl q => inv (P.sigmaEntry c i i ν p q Z)
    | .inr nr => isEmptyElim nr.2
  change IsIso (famHom a)
  apply isIso_famHom_of_inverse a b
  · intro p p'
    obtain rfl := Subsingleton.elim p p'
    obtain ⟨q⟩ := hne.1 ⟨p⟩
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    dsimp only [a, b]
    rw [Finset.sum_eq_zero (fun _ _ => Fintype.sum_empty _), add_zero,
      Fintype.sum_subsingleton _ q, IsIso.hom_inv_id, famId_self]
  · rintro (q | ⟨n,r⟩) (q' | ⟨n',r'⟩)
    · obtain rfl := Subsingleton.elim q q'
      obtain ⟨p⟩ := hne.2 ⟨q⟩
      rw [Fintype.sum_subsingleton _ p]
      exact (IsIso.inv_hom_id _).trans (famId_self _ _).symm
    · exact isEmptyElim r'
    · exact isEmptyElim r
    · exact isEmptyElim r

/-- The negative off-central augmented matrix retains the prescribed principal minus. -/
theorem isIso_augNegMat_of_ne (c : P.CrossCoeff) (i : I) (ν : X)
    {t s : Sector I} (hts : t ≠ s) (Z : P.H s)
    (hσ : ∀ (p : SPath (wd D ν [up i,dn i]) t s)
      (q : SPath (wd D ν [dn i,up i]) t s), IsIso (P.sigmaEntry c i i ν p q Z)) :
    IsIso (P.augNegMat c i ν t s Z) := by
  classical
  let : Subsingleton (SPath (wd D ν [up i,dn i]) t s) := SPath.subsingleton_upDn_self hts _ _
  let : Subsingleton (SPath (wd D ν [dn i,up i]) t s) := SPath.subsingleton_dnUp_self hts _ _
  let : IsEmpty (SPath (wd D ν []) t s) := SPath.isEmpty_nil_of_ne hts
  let := Fintype.ofFinite (SPath (wd D ν [up i,dn i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν [dn i,up i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν []) t s)
  let (p : SPath (wd D ν [up i,dn i]) t s) (q : SPath (wd D ν [dn i,up i]) t s) :
      IsIso (P.sigmaEntry c i i ν p q Z) := hσ p q
  have hne : Nonempty (SPath (wd D ν [up i,dn i]) t s) ↔
      Nonempty (SPath (wd D ν [dn i,up i]) t s) :=
    SPath.nonempty_dnUp_self_iff hts _ _ _ _
  let a : ∀ (y : SPath (wd D ν [up i,dn i]) t s ⊕
        (Fin (-D.h i ν).toNat × SPath (wd D ν []) t s))
      (q : SPath (wd D ν [dn i,up i]) t s),
      (Sum.elim (fun p => (P.pathFunctor p).obj Z)
        (fun nr => (P.pathFunctor nr.2).obj Z)) y ⟶ (P.pathFunctor q).obj Z :=
    fun y q => match y with
    | .inl p => -P.sigmaEntry c i i ν p q Z
    | .inr nr => P.etaEntry c i nr.1 ν nr.2 q Z
  let b : ∀ q y, (P.pathFunctor q).obj Z ⟶
      (Sum.elim (fun p => (P.pathFunctor p).obj Z)
        (fun nr : Fin (-D.h i ν).toNat × SPath (wd D ν []) t s =>
          (P.pathFunctor nr.2).obj Z)) y :=
    fun q y => match y with
    | .inl p => -inv (P.sigmaEntry c i i ν p q Z)
    | .inr nr => isEmptyElim nr.2
  change IsIso (famHom a)
  apply isIso_famHom_of_inverse a b
  · rintro (p | ⟨n,r⟩) (p' | ⟨n',r'⟩)
    · obtain rfl := Subsingleton.elim p p'
      obtain ⟨q⟩ := hne.1 ⟨p⟩
      rw [Fintype.sum_subsingleton _ q]
      dsimp only [a, b]
      rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, IsIso.hom_inv_id, famId_self]
    · exact isEmptyElim r'
    · exact isEmptyElim r
    · exact isEmptyElim r
  · intro q q'
    obtain rfl := Subsingleton.elim q q'
    obtain ⟨p⟩ := hne.2 ⟨q⟩
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    dsimp only [a, b]
    rw [Finset.sum_eq_zero (fun _ _ => Fintype.sum_empty _), add_zero,
      Fintype.sum_subsingleton _ p, Preadditive.neg_comp, Preadditive.comp_neg,
      neg_neg, IsIso.inv_hom_id, famId_self]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
