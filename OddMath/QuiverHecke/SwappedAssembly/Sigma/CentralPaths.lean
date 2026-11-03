import OddMath.QuiverHecke.SwappedAssembly.Sigma.SameColourBlocks

/-! # Pure paths in a central equal-colour block

The path indices in Brundan–Ellis (1.13)–(1.14), at equal outer sectors,
are precisely the valid pure reservoir and pure probe paths. The validity
subtypes retain an absent reservoir source or probe target without adding
a path-existence hypothesis. These indices are used by the two-sector
matrix chart of `SwappedHomInversion` §§3–6.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.SPath
open OddMath.SKM
universe u
variable {I X : Type u}

/-- The first summand of a nonempty path. -/
def firstSide {c : Col I X} {w : List (Col I X)} {t s : Sector I} :
    SPath (c :: w) t s → Bool
  | .cons _ a _ _ _ => a

/-- The first summand of a path satisfies its content condition. -/
theorem firstSide_valid {c : Col I X} {w : List (Col I X)} {t s : Sector I}
    (p : SPath (c :: w) t s) : StepValid c.l p.firstSide t := by
  cases p with | cons _ _ _ hv _ => exact hv

/-- A central equal-colour path cannot mix probe and reservoir summands. -/
theorem sides_eq_of_roundtrip {i : I} {t : Sector I} (upFirst a b : Bool)
    (h : nextSector (!upFirst, i) b (nextSector (upFirst, i) a t) = t) : a = b := by
  have hP := congrArg (fun s : Sector I => s.1 i) h
  have hR := congrArg (fun s : Sector I => s.2 i) h
  cases upFirst <;> cases a <;> cases b <;>
    simp only [Bool.not_false, Bool.not_true, nextSector, Finsupp.coe_add,
      Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same, Prod.fst, Prod.snd] at hP hR <;>
    first | rfl | omega

/-- The pure source path, for either valid first summand of `EᵢFᵢ`. -/
def centralUpDn (i : I) (r r' : X) (t : Sector I)
    (a : {a : Bool // StepValid (up i) a t}) :
    SPath [⟨up i, r⟩, ⟨dn i, r'⟩] t t :=
  two a a a.property (by
    rcases a with ⟨a, ha⟩
    cases a
    · trivial
    · simp [StepValid, nextSector]) (by
    rcases a with ⟨a, ha⟩
    cases a
    · exact next_upDn_false_false ha
    · exact next_upDn_true_true t)

/-- The pure target path, for either valid first summand of `FᵢEᵢ`. -/
def centralDnUp (i : I) (r r' : X) (t : Sector I)
    (a : {a : Bool // StepValid (dn i) a t}) :
    SPath [⟨dn i, r⟩, ⟨up i, r'⟩] t t :=
  two a a a.property (by
    rcases a with ⟨a, ha⟩
    cases a
    · simp [StepValid, nextSector]
    · trivial) (by
    rcases a with ⟨a, ha⟩
    cases a
    · exact next_dnUp_false_false t
    · exact next_dnUp_true_true ha)

/-- Every source path, including boundary sectors, is a valid pure path. -/
def centralUpDnEquiv (i : I) (r r' : X) (t : Sector I) :
    SPath [⟨up i, r⟩, ⟨dn i, r'⟩] t t ≃ {a : Bool // StepValid (up i) a t} where
  toFun p := ⟨p.firstSide, p.firstSide_valid⟩
  invFun := centralUpDn i r r' t
  left_inv p := by
    obtain ⟨a, b, ha, hb, h, rfl⟩ := exists_eq_two p
    have hab := sides_eq_of_roundtrip true a b h
    subst b
    apply eq_of_sides
    change (centralUpDn i r r' t ⟨a, ha⟩).sides = (two a a ha hb h).sides
    simp only [centralUpDn, sides_two]
  right_inv a := by
    apply Subtype.ext
    rfl

/-- Every target path, including boundary sectors, is a valid pure path. -/
def centralDnUpEquiv (i : I) (r r' : X) (t : Sector I) :
    SPath [⟨dn i, r⟩, ⟨up i, r'⟩] t t ≃ {a : Bool // StepValid (dn i) a t} where
  toFun p := ⟨p.firstSide, p.firstSide_valid⟩
  invFun := centralDnUp i r r' t
  left_inv p := by
    obtain ⟨a, b, ha, hb, h, rfl⟩ := exists_eq_two p
    have hab := sides_eq_of_roundtrip false a b h
    subst b
    apply eq_of_sides
    change (centralDnUp i r r' t ⟨a, ha⟩).sides = (two a a ha hb h).sides
    simp only [centralDnUp, sides_two]
  right_inv a := by
    apply Subtype.ext
    rfl

/-- The window path has exactly one index even when a pure corner is absent. -/
def centralNilEquiv (t : Sector I) : SPath ([] : List (Col I X)) t t ≃ Unit where
  toFun _ := ()
  invFun _ := .nil t
  left_inv p := by cases p; rfl
  right_inv a := by cases a; rfl

end OddMath.QuiverHecke.SwappedAssembly.SPath
