import OddMath.SKM.SourceCapAttachment

/-! Concrete checks of fresh IDs, the isolated cap, and later residual joins. -/
noncomputable section
namespace OddMath.SKM.SourceCapAttachmentExamples
open StringDiagrams StringDiagrams.Chord SourceCapAttachment

private def up : Letter Unit := (true, ())
private def dn : Letter Unit := (false, ())

/-- A residual cup starts at ID four, not two, after the isolated cap. -/
example :
    (tRun flipL 2 (tStart [dn, up]) [.cap 0, .mv (.cup 0 up)]).st =
      [(2, dn), (2, up), (4, up), (4, dn)] := by decide

example :
    (tRun flipL 2 (tStart [dn, up]) [.cap 0, .mv (.cup 0 up)]).nxt = 5 := by decide

/-- A later cap joins residual IDs across the inserted pair while leaving its ID fixed. -/
example :
    (tRun flipL 4 (tStart [up, dn, up, dn]) [.cap 1, .cap 0]).st =
      [(6, up), (4, dn), (4, up), (6, dn)] := by decide

example : critPts₂ [up, dn, up, dn] [.cap 1, .cap 0] = [4, 6] := by decide

/-- Attachment works with an arbitrary target and inherited serializer. -/
example {I : Type*} {L Q Z : List (Letter I)} (x : Letter I)
    (F : PointedMatching (L ++ Q) Z) :
    PointedMatching (L ++ flipL x :: x :: Q) Z := attach x F

end OddMath.SKM.SourceCapAttachmentExamples
