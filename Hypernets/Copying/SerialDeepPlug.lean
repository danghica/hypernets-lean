import Hypernets.Copying.SerialPlug
import Hypernets.Copying.SingleHole

/-! Replacement below boxes commutes with the original serial assembly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Serial
open Graph

/-- Changing a left component's box body commutes with serial assembly. -/
noncomputable def replaceBox_left {d I J K} (G : Hypernet (d+1) I J) (H : Hypernet (d+1) J K)
    (e : G.Edge) (b : Box (alphabet d)) (label : G.edgeLabel e = .inr b)
    (A : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)) :
    Net.Iso (replaceBox (net G H) (leftEdge G H e) b ((leftEdge_label G H e).trans label) A)
      (net (replaceBox G e b label A) H) where
  vertices := {
    toFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
    invFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
    left_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl
    right_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl }
  edges := {
    toFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    invFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    left_inv := by rintro ⟨a,f⟩; cases a <;> rfl
    right_inv := by rintro ⟨a,f⟩; cases a <;> rfl }
  internal_label v := by rcases v with v | ⟨a,v⟩; rfl; cases a <;> rfl
  edge_label x := by
    classical
    rcases x with ⟨a,f⟩
    cases a
    · by_cases eq : f = e
      · subst f; simp [replaceBox,Net.relabelEdges,leftEdge,net,Net.expand,Net.Expansion.edgeLabel,filling]
      · simp [replaceBox,Net.relabelEdges,leftEdge,net,Net.expand,Net.Expansion.edgeLabel,filling,eq]
    · simp [replaceBox,Net.relabelEdges,leftEdge,net,Net.expand,Net.Expansion.edgeLabel,filling]
  source x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.source f).map _).map _ = (G.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]
    · change ((H.source f).map _).map _ = (H.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]
  target x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.target f).map _).map _ = (G.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]
    · change ((H.target f).map _).map _ = (H.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]

/-- Changing a right component's box body commutes with serial assembly. -/
noncomputable def replaceBox_right {d I J K} (G : Hypernet (d+1) I J) (H : Hypernet (d+1) J K)
    (e : H.Edge) (b : Box (alphabet d)) (label : H.edgeLabel e = .inr b)
    (A : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)) :
    Net.Iso (replaceBox (net G H) (rightEdge G H e) b ((rightEdge_label G H e).trans label) A)
      (net G (replaceBox H e b label A)) where
  vertices := {
    toFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
    invFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
    left_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl
    right_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl }
  edges := {
    toFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    invFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    left_inv := by rintro ⟨a,f⟩; cases a <;> rfl
    right_inv := by rintro ⟨a,f⟩; cases a <;> rfl }
  internal_label v := by rcases v with v | ⟨a,v⟩; rfl; cases a <;> rfl
  edge_label x := by
    classical
    rcases x with ⟨a,f⟩
    cases a
    · simp [replaceBox,Net.relabelEdges,rightEdge,net,Net.expand,Net.Expansion.edgeLabel,filling]
    · by_cases eq : f = e
      · subst f; simp [replaceBox,Net.relabelEdges,rightEdge,net,Net.expand,Net.Expansion.edgeLabel,filling]
      · simp [replaceBox,Net.relabelEdges,rightEdge,net,Net.expand,Net.Expansion.edgeLabel,filling,eq]
  source x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.source f).map _).map _ = (G.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]
    · change ((H.source f).map _).map _ = (H.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]
  target x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.target f).map _).map _ = (G.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]
    · change ((H.target f).map _).map _ = (H.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,pattern,List.getElem_map,Port.map]

/-- Retain an arbitrary-depth address in the left component. -/
def leftSite {d I J K} {G : Hypernet d I J} (H : Hypernet d J K) {r U V}
    (s : Site G r U V) : Site (net G H) r U V := by
  cases s with
  | shallow G e =>
    exact (Site.shallow (net G H) (leftEdge G H e)).castInterfaces
      (congrArg _ (leftEdge_label G H e)) (congrArg _ (leftEdge_label G H e))
  | inside e b label inner => exact .inside (leftEdge G H e) b ((leftEdge_label G H e).trans label) inner

/-- Retain an arbitrary-depth address in the right component. -/
def rightSite {d I J K} (G : Hypernet d I J) {H : Hypernet d J K} {r U V}
    (s : Site H r U V) : Site (net G H) r U V := by
  cases s with
  | shallow H e =>
    exact (Site.shallow (net G H) (rightEdge G H e)).castInterfaces
      (congrArg _ (rightEdge_label G H e)) (congrArg _ (rightEdge_label G H e))
  | inside e b label inner => exact .inside (rightEdge G H e) b ((rightEdge_label G H e).trans label) inner

/-- Arbitrary-depth addressed replacement commutes with left serial assembly. -/
noncomputable def plugAt_left {d I J K} {G : Hypernet d I J} (H : Hypernet d J K)
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (leftSite H s) A) (net (plugAt s A) H) := by
  cases s with
  | @shallow d I J G e =>
    cases d <;> simpa only [leftSite,Site.castInterfaces,plugAt,Net.reboundary_refl]
      using DeepIso.ofIso (plug_left G H e A)
  | inside e b label inner => exact DeepIso.ofIso (replaceBox_left _ H e b label (plugAt inner A))

/-- Arbitrary-depth addressed replacement commutes with right serial assembly. -/
noncomputable def plugAt_right {d I J K} (G : Hypernet d I J) {H : Hypernet d J K}
    {r U V} (s : Site H r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (rightSite G s) A) (net G (plugAt s A)) := by
  cases s with
  | @shallow d J K H e =>
    cases d <;> simpa only [rightSite,Site.castInterfaces,plugAt,Net.reboundary_refl]
      using DeepIso.ofIso (plug_right G H e A)
  | inside e b label inner => exact DeepIso.ofIso (replaceBox_right G _ e b label (plugAt inner A))

/-- Hole-free labels outside the selected left edge remain hole-free. -/
theorem left_other_free {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (e : G.Edge)
    (others : ∀ f, f ≠ e → LabelAll (fun p => ∀ q, p ≠ .hole q) d (G.edgeLabel f))
    (free : HoleFree H) : ∀ f, f ≠ leftEdge G H e →
      LabelAll (fun p => ∀ q, p ≠ .hole q) d ((net G H).edgeLabel f) := by
  cases d <;> rintro ⟨a,f⟩ ne <;> cases a
  all_goals first
    | exact free f
    | exact others f (fun eq => ne (by subst f; rfl))

/-- Hole-free labels outside the selected right edge remain hole-free. -/
theorem right_other_free {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (e : H.Edge)
    (free : HoleFree G)
    (others : ∀ f, f ≠ e → LabelAll (fun p => ∀ q, p ≠ .hole q) d (H.edgeLabel f)) :
    ∀ f, f ≠ rightEdge G H e → LabelAll (fun p => ∀ q, p ≠ .hole q) d ((net G H).edgeLabel f) := by
  cases d <;> rintro ⟨a,f⟩ ne <;> cases a
  all_goals first
    | exact free f
    | exact others f (fun eq => ne (by subst f; rfl))

/-- The lifted left address stays sole when the right component is hole-free. -/
theorem leftSite_sole {d I J K} {G : Hypernet d I J} (H : Hypernet d J K)
    (free : HoleFree H) {r U V} (s : Site G r U V) (sole : SoleHole s) :
    SoleHole (leftSite H s) := by
  cases s with
  | @shallow d I J G e =>
    cases d <;> change SoleHole (Site.shallow (net G H) (leftEdge G H e))
    all_goals
      obtain ⟨⟨q,eq⟩,others⟩ := sole
      exact ⟨⟨q,(leftEdge_label G H e).trans eq⟩,left_other_free G H e others free⟩
  | inside e b label inner => exact ⟨sole.1,left_other_free _ H e sole.2 free⟩

/-- The lifted right address stays sole when the left component is hole-free. -/
theorem rightSite_sole {d I J K} (G : Hypernet d I J) {H : Hypernet d J K}
    (free : HoleFree G) {r U V} (s : Site H r U V) (sole : SoleHole s) :
    SoleHole (rightSite G s) := by
  cases s with
  | @shallow d J K H e =>
    cases d <;> change SoleHole (Site.shallow (net G H) (rightEdge G H e))
    all_goals
      obtain ⟨⟨q,eq⟩,others⟩ := sole
      exact ⟨⟨q,(rightEdge_label G H e).trans eq⟩,right_other_free G H e free others⟩
  | inside e b label inner => exact ⟨sole.1,right_other_free G _ e free sole.2⟩
end Hypernets.Copying.Serial
