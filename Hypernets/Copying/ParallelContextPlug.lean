import Hypernets.Graph.ParallelPlug
import Hypernets.Graph.ParallelIso
import Hypernets.Copying.BoxContextPlug

/-! Deep addressed filling in two parallel components with arbitrary boundary order. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ParallelPair
open Graph
variable {I J K L P Q : List Wire}
    (B : Net.Parallel.Boundary (Net.Tensor.interfaces I K) (Net.Tensor.interfaces J L) P Q)

/-- The original ordered parallel graph, with a fixed two-component enumeration. -/
abbrev net {d} (G : Hypernet d I J) (H : Hypernet d K L) : Hypernet d P Q :=
  Net.Parallel.net (Net.Tensor.family G H) B ⟨[false,true],by intro b; cases b <;> simp⟩

def leftEdge {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : G.Edge) : (net B G H).Edge := ⟨false,e⟩
def rightEdge {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : H.Edge) : (net B G H).Edge := ⟨true,e⟩

theorem leftEdge_label {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : G.Edge) :
    (net B G H).edgeLabel (leftEdge B G H e) = G.edgeLabel e := rfl

theorem rightEdge_label {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : H.Edge) :
    (net B G H).edgeLabel (rightEdge B G H e) = H.edgeLabel e := rfl

/-- Shallow replacement in the left component preserves the chosen boundary order. -/
noncomputable def plug_left {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : G.Edge)
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e))) :
    Net.Iso ((net B G H).plug (leftEdge B G H e) A) (net B (G.plug e A) H) := by
  classical
  have eq : Net.ParallelPlug.family (Net.Tensor.family G H) false e A = Net.Tensor.family (G.plug e A) H := by
    funext b; cases b <;> simp [Net.ParallelPlug.family,Net.Tensor.family]
  simpa only [eq,leftEdge,rightEdge,net] using Net.ParallelPlug.iso (Net.Tensor.family G H) false e A B
    ⟨[false,true],by intro b; cases b <;> simp⟩

/-- Shallow replacement in the right component preserves the chosen boundary order. -/
noncomputable def plug_right {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : H.Edge)
    (A : Hypernet d ((alphabet d).signature.input (H.edgeLabel e))
      ((alphabet d).signature.output (H.edgeLabel e))) :
    Net.Iso ((net B G H).plug (rightEdge B G H e) A) (net B G (H.plug e A)) := by
  classical
  have eq : Net.ParallelPlug.family (Net.Tensor.family G H) true e A = Net.Tensor.family G (H.plug e A) := by
    funext b; cases b <;> simp [Net.ParallelPlug.family,Net.Tensor.family]
  simpa only [eq,leftEdge,rightEdge,net] using Net.ParallelPlug.iso (Net.Tensor.family G H) true e A B
    ⟨[false,true],by intro b; cases b <;> simp⟩

/-- Component-wise recursive isomorphisms preserve the ordered parallel graph. -/
def congr {d} {G G' : Hypernet d I J} {H H' : Hypernet d K L}
    (f : DeepIso G G') (g : DeepIso H H') : DeepIso (net B G H) (net B G' H') :=
  Net.ParallelIso.iso (fun b => match b with | false => f | true => g) B
    ⟨[false,true],by intro b; cases b <;> simp⟩

/-- Changing a left component's box body commutes with parallel assembly. -/
noncomputable def replaceBox_left {d} (G : Hypernet (d+1) I J) (H : Hypernet (d+1) K L)
    (e : G.Edge) (b : Box (alphabet d)) (label : G.edgeLabel e = .inr b)
    (A : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)) :
    Net.Iso (replaceBox (net B G H) (leftEdge B G H e) b ((leftEdge_label B G H e).trans label) A)
      (net B (replaceBox G e b label A) H) where
  vertices := {
    toFun := fun | ⟨false,v⟩ => ⟨false,v⟩ | ⟨true,v⟩ => ⟨true,v⟩
    invFun := fun | ⟨false,v⟩ => ⟨false,v⟩ | ⟨true,v⟩ => ⟨true,v⟩
    left_inv := by rintro ⟨a,v⟩; cases a <;> rfl
    right_inv := by rintro ⟨a,v⟩; cases a <;> rfl }
  edges := {
    toFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    invFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    left_inv := by rintro ⟨a,f⟩; cases a <;> rfl
    right_inv := by rintro ⟨a,f⟩; cases a <;> rfl }
  internal_label v := by rcases v with ⟨a,v⟩; cases a <;> rfl
  edge_label x := by
    classical
    rcases x with ⟨a,f⟩
    cases a
    · by_cases eq : f = e
      · subst f; simp [replaceBox,Net.relabelEdges,leftEdge,net,Net.Parallel.net,Net.Tensor.family]
      · simp [replaceBox,Net.relabelEdges,leftEdge,net,Net.Parallel.net,Net.Tensor.family,eq]
    · simp [replaceBox,Net.relabelEdges,leftEdge,net,Net.Parallel.net,Net.Tensor.family]
  source x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.source f).map _).map _ = (G.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    · change ((H.source f).map _).map _ = (H.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
  target x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.target f).map _).map _ = (G.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    · change ((H.target f).map _).map _ = (H.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl

/-- Changing a right component's box body commutes with parallel assembly. -/
noncomputable def replaceBox_right {d} (G : Hypernet (d+1) I J) (H : Hypernet (d+1) K L)
    (e : H.Edge) (b : Box (alphabet d)) (label : H.edgeLabel e = .inr b)
    (A : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)) :
    Net.Iso (replaceBox (net B G H) (rightEdge B G H e) b ((rightEdge_label B G H e).trans label) A)
      (net B G (replaceBox H e b label A)) where
  vertices := {
    toFun := fun | ⟨false,v⟩ => ⟨false,v⟩ | ⟨true,v⟩ => ⟨true,v⟩
    invFun := fun | ⟨false,v⟩ => ⟨false,v⟩ | ⟨true,v⟩ => ⟨true,v⟩
    left_inv := by rintro ⟨a,v⟩; cases a <;> rfl
    right_inv := by rintro ⟨a,v⟩; cases a <;> rfl }
  edges := {
    toFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    invFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
    left_inv := by rintro ⟨a,f⟩; cases a <;> rfl
    right_inv := by rintro ⟨a,f⟩; cases a <;> rfl }
  internal_label v := by rcases v with ⟨a,v⟩; cases a <;> rfl
  edge_label x := by
    classical
    rcases x with ⟨a,f⟩
    cases a
    · simp [replaceBox,Net.relabelEdges,rightEdge,net,Net.Parallel.net,Net.Tensor.family]
    · by_cases eq : f = e
      · subst f; simp [replaceBox,Net.relabelEdges,rightEdge,net,Net.Parallel.net,Net.Tensor.family]
      · simp [replaceBox,Net.relabelEdges,rightEdge,net,Net.Parallel.net,Net.Tensor.family,eq]
  source x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.source f).map _).map _ = (G.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    · change ((H.source f).map _).map _ = (H.source f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
  target x := by
    rcases x with ⟨a,f⟩
    cases a
    · change ((G.target f).map _).map _ = (G.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    · change ((H.target f).map _).map _ = (H.target f).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl

/-- Retain an arbitrary-depth address in the left component. -/
def leftSite {d} {G : Hypernet d I J} (H : Hypernet d K L) {r U V}
    (s : Site G r U V) : Site (net B G H) r U V := by
  cases s with
  | shallow G e =>
    exact (Site.shallow (net B G H) (leftEdge B G H e)).castInterfaces
      (congrArg _ (leftEdge_label B G H e)) (congrArg _ (leftEdge_label B G H e))
  | inside e b label inner => exact .inside (leftEdge B G H e) b ((leftEdge_label B G H e).trans label) inner

/-- Retain an arbitrary-depth address in the right component. -/
def rightSite {d} (G : Hypernet d I J) {H : Hypernet d K L} {r U V}
    (s : Site H r U V) : Site (net B G H) r U V := by
  cases s with
  | shallow H e =>
    exact (Site.shallow (net B G H) (rightEdge B G H e)).castInterfaces
      (congrArg _ (rightEdge_label B G H e)) (congrArg _ (rightEdge_label B G H e))
  | inside e b label inner => exact .inside (rightEdge B G H e) b ((rightEdge_label B G H e).trans label) inner

/-- Arbitrary-depth addressed replacement commutes with left parallel assembly. -/
noncomputable def plugAt_left {d} {G : Hypernet d I J} (H : Hypernet d K L)
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (leftSite B H s) A) (net B (plugAt s A) H) := by
  cases s with
  | shallow G e =>
    simpa only [leftSite,Site.castInterfaces,plugAt]
      using DeepIso.ofIso (plug_left B G H e A)
  | inside e b label inner => exact DeepIso.ofIso (replaceBox_left B _ H e b label (plugAt inner A))

/-- Arbitrary-depth addressed replacement commutes with right parallel assembly. -/
noncomputable def plugAt_right {d} (G : Hypernet d I J) {H : Hypernet d K L}
    {r U V} (s : Site H r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (rightSite B G s) A) (net B G (plugAt s A)) := by
  cases s with
  | shallow H e =>
    simpa only [rightSite,Site.castInterfaces,plugAt]
      using DeepIso.ofIso (plug_right B G H e A)
  | inside e b label inner => exact DeepIso.ofIso (replaceBox_right B G _ e b label (plugAt inner A))

/-- Hole-free labels outside the selected left edge remain hole-free. -/
theorem left_other_free {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : G.Edge)
    (others : ∀ f, f ≠ e → LabelAll (fun p => ∀ q, p ≠ .hole q) d (G.edgeLabel f))
    (free : HoleFree H) : ∀ f, f ≠ leftEdge B G H e →
      LabelAll (fun p => ∀ q, p ≠ .hole q) d ((net B G H).edgeLabel f) := by
  rintro ⟨a,f⟩ ne; cases a
  all_goals first
    | exact free f
    | exact others f (fun eq => ne (by subst f; rfl))

/-- Hole-free labels outside the selected right edge remain hole-free. -/
theorem right_other_free {d} (G : Hypernet d I J) (H : Hypernet d K L) (e : H.Edge)
    (free : HoleFree G)
    (others : ∀ f, f ≠ e → LabelAll (fun p => ∀ q, p ≠ .hole q) d (H.edgeLabel f)) :
    ∀ f, f ≠ rightEdge B G H e → LabelAll (fun p => ∀ q, p ≠ .hole q) d ((net B G H).edgeLabel f) := by
  rintro ⟨a,f⟩ ne; cases a
  all_goals first
    | exact free f
    | exact others f (fun eq => ne (by subst f; rfl))

/-- The lifted left address stays sole when the right component is hole-free. -/
theorem leftSite_sole {d} {G : Hypernet d I J} (H : Hypernet d K L)
    (free : HoleFree H) {r U V} (s : Site G r U V) (sole : SoleHole s) :
    SoleHole (leftSite B H s) := by
  cases s with
  | shallow G e =>
    change SoleHole (Site.shallow (net B G H) (leftEdge B G H e))
    all_goals
      obtain ⟨⟨q,eq⟩,others⟩ := sole
      exact ⟨⟨q,(leftEdge_label B G H e).trans eq⟩,left_other_free B G H e others free⟩
  | inside e b label inner => exact ⟨sole.1,left_other_free B _ H e sole.2 free⟩

/-- The lifted right address stays sole when the left component is hole-free. -/
theorem rightSite_sole {d} (G : Hypernet d I J) {H : Hypernet d K L}
    (free : HoleFree G) {r U V} (s : Site H r U V) (sole : SoleHole s) :
    SoleHole (rightSite B G s) := by
  cases s with
  | shallow H e =>
    change SoleHole (Site.shallow (net B G H) (rightEdge B G H e))
    all_goals
      obtain ⟨⟨q,eq⟩,others⟩ := sole
      exact ⟨⟨q,(rightEdge_label B G H e).trans eq⟩,right_other_free B G H e free others⟩
  | inside e b label inner => exact ⟨sole.1,right_other_free B G _ e free sole.2⟩
end Hypernets.Copying.ParallelPair
