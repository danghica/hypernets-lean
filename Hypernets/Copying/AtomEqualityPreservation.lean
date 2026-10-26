import Hypernets.Copying.AtomEqualityExecution

/-! Tree-carrier renaming, literal weakening and untouched store boundaries. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality
open Graph
namespace Same
def before_congr {h} {T V : ContractionTree .atom (h+2)} (f : T.net.Iso V.net) (d : Nat) : DeepIso (before T d) (before V d) :=
  Dereference.liftIso (Net.ExpansionIso.iso (beforeFrame h) (fun e => by
    cases e
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) f
    · exact Net.RelIso.refl (fun _ => rfl) _
    )) d
def after_congr {h} {T V : ContractionTree .atom (h+2)} (f : T.net.Iso V.net) (d : Nat) : DeepIso (after T d) (after V d) :=
  Dereference.liftIso (Net.ExpansionIso.iso (afterFrame h) (fun e => by
    cases e
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) f
    · exact Net.RelIso.refl (fun _ => rfl) _
    )) d
def discardLeft {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Edge := ⟨.discardLeft,(0 : Fin 1)⟩
theorem left_weakened {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    (after T d).edgeLabel (discardLeft T d) = primitiveLabel d (.weakening .term) ∧
    (after T d).target (discardLeft T d) = (after T d).source (afterLeft T d) := ⟨rfl,rfl⟩
def discardRight {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Edge := ⟨.discardRight,(0 : Fin 1)⟩
theorem right_weakened {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    (after T d).edgeLabel (discardRight T d) = primitiveLabel d (.weakening .term) ∧
    (after T d).target (discardRight T d) = (after T d).source (afterRight T d) := ⟨rfl,rfl⟩
theorem store_boundary {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    (before T d).target (beforeStore T d) = [.output 0] ∧
    (after T d).target (afterStore T d) = [.output 0] := ⟨rfl,rfl⟩
theorem other_references {h} (T : ContractionTree .atom (h+2)) (d : Nat) (i : Fin h) :
    beforeLeftVertex T d (.input ⟨i.val+2,by simp⟩) = inputPort h i.succ ∧
    afterLeftVertex T d (.input ⟨i.val+2,by simp⟩) = inputPort h i.succ := by
  constructor <;> simp [beforeLeftVertex,afterLeftVertex,Net.Expansion.insert,Net.Expansion.host,
    Net.sourcePort,beforeFrame,afterFrame,beforeSource,afterSource,otherInputs,inputPort,Port.map,Nat.add_assoc]
end Same
namespace Different
def before_congr {n m} {T V : ContractionTree .atom (n+1)} {U W : ContractionTree .atom (m+1)} (f : T.net.Iso V.net) (g : U.net.Iso W.net) (d : Nat) : DeepIso (before T U d) (before V W d) :=
  Dereference.liftIso (Net.ExpansionIso.iso (beforeFrame n m) (fun e => by
    cases e
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) f
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) g
    · exact Net.RelIso.refl (fun _ => rfl) _
    )) d
def after_congr {n m} {T V : ContractionTree .atom (n+1)} {U W : ContractionTree .atom (m+1)} (f : T.net.Iso V.net) (g : U.net.Iso W.net) (d : Nat) : DeepIso (after T U d) (after V W d) :=
  Dereference.liftIso (Net.ExpansionIso.iso (afterFrame n m) (fun e => by
    cases e
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) f
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) g
    · exact Net.RelIso.refl (fun _ => rfl) _
    )) d
def discardLeft {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge := ⟨.discardLeft,(0 : Fin 1)⟩
theorem left_weakened {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    (after T U d).edgeLabel (discardLeft T U d) = primitiveLabel d (.weakening .term) ∧
    (after T U d).target (discardLeft T U d) = (after T U d).source (afterLeft T U d) := ⟨rfl,rfl⟩
def discardRight {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge := ⟨.discardRight,(0 : Fin 1)⟩
theorem right_weakened {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    (after T U d).edgeLabel (discardRight T U d) = primitiveLabel d (.weakening .term) ∧
    (after T U d).target (discardRight T U d) = (after T U d).source (afterRight T U d) := ⟨rfl,rfl⟩
theorem store_boundaries {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    (before T U d).target (beforeStore T U d) = [.output 0] ∧
    (after T U d).target (afterStore T U d) = [.output 0] ∧
    (before T U d).target (beforeStoreRight T U d) = [.output 1] ∧
    (after T U d).target (afterStoreRight T U d) = [.output 1] := ⟨rfl,rfl,rfl,rfl⟩
theorem other_left_references {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (i : Fin n) :
    beforeLeftVertex T U d (.input ⟨i.val+1,by simp⟩) = inputPort n m ⟨i.val+1,by omega⟩ ∧
    afterLeftVertex T U d (.input ⟨i.val+1,by simp⟩) = inputPort n m ⟨i.val+1,by omega⟩ := by
  constructor <;> simp [beforeLeftVertex,afterLeftVertex,Net.Expansion.insert,Net.Expansion.host,
    Net.sourcePort,beforeFrame,afterFrame,beforeSource,afterSource,leftInputs,inputPort,Port.map]
theorem other_right_references {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (i : Fin m) :
    beforeRightVertex T U d (.input ⟨i.val+1,by simp⟩) = inputPort n m ⟨n+i.val+1,by omega⟩ ∧
    afterRightVertex T U d (.input ⟨i.val+1,by simp⟩) = inputPort n m ⟨n+i.val+1,by omega⟩ := by
  constructor <;> simp [beforeRightVertex,afterRightVertex,Net.Expansion.insert,Net.Expansion.host,
    Net.sourcePort,beforeFrame,afterFrame,beforeSource,afterSource,rightInputs,inputPort,Port.map]
end Different
end Hypernets.Copying.AtomEquality
