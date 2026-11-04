import Hypernets.Copying.WeakeningExtensionIso

/-! A literal weakening edge at an external output is a complete occurrence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph Opening

def weakeningAt {d I O} (H : Hypernet d I O) (e : H.Edge) (s : ShareSort)
    (j : Fin O.length) (label : H.edgeLabel e = primitiveLabel d (.weakening s))
    (source : H.source e = []) (target : H.target e = [.output j]) :
    Occurrence (primitiveNet d (.weakening s)) H := by
  cases d
  all_goals exact {
    ports := fun | .internal v => nomatch v | .input v => nomatch v | .output _ => .output j
    internals := fun v => nomatch v
    edges := fun _ => e
    internal_map := fun v => nomatch v
    internal_injective := fun v => nomatch v
    edge_injective := fun _ _ _ => Subsingleton.elim (α := Fin 1) _ _
    internal_label := fun v => nomatch v
    label := fun _ => by rw [label]; exact labelEquiv_refl _ _
    source := fun _ => source.symm
    target := fun _ => target.symm }

theorem weakeningAt_edge {d I O} (H : Hypernet d I O) (e : H.Edge) (s : ShareSort)
    (j : Fin O.length) (label : H.edgeLabel e = primitiveLabel d (.weakening s))
    (source : H.source e = []) (target : H.target e = [.output j])
    (a : (primitiveNet d (.weakening s)).Edge) :
    (weakeningAt H e s j label source target).edges a = e := by cases d <;> rfl

theorem weakeningAt_output {d I O} (H : Hypernet d I O) (e : H.Edge) (s : ShareSort)
    (j : Fin O.length) (label : H.edgeLabel e = primitiveLabel d (.weakening s))
    (source : H.source e = []) (target : H.target e = [.output j]) (i : Fin 1) :
    (weakeningAt H e s j label source target).ports (.output i) = .output j := by cases d <;> rfl
end Hypernets.Copying.Weakening
