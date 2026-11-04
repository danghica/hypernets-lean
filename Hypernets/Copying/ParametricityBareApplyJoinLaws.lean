import Hypernets.Copying.ParametricityBareApplyJoin

/-! The assembled bare application preserves every vertex and edge of each
original component, including internal vertices and exposed boundaries. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyFirst.Join
open Graph Opening
variable {d n I O} (G : Hypernet d (List.replicate (n+1) .term) [])
    {H : Hypernet d I O} (a : Occurrence (primitiveNet d (.operation .app)) H)
    (f : Occurrence G H)
    (link : a.ports (.output (0 : Fin 2)) = f.ports (.input ⟨0,by simp⟩))
    (disjoint : ∀ e x, a.edges e ≠ f.edges x)

theorem head_port (v : (primitiveNet d (.operation .app)).Vertex) :
    (occurrence G a f link disjoint).ports ((head G).ports v) = a.ports v := by
  cases d
  all_goals
    exact Occurrence.ExpansionJoin.insert_ports (pattern n _) (filling G)
      (components G a f) (host G a f) (inputs G a f link) (outputs G a f) false v

theorem family_port (v : G.Vertex) :
    (occurrence G a f link disjoint).ports ((family G).ports v) = f.ports v := by
  cases d
  all_goals
    exact Occurrence.ExpansionJoin.insert_ports (pattern n _) (filling G)
      (components G a f) (host G a f) (inputs G a f link) (outputs G a f) true v

theorem head_edge (e : (primitiveNet d (.operation .app)).Edge) :
    (occurrence G a f link disjoint).edges ((head G).edges e) = a.edges e := by cases d <;> rfl

theorem family_edge (e : G.Edge) :
    (occurrence G a f link disjoint).edges ((family G).edges e) = f.edges e := by cases d <;> rfl

end Hypernets.Copying.Parametricity.BareApplyFirst.Join
