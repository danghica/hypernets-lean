import Hypernets.Copying.ParametricityCommonRead

/-! Equality of interface lists transports every original correction graph
and exact token, leaving the four independently proved template links intact. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph

noncomputable def ReadCorrection.reboundary {d I O J K} {G H : Hypernet d I O} {v w}
    (p : ReadCorrection G v H w) (hi : I=J) (ho : O=K) :
    ReadCorrection (G.reboundary hi ho) (Port.cast hi ho v)
      (H.reboundary hi ho) (Port.cast hi ho w) :=
  ⟨p.middle.reboundary hi ho,Port.cast hi ho p.point,
    p.next.reboundary hi ho,Port.cast hi ho p.nextPoint,
    p.copying.reboundary hi ho,p.first.reboundary hi ho,p.second.reboundary hi ho⟩

noncomputable def ReadResidual.reboundary {d I O J K} {G H : Hypernet d I O} {v w}
    (p : ReadResidual G v H w) (hi : I=J) (ho : O=K) :
    ReadResidual (G.reboundary hi ho) (Port.cast hi ho v)
      (H.reboundary hi ho) (Port.cast hi ho w) :=
  ⟨p.middle.reboundary hi ho,Port.cast hi ho p.point,
    p.correction.reboundary hi ho,p.sharing.reboundary hi ho⟩

/-- Reflexivity uses actual reflexive filling witnesses for each independently
proved correction template, without identifying distinct graphs. -/
def ReadCorrection.refl {d I O} (G : Hypernet d I O) (free : FocusFree G) (v : G.Vertex) :
    ReadCorrection G v G v :=
  ⟨G,v,G,v,.refl G free v,.refl G free v,.refl G free v⟩

def ReadResidual.refl {d I O} (G : Hypernet d I O) (free : FocusFree G) (v : G.Vertex) :
    ReadResidual G v G v :=
  ⟨G,v,ReadCorrection.refl G free v,.refl G free v⟩
end Hypernets.Copying.Parametricity
