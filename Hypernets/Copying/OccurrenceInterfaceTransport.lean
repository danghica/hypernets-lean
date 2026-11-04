import Hypernets.Copying.WeakeningBinarySteps

/-! Occurrences through the original translation's equality transports. -/
namespace Hypernets.Copying.Opening.Occurrence
open Graph

def castInterfaces {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : Occurrence G H) (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X) :
    Occurrence (Translation.castInterfaces hi ho G) (Translation.castInterfaces hj hk H) := by
  cases hi; cases ho; cases hj; cases hk; exact f

theorem castInterfaces_input {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : Occurrence G H) (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X)
    (a : Fin I.length) (b : Fin J.length) (eq : f.ports (.input a) = .input b) :
    (f.castInterfaces hi ho hj hk).ports (.input (Fin.cast (congrArg List.length hi) a)) =
      .input (Fin.cast (congrArg List.length hj) b) := by
  cases hi; cases ho; cases hj; cases hk; exact eq

theorem castInterfaces_output {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : Occurrence G H) (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X)
    (a : Fin O.length) (b : Fin K.length) (eq : f.ports (.output a) = .output b) :
    (f.castInterfaces hi ho hj hk).ports (.output (Fin.cast (congrArg List.length ho) a)) =
      .output (Fin.cast (congrArg List.length hk) b) := by
  cases hi; cases ho; cases hj; cases hk; exact eq
end Hypernets.Copying.Opening.Occurrence
