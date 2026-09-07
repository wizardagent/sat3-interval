import Sat3.Search

namespace Sat3

theorem anyMaximalSearch6_37 : anyMaximalSearch 37 6 = false := by native_decide
theorem anyMaximalSearch7_37 : anyMaximalSearch 37 7 = false := by native_decide

theorem nodupInt_cert37 : NodupInt [1, 2, 5, 6, 14, 15, 18, 19] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_37_8 : HasMaximalOfSize 37 8 :=
  ⟨ofIntList [1, 2, 5, 6, 14, 15, 18, 19], [1, 2, 5, 6, 14, 15, 18, 19],
    maximal_of_cert_n37, nodupInt_cert37, rfl,
    ofIntList_of_memInt [1, 2, 5, 6, 14, 15, 18, 19]⟩

theorem sat3_eq_thirtyseven : sat3 37 (by decide) = 8 :=
  sat3_eq_eight_of_pair5 37 (by decide) (by decide)
    anyMaximalSearch6_37 anyMaximalSearch7_37 HasMaximalOfSize_37_8

end Sat3
