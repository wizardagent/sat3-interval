import Sat3.Search

namespace Sat3

theorem anyMaximalSearch6_38 : anyMaximalSearch 38 6 = false := by native_decide
theorem anyMaximalSearch7_38 : anyMaximalSearch 38 7 = false := by native_decide

theorem nodupInt_cert38 : NodupInt [1, 2, 5, 6, 15, 16, 19, 20] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_38_8 : HasMaximalOfSize 38 8 :=
  ⟨ofIntList [1, 2, 5, 6, 15, 16, 19, 20], [1, 2, 5, 6, 15, 16, 19, 20],
    maximal_of_cert_n38, nodupInt_cert38, rfl,
    ofIntList_of_memInt [1, 2, 5, 6, 15, 16, 19, 20]⟩

theorem sat3_eq_thirtyeight : sat3 38 (by decide) = 8 :=
  sat3_eq_eight_of_pair5 38 (by decide) (by decide)
    anyMaximalSearch6_38 anyMaximalSearch7_38 HasMaximalOfSize_38_8

end Sat3
