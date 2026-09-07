import Sat3.Search

namespace Sat3

theorem anyMaximalSearch5_35 : anyMaximalSearch 35 5 = false := by native_decide
theorem anyMaximalSearch6_35 : anyMaximalSearch 35 6 = false := by native_decide
theorem anyMaximalSearch7_35 : anyMaximalSearch 35 7 = false := by native_decide

theorem nodupInt_cert35 : NodupInt [1, 2, 4, 5, 14, 15, 17, 18] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_35_8 : HasMaximalOfSize 35 8 :=
  ⟨ofIntList [1, 2, 4, 5, 14, 15, 17, 18], [1, 2, 4, 5, 14, 15, 17, 18],
    maximal_of_cert_n35, nodupInt_cert35, rfl,
    ofIntList_of_memInt [1, 2, 4, 5, 14, 15, 17, 18]⟩

theorem sat3_eq_thirtyfive : sat3 35 (by decide) = 8 :=
  sat3_eq_eight_of 35 (by decide) (by decide)
    anyMaximalSearch5_35 anyMaximalSearch6_35 anyMaximalSearch7_35
    HasMaximalOfSize_35_8

end Sat3
