import Sat3.Search

namespace Sat3

theorem anyMaximalSearch5_34 : anyMaximalSearch 34 5 = false := by native_decide
theorem anyMaximalSearch6_34 : anyMaximalSearch 34 6 = false := by native_decide
theorem anyMaximalSearch7_34 : anyMaximalSearch 34 7 = false := by native_decide

theorem nodupInt_cert34 : NodupInt [1, 2, 4, 5, 14, 15, 17, 18] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_34_8 : HasMaximalOfSize 34 8 :=
  ⟨ofIntList [1, 2, 4, 5, 14, 15, 17, 18], [1, 2, 4, 5, 14, 15, 17, 18],
    maximal_of_cert_n34, nodupInt_cert34, rfl,
    ofIntList_of_memInt [1, 2, 4, 5, 14, 15, 17, 18]⟩

theorem sat3_eq_thirtyfour : sat3 34 (by decide) = 8 :=
  sat3_eq_eight_of 34 (by decide) (by decide)
    anyMaximalSearch5_34 anyMaximalSearch6_34 anyMaximalSearch7_34
    HasMaximalOfSize_34_8

end Sat3
