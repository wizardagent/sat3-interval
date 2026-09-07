import Sat3.Basic
import Sat3.Block
import Sat3.Sound

/-
  Boolean certificates for explicit maximal 3-AP-free sets.
  These are the examples from the computational table in `data/sat3_values.json`.
  Each lemma is an upper bound `sat_3(n) ≤ |A|`.
-/

namespace Sat3

theorem cert_n1 : maximal 1 [1] = true := by native_decide
theorem cert_n2 : maximal 2 [1, 2] = true := by native_decide
theorem cert_n3 : maximal 3 [1, 2] = true := by native_decide
theorem cert_n4 : maximal 4 [2, 3] = true := by native_decide
theorem cert_n5 : maximal 5 [1, 3, 4] = true := by native_decide
theorem cert_n6 : maximal 6 [1, 2, 4, 5] = true := by native_decide
theorem cert_n9 : maximal 9 [1, 2, 4, 5] = true := by native_decide
theorem cert_n16 : maximal 16 [6, 7, 10, 11] = true := by native_decide
theorem cert_n17 : maximal 17 [1, 7, 8, 11, 12] = true := by native_decide
theorem cert_n18 : maximal 18 [1, 2, 4, 8, 9, 11] = true := by native_decide
theorem cert_n19 : maximal 19 [1, 2, 4, 8, 17, 18] = true := by native_decide
theorem cert_n20 : maximal 20 [1, 2, 4, 9, 11, 15] = true := by native_decide
theorem cert_n21 : maximal 21 [1, 2, 4, 9, 11, 15] = true := by native_decide
theorem cert_n22 : maximal 22 [1, 2, 10, 11, 15, 16] = true := by native_decide
theorem cert_n23 : maximal 23 [2, 3, 11, 12, 16, 17] = true := by native_decide
theorem cert_n24 : maximal 24 [4, 5, 7, 12, 14, 18] = true := by native_decide
theorem cert_n25 : maximal 25 [5, 6, 8, 13, 15, 19] = true := by native_decide
theorem cert_n26 : maximal 26 [8, 10, 11, 15, 17, 18] = true := by native_decide
theorem cert_n27 : maximal 27 [1, 2, 5, 11, 12, 14, 18] = true := by native_decide
theorem cert_n28 : maximal 28 [1, 2, 12, 13, 15, 19, 20] = true := by native_decide
theorem cert_n29 : maximal 29 [1, 2, 12, 13, 15, 19, 20] = true := by native_decide
theorem cert_n30 : maximal 30 [1, 2, 13, 14, 16, 21, 22] = true := by native_decide
theorem cert_n31 : maximal 31 [1, 2, 13, 14, 16, 21, 22] = true := by native_decide
theorem cert_n32 : maximal 32 [2, 3, 14, 15, 17, 22, 23] = true := by native_decide
theorem cert_n33 : maximal 33 [1, 2, 4, 5, 13, 14, 16, 17] = true := by native_decide
theorem cert_n34 : maximal 34 [1, 2, 4, 5, 14, 15, 17, 18] = true := by native_decide
theorem cert_n35 : maximal 35 [1, 2, 4, 5, 14, 15, 17, 18] = true := by native_decide
theorem cert_n36 : maximal 36 [1, 2, 5, 6, 14, 15, 18, 19] = true := by native_decide
theorem cert_n37 : maximal 37 [1, 2, 5, 6, 14, 15, 18, 19] = true := by native_decide
theorem cert_n38 : maximal 38 [1, 2, 5, 6, 15, 16, 19, 20] = true := by native_decide
theorem cert_n39 : maximal 39 [1, 2, 5, 6, 15, 16, 19, 20] = true := by native_decide
theorem cert_n40 : maximal 40 [1, 2, 5, 6, 16, 17, 20, 21] = true := by native_decide

theorem maximal_of_cert_n1 : MaximalAP3Free 1 (ofIntList [1]) :=
  maximal_sound 1 [1] cert_n1
theorem maximal_of_cert_n2 : MaximalAP3Free 2 (ofIntList [1, 2]) :=
  maximal_sound 2 [1, 2] cert_n2
theorem maximal_of_cert_n3 : MaximalAP3Free 3 (ofIntList [1, 2]) :=
  maximal_sound 3 [1, 2] cert_n3
theorem maximal_of_cert_n4 : MaximalAP3Free 4 (ofIntList [2, 3]) :=
  maximal_sound 4 [2, 3] cert_n4
theorem maximal_of_cert_n5 : MaximalAP3Free 5 (ofIntList [1, 3, 4]) :=
  maximal_sound 5 [1, 3, 4] cert_n5
theorem maximal_of_cert_n6 : MaximalAP3Free 6 (ofIntList [1, 2, 4, 5]) :=
  maximal_sound 6 [1, 2, 4, 5] cert_n6
theorem maximal_of_cert_n9 : MaximalAP3Free 9 (ofIntList [1, 2, 4, 5]) :=
  maximal_sound 9 [1, 2, 4, 5] cert_n9
theorem maximal_of_cert_n16 : MaximalAP3Free 16 (ofIntList [6, 7, 10, 11]) :=
  maximal_sound 16 [6, 7, 10, 11] cert_n16
theorem maximal_of_cert_n17 : MaximalAP3Free 17 (ofIntList [1, 7, 8, 11, 12]) :=
  maximal_sound 17 [1, 7, 8, 11, 12] cert_n17
theorem maximal_of_cert_n18 : MaximalAP3Free 18 (ofIntList [1, 2, 4, 8, 9, 11]) :=
  maximal_sound 18 [1, 2, 4, 8, 9, 11] cert_n18
theorem maximal_of_cert_n19 : MaximalAP3Free 19 (ofIntList [1, 2, 4, 8, 17, 18]) :=
  maximal_sound 19 [1, 2, 4, 8, 17, 18] cert_n19
theorem maximal_of_cert_n20 : MaximalAP3Free 20 (ofIntList [1, 2, 4, 9, 11, 15]) :=
  maximal_sound 20 [1, 2, 4, 9, 11, 15] cert_n20
theorem maximal_of_cert_n21 : MaximalAP3Free 21 (ofIntList [1, 2, 4, 9, 11, 15]) :=
  maximal_sound 21 [1, 2, 4, 9, 11, 15] cert_n21
theorem maximal_of_cert_n22 : MaximalAP3Free 22 (ofIntList [1, 2, 10, 11, 15, 16]) :=
  maximal_sound 22 [1, 2, 10, 11, 15, 16] cert_n22
theorem maximal_of_cert_n23 : MaximalAP3Free 23 (ofIntList [2, 3, 11, 12, 16, 17]) :=
  maximal_sound 23 [2, 3, 11, 12, 16, 17] cert_n23
theorem maximal_of_cert_n24 : MaximalAP3Free 24 (ofIntList [4, 5, 7, 12, 14, 18]) :=
  maximal_sound 24 [4, 5, 7, 12, 14, 18] cert_n24
theorem maximal_of_cert_n25 : MaximalAP3Free 25 (ofIntList [5, 6, 8, 13, 15, 19]) :=
  maximal_sound 25 [5, 6, 8, 13, 15, 19] cert_n25
theorem maximal_of_cert_n26 : MaximalAP3Free 26 (ofIntList [8, 10, 11, 15, 17, 18]) :=
  maximal_sound 26 [8, 10, 11, 15, 17, 18] cert_n26
theorem maximal_of_cert_n27 : MaximalAP3Free 27 (ofIntList [1, 2, 5, 11, 12, 14, 18]) :=
  maximal_sound 27 [1, 2, 5, 11, 12, 14, 18] cert_n27
theorem maximal_of_cert_n28 : MaximalAP3Free 28 (ofIntList [1, 2, 12, 13, 15, 19, 20]) :=
  maximal_sound 28 [1, 2, 12, 13, 15, 19, 20] cert_n28
theorem maximal_of_cert_n29 : MaximalAP3Free 29 (ofIntList [1, 2, 12, 13, 15, 19, 20]) :=
  maximal_sound 29 [1, 2, 12, 13, 15, 19, 20] cert_n29
theorem maximal_of_cert_n30 : MaximalAP3Free 30 (ofIntList [1, 2, 13, 14, 16, 21, 22]) :=
  maximal_sound 30 [1, 2, 13, 14, 16, 21, 22] cert_n30
theorem maximal_of_cert_n31 : MaximalAP3Free 31 (ofIntList [1, 2, 13, 14, 16, 21, 22]) :=
  maximal_sound 31 [1, 2, 13, 14, 16, 21, 22] cert_n31
theorem maximal_of_cert_n32 : MaximalAP3Free 32 (ofIntList [2, 3, 14, 15, 17, 22, 23]) :=
  maximal_sound 32 [2, 3, 14, 15, 17, 22, 23] cert_n32
theorem maximal_of_cert_n33 : MaximalAP3Free 33 (ofIntList [1, 2, 4, 5, 13, 14, 16, 17]) :=
  maximal_sound 33 [1, 2, 4, 5, 13, 14, 16, 17] cert_n33
theorem maximal_of_cert_n34 : MaximalAP3Free 34 (ofIntList [1, 2, 4, 5, 14, 15, 17, 18]) :=
  maximal_sound 34 [1, 2, 4, 5, 14, 15, 17, 18] cert_n34
theorem maximal_of_cert_n35 : MaximalAP3Free 35 (ofIntList [1, 2, 4, 5, 14, 15, 17, 18]) :=
  maximal_sound 35 [1, 2, 4, 5, 14, 15, 17, 18] cert_n35
theorem maximal_of_cert_n36 : MaximalAP3Free 36 (ofIntList [1, 2, 5, 6, 14, 15, 18, 19]) :=
  maximal_sound 36 [1, 2, 5, 6, 14, 15, 18, 19] cert_n36
theorem maximal_of_cert_n37 : MaximalAP3Free 37 (ofIntList [1, 2, 5, 6, 14, 15, 18, 19]) :=
  maximal_sound 37 [1, 2, 5, 6, 14, 15, 18, 19] cert_n37
theorem maximal_of_cert_n38 : MaximalAP3Free 38 (ofIntList [1, 2, 5, 6, 15, 16, 19, 20]) :=
  maximal_sound 38 [1, 2, 5, 6, 15, 16, 19, 20] cert_n38
theorem maximal_of_cert_n39 : MaximalAP3Free 39 (ofIntList [1, 2, 5, 6, 15, 16, 19, 20]) :=
  maximal_sound 39 [1, 2, 5, 6, 15, 16, 19, 20] cert_n39
theorem maximal_of_cert_n40 : MaximalAP3Free 40 (ofIntList [1, 2, 5, 6, 16, 17, 20, 21]) :=
  maximal_sound 40 [1, 2, 5, 6, 16, 17, 20, 21] cert_n40

end Sat3
