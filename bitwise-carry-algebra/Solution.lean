/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitwiseCarryAlgebra

namespace BitwiseCarryChallenge

open BitwiseCarryAlgebra

theorem carryWord_cocycle (x y z : Nat) :
    carryWord x y ^^^ carryWord (x + y) z ^^^ carryWord y z ^^^ carryWord x (y + z) = 0 :=
  BitwiseCarryAlgebra.carryWord_cocycle x y z

theorem carryPop_cocycle (x y z : Nat) :
    popcnt (carryWord x y) + popcnt (carryWord (x + y) z) =
    popcnt (carryWord y z) + popcnt (carryWord x (y + z)) :=
  BitwiseCarryAlgebra.carryPop_cocycle x y z

theorem gray_add_xor_eq_gray_carryWord (x y : Nat) :
    gray (x + y) ^^^ gray x ^^^ gray y = gray (carryWord x y) :=
  BitwiseCarryAlgebra.gray_add_xor_eq_gray_carryWord x y

theorem popcnt_gray_carryWord (x y : Nat) :
    popcnt (gray (x + y) ^^^ gray x ^^^ gray y) = 2 * carryBlocks x y :=
  BitwiseCarryAlgebra.popcnt_gray_carryWord x y

theorem borrowWord_eq_carryWord (x y : Nat) :
    borrowWord x y = carryWord (min x y) (max x y - min x y) :=
  BitwiseCarryAlgebra.borrowWord_eq_carryWord x y

theorem sumSquare_carryPop (k : Nat) :
    2 * sumSquare k (fun i j => popcnt (carryWord i j)) + 4 ^ k = k * 4 ^ k + 2 ^ k :=
  BitwiseCarryAlgebra.sumSquare_carryPop k

theorem sumSquare_carryBlocks (k : Nat) :
    8 * sumSquare k carryBlocks + 2 * 2 ^ k = (k + 2) * 4 ^ k :=
  BitwiseCarryAlgebra.sumSquare_carryBlocks k

theorem count_zero_and_one_carryBlock (k : Nat) :
    sumSquare k (fun i j => if carryBlocks i j = 0 then 1 else 0) = 3 ^ k ∧
    2 * sumSquare (k + 2) (fun i j => if carryBlocks i j = 1 then 1 else 0) =
      (k + 2) * (k + 7) * 3 ^ k :=
  BitwiseCarryAlgebra.count_zero_and_one_carryBlock k

end BitwiseCarryChallenge
