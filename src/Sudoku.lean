import Sudoku.Utils
namespace Sudoku


/-
Height and width
-/
variable {h w : Nat}

/-
A Sudoku board not validated
-/
structure Board where
  h : Nat
  w : Nat
  ax : h ≥ 1 ∧ w ≥ 1
  Element := BNat 1 (h*w) (one_le_size ax)
  arr : Array (Option $ Element)
  axArr : arr.size = h*h*w*w

namespace Board
def size (b: Board) : Nat := b.h * b.w

@[simp] theorem board_size (b : Board) : b.size = h * h * w * w := by
  -- apply Board.size
  -- simp [b.axArr]
  sorry
  -- simp [b.axArr, Nat.mul_assoc, Nat.mul_comm w (h * w), ←Nat.mul_assoc, ←Nat.mul_assoc]


@[simp] theorem board_size_ge_one (b : Board) : b.size ≥ 1 := by
  rw [board_size];
  have hh := mul_ge_one_of_ge_one b.ax.1 b.ax.1
  have ww := mul_ge_one_of_ge_one b.ax.2 b.ax.2
  rw [Nat.mul_assoc]
  exact mul_ge_one_of_ge_one hh ww

def Index (b : Board) := BNat 1 b.size (board_size_ge_one b)
/-
Get an element in a matrix 1-indexed manner. E.g. the upper left corner is (1,1)
and the rest of the corners are lower left (h * w, 1), upper
-/
def get (b : Board) (i j : b.Index) : Option $ b.Element :=
  b.arr.get ⟨(i.val - 1) * b.size + j.val - 1, by
    -- simp
    -- decide
    --rw [Nat.mul_comm]
    -- apply i.property
    -- apply j.property
    sorry
  ⟩

def CellRowIndex (b : Board) := BNat 1 b.w (by apply b.ax.right) 
def CellColIndex (b : Board) := BNat 1 b.h (by apply b.ax.left)

def getCell (b : Board) (i : b.CellRowIndex) (j : b.CellColIndex) : Slices <| Option b.Element :=
  slice b.arr #[(⟨(i.val-1)*b.h, by sorry; /- simp-/⟩, ⟨(j.val-1)*b.w, by sorry; /-simp; rw [Nat.add_mul j.val 1 b.w, Nat.sub_le]; apply j.isLe -/⟩)]

-- def getRow (b : Board) (r : BNat 1 (b.w*b.h) (by apply ax.right)) : Slices <| Option b.Element :=
--   slice b.arr #[(⟨(r.val-1)*b.h, by simp⟩, ⟨(j.val-1)*b.w, by simp; rw [Nat.add_mul j.val 1 b.w, Nat.sub_le]; apply j.isLe⟩)] 
--#eval ([1:3])

/-def validate (b : Board) : Except String Unit := do
  -- cells
  for r in [1:h] do
    for c in [1:w] do
      let cell := getCell b r c
      if not (unique cell) then
        error s!"not unique"
  -- rows
  for r in [1:h*w] do
    let row := getRow b r
    if not (unique row) then
      error s!"not unique"
  -- columns
  for c in [1:h*w] do
    let col := getColumn b c
    if not (unique col) then
      error s!"not unique"-/
end Board
end Sudoku
