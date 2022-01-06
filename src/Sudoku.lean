import Sudoku.Utils
namespace Sudoku


/-
Height and width
-/
variable {h w : Nat}

/-
A Sudoku board not validated
-/
def Board (h w : Nat) (ax : h ≥ 1 ∧ w ≥ 1) : Type :=
  let size := h * w
  { arr : Array (Option $ BNat 1 size (one_le_size ax)) // arr.size = size * size }

@[simp] theorem board_size {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) : b.val.size = h * h * w * w := by
  rw [b.property, Nat.mul_assoc, Nat.mul_comm w (h * w), ←Nat.mul_assoc, ←Nat.mul_assoc]


@[simp] theorem board_size_ge_one {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) : b.val.size ≥ 1 := by
  rw [board_size];
  have hh := mul_ge_one_of_ge_one ax.1 ax.1
  have ww := mul_ge_one_of_ge_one ax.2 ax.2
  rw [Nat.mul_assoc]
  exact mul_ge_one_of_ge_one hh ww

/-
Get an element in a matrix 1-indexed manner. E.g. the upper left corner is (1,1)
and the rest of the corners are lower left (h * w, 1), upper
-/
def get {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) (i j : BNat 1 b.val.size (board_size_ge_one b)) : Option $ BNat 1 b.val.size (board_size_ge_one b) :=
  let size := h * w
  b.val.get ⟨(i.val - 1) * size + j.val - 1, by
    simp
    decide
    --rw [Nat.mul_comm]
    apply i.property
    apply j.property
  ⟩

def getCell {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) (i : BNat 1 w (by apply ax.right)) (j : BNat 1 h (by apply ax.left)) : Slices <| Option <| Element h w :=
  slice b.val #[(⟨(i.val-1)*h, by simp⟩, ⟨(j.val-1)*w, by simp; rw [Nat.add_mul j.val 1 w, Nat.sub_le]; apply j.isLe⟩)] 

def getRow {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) (r : BNat 1 (w*h) (by apply ax.right)) : Slices <| Option <| Element h w :=
  slice b.val #[(⟨(i.val-1)*h, by simp⟩, ⟨(j.val-1)*w, by simp; rw [Nat.add_mul j.val 1 w, Nat.sub_le]; apply j.isLe⟩)] 
--#eval ([1:3])

def validate {ax : h ≥ 1 ∧ w ≥ 1} (s : Board h w ax) : Except String Unit := do
  -- cells
  for r in 1 h do
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
      error s!"not unique"

