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
  elementBound := { min := 1, max := (h*w), isMinMax := (one_le_size ax) : Bound }
  -- A rows first matrix
  arr : Array (Option <| BNat elementBound)
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

abbrev Index (b : Board) := BNat b.elementBound
/-
Get an element in a matrix 1-indexed manner. E.g. the upper left corner is (1,1)
and the rest of the corners are lower left (h * w, 1), upper
-/
def get (b : Board) (i j : b.Index) : Option $ BNat b.elementBound :=
  b.arr.get ⟨(i.val - 1) * b.size + j.val - 1, by
    -- simp
    -- decide
    --rw [Nat.mul_comm]
    -- apply i.property
    -- apply j.property
    sorry
  ⟩

def CellRowIndex (b : Board) : Type := BNat <| Bound.mk 1 b.h (by apply b.ax.left) 
def CellColIndex (b : Board) : Type := BNat <| Bound.mk 1 b.w (by apply b.ax.right)

def getCell (b : Board) (i : b.CellRowIndex) (j : b.CellColIndex) : Slice <| Option <| BNat b.elementBound :=
  let colStart := (j.val-1)*b.w
  let rowStart := colStart + (i.val-1)*b.h
  let rows := b.elementBound.range.toArray.map (λ r =>
    { start := (i.val-1)*b.h, stop := (j.val-1)*b.w, h1 := by sorry;, h2 := by sorry; /- simp-/ : SliceRange b.arr.size }
  )
  { array := b.arr, ranges := rows : Slice <| Option <| BNat b.elementBound  }

def validateSlice {A : Type} [BEq A] (s: Slice <| Option A) : Bool :=
  Prod.snd <| s.foldl (λ (found, b) o =>
  match o with
  | some a =>
    if found.contains a then
      (found, false)
    else
      (found.push a, b)
  | none => (found, b)
  ) (#[], true)

def isValid? (b : Board) : Except String Unit := do
  -- cells
  -- let mut er := 1
  -- let mut ec := 1
  let mut valid := true
  for r in [1:h] do
    for c in [1:w] do
      let cell := b.getCell (r.toBNat.get! : b.CellRowIndex) (c.toBNat.get! : b.CellColIndex)
      if not (validateSlice cell) then
        valid := false
        -- er := r
        -- ec := c
        break
  if valid then
    return ()
  else
    throw s!"invalid at"


-- /--- rows
--   for r in [1:h*w] do
--     let row := getRow b r
--     if not (unique row) then
--       error s!"not unique"
--   -- columns
--   for c in [1:h*w] do
--     let col := getColumn b c
--     if not (unique col) then
--       error s!"not unique"
-- -/

private def toString (b : Board) : String :=
  let horiz := "-".replicate (3*b.h*b.w + b.w + 1) ++ "\n"
  b.arr.toList.enum.foldl (λ acc (i, oe) => 
    acc ++ (if i % b.w = 0 then
      "|"
    else
      ""
    ) ++ 
    (match oe with
    | some e => s!" {e} "
    | none => s!" _ "
    ) ++ (if (i + 1) % b.size = 0 then
      "|\n" ++
        (if ((i+1) /(b.h*b.w)) % b.h = 0 then
          horiz
        else
          ""
        )
    else
      ""
    )    
  ) horiz

instance : ToString Board := ⟨Board.toString⟩

def parseText (s : String) (h : Nat := 3) (w : Nat := 3) : Except String Board := do
  if ax : h ≥ 1 ∧ w ≥ 1 then
    let lines := s.splitOn "\n"
    let elementBound := { min := 1, max := h*w, isMinMax := one_le_size ax : Bound }
    let rows : Array <| Option (BNat elementBound) := lines.foldl (λ acc l => 
      let numbers := l.splitOn " "
      acc ++ numbers.toArray.map (λ s =>
      if let some n := s.toNat? then
        n.toBNat
      else
        none
      ) 
    ) #[]
    if axArr : rows.size = h*h*w*w then
      return { h, w, ax, arr := rows, axArr : Board }
    else
      throw s!"Wrong number of elements {rows.size} should be h*h*w*w = {h*h*w*w}"
  else
    throw "w and h must be ≥1"
    
def parseFile (f : System.FilePath) (h : Nat := 3) (w : Nat := 3) : IO Board := do
  let text ← IO.FS.readFile f
  let board : Board ← IO.ofExcept <| parseText text h w
  return board

end Board
end Sudoku