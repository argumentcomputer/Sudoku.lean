import Sudoku.Utils
namespace Sudoku

universe u
/-
Height and width
-/
variable {h w : Nat} {bound : Bound}

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

structure FilledBoard extends Board where
  prop : arr.toList.allSome = true

def FilledBoard.list (fb : FilledBoard) : List Nat := fb.arr.toList.allSomeUnwrap (fb.prop) |> List.map BNat.val

inductive Permutation {A : Type u} : (l1 l2 : List A) → Prop
  | refl : Permutation [] []
  | skip {a : A} (p : Permutation l2 l1) : Permutation (a :: l2) (a :: l1)
  | swap {a b : A} : Permutation (a :: b :: l1) (a :: b :: l2)
  | trans (p1 : Permutation l1 l2) (p2 : Permutation l2 l3) : Permutation l1 l3
  
-- def Permutation.decide {A} : ∀ (a b : A), a = b + a <> b → ∀ (l1 l2 : List A), (Permutation l1 l2) + (~ Permutation l1 l2)


namespace Board
/-
The size of the side of the quadratic grid. The number of elements is size^2.
-/
def size (b: Board) : Nat := b.h * b.w

/-
Reference List of legal elements (list version of BNat b.elementBound)
-/
def refList (b : Board) : List Nat := progression b.size 1

end Board

variable {size : Nat}

structure Pos (size) where
  x : Fin size
  y : Fin size
  deriving BEq

theorem Fin.of_zero {n : Nat} (f : Fin n) : 0 < n := by apply Nat.lt_of_le_and_ne; apply Nat.zero_le; sorry

def Pos.next {size} (p : Pos size) : Pos size :=
  if h : p.y < size then { p with y := p.y }
  else if h : Nat.succ p.x < size then { x := ⟨p.x + 1, by apply h⟩, y := ⟨0, Fin.of_zero p.x⟩ }
  else p

structure Litteral (size) where
  p : Pos size
  v : Nat
  deriving BEq

def Clause size := List (Litteral size)

namespace Clause

def rm (c1 c2 : Clause size) : Clause size := List.removeAll c1 c2

def merge (c1 c2 : Clause size) : Clause size := List.append c1 c2

-- def update (c : Clause size) : Clause size := c.find? (λ l => l.v)

end Clause

def Clauses size := List (Nat × Clause size)

namespace Clauses

def merge (c1 c2 : Clauses size) : Clauses size := List.append c1 c2

def insert (c : Clause size) (cs : Clauses size) : Clauses size := (c.length, c) :: cs

-- def update (c : Clauses size) : Clauses size := c.find? (λ l => l.v)

end Clauses

def indexes (b : Board) : List Nat := progression b.size 0

def cross (b : Board) : List (Pos b.size) :=
  let p : List Nat := progression b.h 0
  let q : List Nat := progression b.w 0
  p.foldr (fun x l => (q.map (fun y => (Pos.mk ⟨x, by sorry⟩ ⟨y, by sorry⟩))) ++ l) []

namespace FilledBoard

def row (b : FilledBoard) (i : Nat) : List Nat := (b.list.drop (i * b.size)).take i

def column (b : FilledBoard) (i : Nat) : List Nat := (b.list.drop i).takeAndJump 1 b.size b.size

def cell (b : FilledBoard) (i : Nat) : List Nat := (b.list.drop (b.w * (i % b.h) + b.h * (i / b.h) * b.size)).takeAndJump b.w b.size b.h

def get (b : FilledBoard) (p : Pos b.size) : Nat :=
  let i := p.x * b.size + p.y
  b.list.get i (by sorry;)

def Sudoku (b : FilledBoard) : Prop :=
  ∀ i, i < b.size → Permutation (b.row i) b.refList ∧
  ∀ i, i < b.size → Permutation (b.column i) b.refList ∧
  ∀ i, i < b.size → Permutation (b.cell i) b.refList

-- def check {fb} (s : Sudoku fb) : Prop := 

end FilledBoard

namespace Board

@[simp] theorem board_size_ge_one (b : Board) : b.arr.size ≥ 1 := by
  rw [b.axArr];
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
    let start := rowStart + r.val*b.w*b.h
    { start, stop := start + b.w, h1 := by sorry;, h2 := by sorry; /- simp-/ : SliceRange b.arr.size }
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

def isValid? (b : Board) : Except String Unit := do {
  -- cells
  -- let mut er := 1
  -- let mut ec := 1
  let mut valid := true;
  -- for r in [1:b.h] do
  --   for c in [1:b.w] do
      -- let cell := b.getCell (r.toBNat.get! : b.CellRowIndex) (c.toBNat.get! : b.CellColIndex)
      -- if not (validateSlice cell) then
      --   valid := false
        -- er := r
        -- ec := c
      -- break
  if valid then
    return ();
  else
    throw s!"invalid at";
}


protected def toString (b : Board) (useBorders : Bool := true) : String :=
  let horiz := "-".replicate (3*b.h*b.w + b.w + 1) ++ "\n"
  b.arr.toList.enum.foldl (λ acc (i, oe) => 
    acc ++ (if useBorders ∧ i % b.w = 0 then
      "|"
    else
      ""
    ) ++ 
    (match oe with
    | some e => s!" {e} "
    | none => s!" _ "
    ) ++ (if (i + 1) % b.size = 0 then
      (if useBorders then "|" else "") ++
      "\n" ++
        (if useBorders ∧ ((i+1) /(b.h*b.w)) % b.h = 0 then
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
        n.toBNat?
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