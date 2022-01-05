
namespace Sudoku

universe u v

def Slices (A : Type u) : Type u := Array $ Subarray A

def slice {A : Type u} (as : Array A) (ranges : Array ((Fin (as.size + 1)) × (Fin (as.size+1)))) : Slices A :=
  Array.map (fun (start, stop) =>
    as.toSubarray start.val stop.val
  ) ranges

/-
Bounded Nat
-/
-- def BNat (min max : Nat) (h : min ≤ max) := {n : Fin (max + 1) // GE.ge n.val min }
structure BNat (min max : Nat) (isMinMax : LE.le min max)where
  val  : Nat
  isLe : LE.le val max
  isGe : GE.ge val min

-- def BNat.mk {min max : Nat} {h : min ≤ max} (n : Nat) (h1 : LE.le n max) (h2 : GE.ge n min) : BNat min max h :=
--   let f : Fin (max + 1) := ⟨n, by
--     rw [Nat.add_one]
--     apply Nat.lt_succ_of_le
--     apply h1
--   ⟩
--   ⟨f, by apply h2⟩

@[simp] theorem ge_is_le (n m : Nat) : n ≥ m → m ≤ n := by
  intro h
  exact h

@[simp] theorem ge_refl (n : Nat) : n ≥ n := by apply ge_is_le; apply Nat.le_refl

instance {min max} {h : min ≤ max}: Inhabited (BNat min max h) := ⟨BNat.mk min h (by simp)⟩

instance Nat_toBNat {min max n : Nat} {h : min ≤ max} (h1 : LE.le n max ∧ GE.ge n min) : OfNat (BNat min max h) n := ⟨BNat.mk n h1.left h1.right⟩

theorem BNat.eq_of_val_eq {max min} {h : min ≤ max} : ∀ {i j : BNat min max h}, Eq i.val j.val → Eq i j
  | ⟨v, lt, gt⟩, ⟨_, _, _⟩, rfl => rfl

theorem BNat.val_eq_of_eq {max min} {h1 : min ≤ max} {i j : BNat min max h1} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

theorem BNat.ne_of_val_ne {max min} {h1 : min ≤ max} {i j : BNat min max h1} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

@[simp] theorem BNat.succ_le {max min} {h1 : min ≤ max} (n : BNat min max h1) (h : n.val < max): Nat.succ n.val ≤ max := h

instance (max min : Nat) (h1 : min ≤ max): DecidableEq (BNat min max h1) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (BNat.eq_of_val_eq h)
    | isFalse h => isFalse (BNat.ne_of_val_ne h)

instance {min max} {h : min ≤ max} : LT (BNat min max h) where
  lt a b := LT.lt a.val b.val

instance {min max} {h : min ≤ max} : LE (BNat min max h) where
  le a b := LE.le a.val b.val

instance BNat.decLt {min max} {h : min ≤ max} (a b : BNat min max h) : Decidable (LT.lt a b) := Nat.decLt ..
instance BNat.decLe {min max} {h : min ≤ max} (a b : BNat min max h) : Decidable (LE.le a b) := Nat.decLe ..

theorem range_terminates {min max} {h : min ≤ max} (n : BNat min max h): max - Nat.succ n.val ≤ max - n.val := by
  

@[inline] def BNat.range {min max} {h' : min ≤ max} : List $ BNat min max h' :=
  let rec @[specialize] it : BNat min max h' → (List $ BNat min max h') := (λ n => 
    if h : n.val < max then
      List.cons n $ it 
        { val := Nat.succ n.val
        , isLe := (by apply h)
        , isGe := (by
          apply ge_is_le
          apply Nat.le_of_lt
          apply Nat.lt_succ_of_le
          apply n.isGe
        )
        }
    else
      [BNat.mk n.val (by apply n.isLe) n.isGe]
  )
  it (BNat.mk min h' (by apply ge_refl))
termination_by measure λ b => b.snd.fst - b.snd.snd.snd.val
decreasing_by exact range_terminates

--   rw []
--   ) it
-- instance (b : BNat min max) : Sub Nat b := 
/-
Height and width
-/
variable {h w : Nat}

/-
An element 1 ≤ e ≤ size
-/
def Element (h w : Nat) : Type :=
  let size := h * w
  { elem : Nat // elem <= size && elem >= 1 }

/-
A Sudoku board not validated
-/
def Board (h w : Nat) (ax : h ≥ 1 ∧ w ≥ 1) : Type :=
 let size := h * w
 { arr : Array (Option $ Element h w) // arr.size = size * size }

@[simp] theorem board_size {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) : b.val.size = h * h * w * w := by
  rw [b.property, Nat.mul_assoc, Nat.mul_comm w (h * w), ←Nat.mul_assoc, ←Nat.mul_assoc]

@[simp] theorem add_le_cancel_right (m n k: Nat) : m ≤ n → m + k ≤ n + k := by
  intro h'
  apply Nat.add_le_add_right
  apply h'
/-
Get an element in a matrix 1-indexed manner. E.g. the upper left corner is (1,1)
and the rest of the corners are lower left (h * w, 1), upper
-/
def get {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) (i j : BNat 1 b.val.size (by 
    rw [board_size];
    apply ge_is_le;
    rw [Nat.]
    apply ax.left
    --decide;
    -- induction w, h with
    -- | zero zero => rw [ax]
    -- | succ 
    -- rw [Nat.mul_le_mul];
    -- apply ax.right
  )) : Option $ Element h w :=
  let size := h * w
  b.val.get ⟨(i.val - 1) * size + j.val - 1, by
    simp
    --rw [Nat.mul_comm]
    apply i.property
    apply j.property
  ⟩

def getCell {ax : h ≥ 1 ∧ w ≥ 1} (b : Board h w ax) (i : BNat 1 w (by apply ax.right)) (j : BNat 1 h (by apply ax.left)) : Slices <| Option <| Element h w :=
  slice b.val #[(⟨(i.val-1)*h, by simp⟩, ⟨(j.val-1)*w, by simp; rw [Nat.add_mul j.val 1 w, Nat.sub_le]; apply j.isLe⟩)] 

--#eval ([1:3])

def validate {ax : h ≥ 1 ∧ w ≥ 1} (s : Board h w ax) : Except String Unit :=
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
      error s!"not unique"

