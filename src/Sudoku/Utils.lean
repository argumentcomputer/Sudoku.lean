universe u v

def String.replicate (s: String) (n : Nat) (sep := "") : String :=
  sep.intercalate (List.replicate n s)

-- def Slice (A : Type u) : Type u := Array $ Subarray A
open Std

structure SliceRange (size : Nat) where
  start : Nat
  stop : Nat
  h1 : start ≤ stop
  h2 : stop ≤ size

def SliceRange.toRange (s : SliceRange n) : List Nat :=
  let rec f n := 
    if n < s.stop then
      n :: f (n+1)
    else
      []
  f s.start
termination_by _ => s.stop - n
decreasing_by f =>
  simp [Nat.succ_eq_add_one]
  sorry

structure Slice (α : Type u) where
  array : Array α
  ranges : Array (SliceRange array.size)

def List.allSome {A} (l : List <| Option A) : Bool := l.all (λ o => o.isSome)

def List.allSomeUnwrap {A} [Inhabited A] (l : List <| Option A) (prop : l.allSome = true) : List A := 
  l.map (λ o => o.get!)

/-
Take t and jump/drop j for n times.
-/
def List.takeAndJump {A} (t j n : Nat) (l : List A) : List A :=
  match n with
  | 0 => []
  | Nat.succ ns => l.take t ++ (l.drop j).takeAndJump t j ns

namespace Slice

def map {α β : Type u} (f : α → β) (s : Slice α) : Array β :=
  s.ranges.foldl (λ acc srange =>
    acc ++ (srange.toRange.toArray.map (λ i =>
      f <| s.array.get ⟨i, by simp [srange.h2]; sorry⟩
    ))
  ) #[]

def foldl {α β : Type u} (f : α → β → α) (init : α) (s : Slice β) : α :=
  s.ranges.foldl (λ acc srange =>
    srange.toRange.foldl (λ acc i =>
      f acc <| s.array.get ⟨i, by sorry⟩ 
    ) acc
  ) init

end Slice

@[simp] theorem Nat.ge_is_le (n m : Nat) : n ≥ m → m ≤ n := by
  intro h
  exact h

@[simp] theorem Nat.ge_refl (n : Nat) : n ≥ n := by apply ge_is_le; apply Nat.le_refl

structure Bound where
  min : Nat
  max : Nat
  isMinMax : LE.le min max

/-
Bounded Nat
-/
structure BNat (bound : Bound) where
  val  : Nat
  isLe : LE.le val bound.max
  isGe : GE.ge val bound.min

def BNat.succ {bound} (b : BNat bound) : BNat bound :=
  let val := Nat.succ b.val
  if isLe : val ≤ bound.max then
    { val, isLe, isGe := by
      -- apply Nat.ge_is_le;
      simp [b.isGe];
      sorry
    }
  else
    b

def List.weaken {bound} (l : List <| BNat bound) : List Nat := l.map (λ b => b.val)

def BNat.raise {b1 : Bound} (b : BNat b1) (max : Nat) (h : b1.max ≤ max) : BNat <| {b1 with max := max, isMinMax := by simp [Nat.lt_trans]; sorry; } :=
  { val := b.val, isLe := by sorry; /-rw [h]; apply b.isLe; sorry;-/, isGe := b.isGe }

def Nat.toBNat? {b} (n : Nat) : Option <| BNat b :=
  if h : b.min ≤ n ∧ n ≤ b.max then
    some { val:= n, isGe := h.left, isLe := h.right }
  else
    none

theorem le_left_cancel {m n : Nat} : m ≤ m + n := by {
  rw [←Nat.add_zero m]
  apply Nat.add_le_add_left;
  apply Nat.zero_le n;
}

def progression (n m : Nat) /-(bound : Bound := ⟨m, m+n, le_left_cancel⟩)-/ : List Nat :=
  match n with
  | 0 => []
  | Nat.succ ns => m /-{ val := m, isLe := sorry, isGe := sorry }-/ :: (progression ns (Nat.succ m))--.map (λ b : BNat _ => BNat.raise b (max := m+n) (h := by sorry) : BNat bound)

def Fin.toBNat {n} (bound := Bound.mk 0 n (Nat.zero_le n)) (f : Fin n) : BNat <| bound := ⟨f.val, by simp [f.isLt]; sorry, by simp [(Nat.zero_le f.val), Nat.ge_is_le]; sorry;⟩

instance {b} (n : Nat) {h1 : n ≥ b.min} {h2 : n ≤ b.max} : OfNat (BNat b) n where
  ofNat := {val := n, isLe := h2, isGe := h1 }

instance {bound} : ToString (BNat bound) where
  toString b := ToString.toString b.val


instance {b}: Inhabited (BNat b) := ⟨BNat.mk b.min b.isMinMax (by simp)⟩

instance Nat_toBNat {b} (h1 : LE.le n b.max ∧ GE.ge n b.min) : OfNat (BNat b) n := ⟨BNat.mk n h1.left h1.right⟩

theorem BNat.eq_of_val_eq {b} : ∀ {i j : BNat b}, Eq i.val j.val → Eq i j
  | ⟨v, lt, gt⟩, ⟨_, _, _⟩, rfl => rfl

theorem BNat.val_eq_of_eq {b} {i j : BNat b} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

theorem BNat.ne_of_val_ne {b} {i j : BNat b} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

@[simp] theorem BNat.succ_le {b} (n : BNat b) (h : n.val < b.max): Nat.succ n.val ≤ b.max := h

instance (b : Bound): DecidableEq (BNat b) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (BNat.eq_of_val_eq h)
    | isFalse h => isFalse (BNat.ne_of_val_ne h)

instance {bound} : LT (BNat bound) where
  lt a b := LT.lt a.val b.val

instance {bound} : LE (BNat bound) where
  le a b := LE.le a.val b.val

instance BNat.decLt {bound} (a b : BNat bound) : Decidable (LT.lt a b) := Nat.decLt ..
instance BNat.decLe {bound} (a b : BNat bound) : Decidable (LE.le a b) := Nat.decLe ..

@[inline] def Bound.range (b : Bound) : List $ BNat b :=
  let rec @[specialize] it : BNat b → (List $ BNat b) := (λ n => 
    if h : n.val < b.max then
      List.cons n $ it 
        { val := Nat.succ n.val
        , isLe := (by apply h)
        , isGe := (by
          apply Nat.ge_is_le
          apply Nat.le_of_lt
          apply Nat.lt_succ_of_le
          apply n.isGe
        )
        }
    else
      [BNat.mk n.val (by apply n.isLe) n.isGe]
  )
  it (BNat.mk b.min b.isMinMax (by apply Nat.ge_refl))
termination_by _ => b.max - n.val

@[simp] theorem add_le_cancel_right (m n k: Nat) : m ≤ n → m + k ≤ n + k := by
  intro h'
  apply Nat.add_le_add_right
  apply h'

@[simp] theorem mul_ge_one_of_ge_one {a b c : Nat} (ha : a ≥ c ) (hb : b ≥ 1) : a * b ≥ c := 
  --have h1 := Nat.le_refl a ▸ apply ha
  -- inductive a hs
  -- induction a-1 with
  -- | zero =>
  --   apply ha
  -- | succ n =>
  --   apply ha
  -- calc
  --   ha
  --   ... = a * 1 : (mul_one a).symm
  --   ... ≤ a * b : mul_le_mul_left' hb a
  by sorry
  -- rw [Nat.mul_le_mul]

--   rw []
--   ) it
-- instance (b : BNat min max) : Sub Nat b := 

@[simp] theorem one_le_size {h w : Nat} (ax : h ≥ 1 ∧ w ≥ 1) : 1 ≤ h * w := by
  apply mul_ge_one_of_ge_one
  apply ax.left
  apply ax.right
