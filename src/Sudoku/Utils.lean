universe u v

def Slices (A : Type u) : Type u := Array $ Subarray A

def slice {A : Type u} (as : Array A) (ranges : Array ((Fin (as.size + 1)) × (Fin (as.size+1)))) : Slices A :=
  Array.map (fun (start, stop) =>
    as.toSubarray start.val stop.val
  ) ranges


def Subarray.unique {A : Type u} [BEq A] (s : Subarray A) : Bool :=
  (s.foldl (λ (b, arr) a => if b && !arr.contains a then (b, arr.push a) else (false, arr)) (true, #[])).fst

/-
Bounded Nat
-/
structure BNat (min max : Nat) (isMinMax : LE.le min max)where
  val  : Nat
  isLe : LE.le val max
  isGe : GE.ge val min

def Nat.toBNat {min max} {h : min ≤ max} (n : Nat) : Option <| BNat min max h :=
  if h : min ≤ n ∧ n ≤ max then
    some { val:= n, isGe := h.left, isLe := h.right }
  else
    none
    

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

theorem range_terminates {min max} {h : min ≤ max} (n : BNat min max h): max - Nat.succ n.val ≤ max - n.val := by sorry

@[inline] partial def BNat.range {min max} {h' : min ≤ max} : List $ BNat min max h' :=
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
-- termination_by measure λ b => b.snd.fst - b.snd.snd.snd.val
-- decreasing_by exact range_terminates

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
