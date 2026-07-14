import Std.Data.BitVec

/-
inductive Space where
  | Register | Unique | Ram | Constant
-/

-- Just start with specialized to 64 bits
abbrev Byte := BitVec 8
structure Machine (bits : Nat) where
  spaces : String -> BitVec bits -> Byte
  --ram :  BitVec bits -> Byte
  --register : BitVec bits -> Byte
  --unique :  BitVec bits -> Byte
  addr : BitVec bits
  pcode_pc : Nat
deriving Repr

-- Just keep it a tuple?
structure VarNode (bits : Nat) where
  space : String
  offset : BitVec bits
  size : Nat
deriving Repr


-- state monad style?
/-
I'm somewhat burned by

-/
--def store mach addr value :=
--  {mach | spaces := fun s a => if s == addr.space && s == addr.offset spaces}

/-
def store (space, offset, size) mach :=
  {m | ram :=  fun addr => m.ram}

def select space offset size mach :=
  match space with
  | Ram

def COPY out in1 mach :=
  store out (select in1)

def Copy out in1 : State Machine Unit
def
-/
