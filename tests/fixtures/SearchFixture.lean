import Lean

/- Small, compiled corpus for search regression tests. Regenerate its JSONL
   with the ignored `live_lean_search` test and DISCRTREE_LEAN set to Lean. -/
namespace SearchFixture

theorem succ_add (n : Nat) : Nat.succ n = n + 1 := rfl
theorem add_comm (n m : Nat) : n + m = m + n := Nat.add_comm n m
theorem mul_comm (n m : Nat) : n * m = m * n := Nat.mul_comm n m
theorem pow_two (n : Nat) : n ^ 2 = n * n := by simp [Nat.pow_succ]
theorem mul_nonneg (n : Nat) : 0 ≤ n * n := Nat.zero_le _
theorem succ_pos (n : Nat) : 0 < Nat.succ n := Nat.zero_lt_succ n
theorem succ_ne_zero (n : Nat) : Nat.succ n ≠ 0 := Nat.succ_ne_zero n
theorem not_succ_zero (n : Nat) : ¬ Nat.succ n = 0 := Nat.succ_ne_zero n
theorem exists_succ : ∃ n : Nat, Nat.succ n = 1 := ⟨0, rfl⟩
theorem not_exists : ¬ (∃ n : Nat, Nat.succ n = 0) := by
  rintro ⟨n, h⟩
  exact Nat.succ_ne_zero n h
theorem iff_and (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := And.comm
theorem implication (p q : Prop) : (p → q) → p → q := fun h hp => h hp
theorem equality_hypothesis (n m : Nat) : n = m → Nat.succ n = Nat.succ m :=
  fun h => congrArg Nat.succ h
theorem forall_body (f : Nat → Nat) : ∀ n : Nat, f n = f n := fun _ => rfl
theorem shadowed_id (id : Nat) : id + id = id + id := rfl
theorem shadowed_Nat (Nat : Type) (n : Nat) : n = n := rfl
theorem scoped_shadow : (∀ Nat : Type, ∀ n : Nat, n = n) ∧ Nat.succ 0 = 1 :=
  ⟨fun _ _ => rfl, rfl⟩
theorem not_mem_iff (n : Nat) (xs : List Nat) : ¬ n ∈ xs ↔ n ∉ xs := Iff.rfl
theorem not_implication (p : Prop) (hp : p) : ¬ (p → False) := fun h => h hp
theorem exists_function : ∃ f : Nat → Nat, f 0 = 0 := ⟨fun _ => 0, rfl⟩
theorem exists_implication : ∃ n : Nat, n = 0 → Nat.succ n = 1 := ⟨0, fun _ => rfl⟩

def TypePred (α : Type) : Prop := Nonempty α
theorem function_type : TypePred (Nat → Nat) := ⟨fun _ => 0⟩
theorem nested_function_type : TypePred ((Nat → Nat) → Nat) := ⟨fun _ => 0⟩
theorem list_type : TypePred (List Nat) := ⟨[]⟩
theorem prop_type : TypePred Prop := ⟨True⟩

class Witness (α : Type) where
  witness : α
instance natWitness : Witness Nat := ⟨0⟩

theorem append_nil (xs : List Nat) : xs ++ [] = xs := List.append_nil xs
theorem append_length (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length :=
  List.length_append
theorem reverse_reverse (xs : List Nat) : xs.reverse.reverse = xs := List.reverse_reverse xs
theorem head_cons (n : Nat) (xs : List Nat) : (n :: xs).head? = some n := rfl
theorem getElem_cons (n : Nat) (xs : List Nat) : (n :: xs)[0]? = some n := rfl
theorem nil_mem (n : Nat) : n ∉ ([] : List Nat) := List.not_mem_nil
theorem cons_mem (n : Nat) (xs : List Nat) : n ∈ n :: xs := List.mem_cons_self
theorem option_map (n : Nat) : Option.map Nat.succ (some n) = some (Nat.succ n) := rfl
theorem pair_fst (n m : Nat) : Prod.fst (n, m) = n := rfl
theorem pair_eq (n m : Nat) : (n, m) = (n, m) := rfl
theorem pair_iff (n m a b : Nat) : (n, m) = (a, b) ↔ n = a ∧ m = b := by simp

abbrev Alias := List Nat
theorem alias_type : TypePred Alias := ⟨[]⟩

/-- A fixture documenting addition and its symmetry. -/
theorem documented (n m : Nat) : n + m = m + n := Nat.add_comm n m
theorem admitted (n : Nat) : Nat.succ n = n := by sorry
theorem Γ_eq (n : Nat) : n = n := rfl
theorem γ_eq (n : Nat) : n = n := rfl

theorem boolean_beq (n m : Nat) : (n == m) = (n == m) := rfl
theorem boolean_and (p q : Bool) : (p && q) = (p && q) := rfl
theorem boolean_or (p q : Bool) : (p || q) = (p || q) := rfl
theorem boolean_xor (p q : Bool) : (p ^^ q) = (p ^^ q) := rfl
theorem boolean_not (p : Bool) : (!p) = !p := rfl
theorem bit_shift_left (n m : Nat) : (n <<< m) = (n <<< m) := rfl
theorem bit_shift_right (n m : Nat) : (n >>> m) = (n >>> m) := rfl
theorem bit_and (n m : Nat) : (n &&& m) = (n &&& m) := rfl
theorem bit_or (n m : Nat) : (n ||| m) = (n ||| m) := rfl
theorem bit_xor (n m : Nat) : (n ^^^ m) = (n ^^^ m) := rfl
theorem bit_complement (n : UInt8) : (~~~n) = ~~~n := rfl
theorem equality_rhs_not (p : Prop) : (¬p) = ¬p := rfl
theorem list_literal (n m : Nat) : [n, m] = n :: m :: [] := rfl
theorem list_empty : ([] : List Nat) = [] := rfl
theorem list_literal_length (n m : Nat) : [n, m].length = 2 := rfl
theorem list_empty_length : ([] : List Nat).length = 0 := rfl
theorem conditional (n m : Nat) :
    (if n ≤ m then n + 1 else m * 2) = (if n ≤ m then n + 1 else m * 2) := rfl
theorem conditional_add (n m : Nat) :
    n + (if n ≤ m then 1 else 0) = n + (if n ≤ m then 1 else 0) := rfl

def «arrow → + /- sorry» (n : Nat) := n
def «has.dot» (n : Nat) := n
theorem escaped_head (n : Nat) : «arrow → + /- sorry» n = n := rfl
theorem escaped_dot (n : Nat) : «has.dot» n = n := rfl
theorem nat_type : TypePred Nat := ⟨0⟩
theorem subtype_type : TypePred { id : Nat // id = id } := ⟨⟨0, rfl⟩⟩
theorem dependent_exists : ∃ (Carrier : Type) (value : Carrier), True := ⟨Nat, 0, trivial⟩
theorem succ_mem_cons (n : Nat) (xs : List Nat) : Nat.succ n ∈ Nat.succ n :: xs := List.mem_cons_self
theorem succ_heq (n : Nat) : Nat.succ n ≍ Nat.succ n := HEq.rfl
theorem lambda_pair : ((fun n : Nat => n), 0) = ((fun n : Nat => n), 0) := rfl
theorem lambda_match_field (xs : List Nat) :
    (List.map (fun n => match n with | 0 => 0 | n + 1 => n) xs).reverse =
    (List.map (fun n => match n with | 0 => 0 | n + 1 => n) xs).reverse := rfl

theorem nat_cast_zero : (↑(0 : Nat) : Int) = 0 := rfl
theorem nat_cast_field (a : Int) : (↑a.natAbs : Int) = ↑a.natAbs := rfl
theorem iff_imp_left (p q : Prop) : (p → q) ↔ (p → q) := Iff.rfl
theorem iff_imp_right (p q : Prop) (hq : q) : p ↔ q → p := by
  constructor
  · exact fun hp _ => hp
  · exact fun h => h hq
theorem option_seq (f : Option (Nat → Nat)) (a : Option Nat) : (f <*> a) = f <*> a := rfl
theorem option_seq_left (a b : Option Nat) : (a <* b) = a <* b := rfl
theorem option_seq_right (a b : Option Nat) : (a *> b) = a *> b := rfl
theorem option_then {α : Type} [AndThen α] (a b : α) : (a >> b) = a >> b := rfl
theorem option_fmap (f : Nat → Nat) (a : Option Nat) : (f <$> a) = f <$> a := rfl
theorem neg_bit_or (a : UInt8) : (a ||| -1) = a ||| -1 := rfl
theorem constant_receiver_field : Ordering.gt.isGE = true := rfl
theorem raw_record (n : Nat) : ({ byteIdx := n } : String.Pos.Raw) = { byteIdx := n } := rfl
theorem anonymous_fin (n : Nat) : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ := rfl
theorem range_list (n m : Nat) : (n...m).toList = (n...m).toList := rfl
theorem range_closed (n m : Nat) : (n...=m) = (n...=m) := rfl
theorem range_unbounded (n : Nat) : (n...*) = (n...*) := rfl
theorem range_bounds (n m : Nat) : ((n + 1)...m).toList = ((n + 1)...m).toList := rfl
theorem range_closed_open (n m : Nat) : (n...<m) = (n...<m) := rfl
theorem range_open (n m : Nat) : (n<...m) = (n<...m) := rfl
theorem range_open_open (n m : Nat) : (n<...<m) = (n<...<m) := rfl
theorem range_open_closed (n m : Nat) : (n<...=m) = (n<...=m) := rfl
theorem range_open_unbounded (n : Nat) : (n<...*) = (n<...*) := rfl
theorem range_unbounded_open (m : Nat) : (*...m) = (*...m) := rfl
theorem range_unbounded_open_alias (m : Nat) : (*...<m) = (*...<m) := rfl
theorem range_unbounded_closed (m : Nat) : (*...=m) = (*...=m) := rfl
theorem range_all : (*...* : Std.Rii Nat) = *...* := rfl
theorem let_shadow (n : Nat) : let id := Nat.succ n; id = id := rfl
theorem have_shadow (n : Nat) : have id := Nat.succ n; id = id := rfl

class Interleaved (α : Type) [Inhabited α] (β : Type) : Prop where
  witness : True
instance interleavedNatInt : Interleaved Nat Int := ⟨trivial⟩
theorem interleaved_type : Interleaved Nat Int := inferInstance

theorem nat_type_equality : Nat = Nat := rfl
def BiTypePred (α β : Type) : Prop := True
theorem bitype_nat_int : BiTypePred Nat Int := trivial
theorem bitype_int_nat : BiTypePred Int Nat := trivial

theorem array_literal (n m : Nat) : #[n, m] = #[n, m] := rfl
theorem array_empty : (#[] : Array Nat) = #[] := rfl
theorem array_literal_size (n m : Nat) : #[n, m].size = 2 := rfl
theorem string_literal : "Nat.succ + ∀ → [id]" = "Nat.succ + ∀ → [id]" := rfl
theorem string_literal_length : "a → \"foo\"".length = "a → \"foo\"".length := rfl
theorem char_literal : 'a' = 'a' := rfl
theorem char_literal_symbol : '→' = '→' := rfl
theorem char_literal_quote : '\'' = '\'' := rfl
theorem scientific_literal : (1.25 : Float) = 1.25 := rfl
theorem scientific_literal_exponent : (1.25e3 : Float) = 1.25e3 := rfl
theorem scientific_literal_negative_exponent : (1.25e-3 : Float) = 1.25e-3 := rfl
theorem hex_literal : (0xff : Nat) = 255 := rfl

class InterleavedValues (n : Nat) [Inhabited Nat] (m : Nat) : Prop where
  witness : True
instance interleavedValues (n m : Nat) : InterleavedValues n m := ⟨trivial⟩
theorem interleaved_powers (n : Nat) : InterleavedValues (n ^ 2) (n * n) := inferInstance
theorem pow_exponents (n m : Nat) (h : n ^ 3 = m ^ 2) : n ^ 3 = m ^ 2 := h
theorem pow_heq (n : Nat) : (n ^ 2) ≍ (n * n) := heq_of_eq (Nat.pow_two n)

def TypedValue {α : Type} (value : α) : α := value
theorem typed_nat (n : Nat) : TypedValue n = n := rfl
theorem typed_int (n : Int) : TypedValue n = n := rfl
theorem typed_nat_mentions_int (n : Nat) (_z : Int) : TypedValue n = n := rfl
theorem typed_generic {α : Type} (value : α) : TypedValue value = value := rfl
theorem typed_list_nat (ns : List Nat) : TypedValue ns = ns := rfl
theorem typed_list_int (zs : List Int) : TypedValue zs = zs := rfl
theorem typed_function (f : Nat → Nat) : TypedValue f = f := rfl
theorem typed_higher_type {F : Type → Type} (value : F Nat) : TypedValue value = value := rfl

def SameArgs {α : Type} (_x _y : α) : Prop := True
theorem typed_same_generic {α : Type} (x y : α) : SameArgs x y := trivial
theorem typed_same_nat (n m : Nat) : SameArgs n m := trivial

theorem numeral_zero : TypedValue (0 : Nat) = 0 := rfl
theorem numeral_one : TypedValue (1 : Nat) = 1 := rfl
theorem numeral_two : TypedValue (2 : Nat) = 2 := rfl
theorem numeral_zero_mentions_one (n : Nat) (_h : n = 1) : TypedValue (0 : Nat) = 0 := rfl
theorem numeral_one_reversed : 1 = TypedValue (1 : Nat) := rfl
theorem numeral_nested_one (n : Nat) : TypedValue (n + 1) = n + 1 := rfl
theorem numeral_nested_two (n : Nat) : TypedValue (n + 2) = n + 2 := rfl
theorem numeral_negative_one : TypedValue (-1 : Int) = -1 := rfl
theorem numeral_negative_two : TypedValue (-2 : Int) = -2 := rfl
theorem numeral_large :
    TypedValue (340282366920938463463374607431768211456 : Nat) =
      340282366920938463463374607431768211456 := rfl
theorem numeral_hex : TypedValue (0xff : Nat) = 255 := rfl
theorem numeral_scientific : TypedValue (1.25 : Float) = 1.25 := rfl
theorem numeral_scientific_other : TypedValue (1.5 : Float) = 1.5 := rfl
theorem numeral_scientific_positive_exponent : TypedValue (1.25e3 : Float) = 1.25e3 := rfl
theorem numeral_scientific_negative_exponent : TypedValue (1.25e-3 : Float) = 1.25e-3 := rfl
theorem numeral_scientific_trailing_zeroes : TypedValue (1.2500 : Float) = 1.2500 := rfl
theorem numeral_scientific_zero : TypedValue (0.00e30 : Float) = 0.00e30 := rfl
theorem numeral_fin_three : TypePred (Fin 3) := ⟨⟨0, by decide⟩⟩
theorem numeral_fin_four : TypePred (Fin 4) := ⟨⟨0, by decide⟩⟩

end SearchFixture
