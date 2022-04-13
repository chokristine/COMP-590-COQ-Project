(** Kristine Cho & Richard Gabrielli **)
(** COMP 590: Logical Foundations **)
(** DFA Proof - Final Project **)

(** Goal of this project is to design a generalized DFA type and 
    then provide an example of a DFA. **)

 (** Why doesn\u00b4t this bring in the bool notation? **)
From LF Require Import Basics.
From LF Require Import Lists.
Require Import Bool.
(**Require Import Coq.Lists.List.
Import ListNotations. **)



Inductive nat : Type :=
  | O
  | S (n : nat).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Inductive list (X : Type) : Type :=
| nil
| cons (h : X) (t : list X).


(** Counts the number of items in a list of a specific type (list of states/input)**)
Fixpoint length_of_list (V : Type)(s: list V) : nat :=
  match s with
  | nil _ => O
  | cons _ h t => S (length_of_list V t)
  end.

(** Example test_lol1 : length_of_list nat [1;2;3] = 3. **)

(** ----------------------------- Start: Encountered Issue pt.1 ------------------------------------

The motivation behind this code below is to count the occurences of an item in a list in a totally
Polymorphic way. The issue encountered with this is is actually calculating if the HEAD of a 
list is equivalent to the item we want to know the number occurrances of.

Doing this in a polymorphic way is difficult because when the eqbt function is written,
matching n leaves a gap. The downfall of this is that for every dfa, this function will have to
be written specifically to the wanted dfa.


Fixpoint eqbt (n m : Type) : bool :=
  match n with
  | m => true
  | _ => false          (THIS is the failure point!)
end.


Fixpoint count_occurrences_of_item (V : Type) (s : list V) (x : V) : nat := 
  match s with
    | nil _ => O
    | cons _ h t => 
      match eqbt h x with
        | true => S ( count_occurrences_of_item V t x)
        | false => (count_occurrences_of_item V t x)
        end 
end.

-------------------------------------- End: Encountered Issue pt.1 ---------------------------------- **)

(** ---------------------------------- Start: A More General Definition of DFA ----------------------------**)

Record dfa (State : Type) (Alphabet : Type) := DFA {
  start_state : State;
  all_states : list State;
  is_accepting_state : State -> bool;
  transition : State -> Alphabet -> State;
}.

(** ---------------------------------- End: A More General Definition of DFA ----------------------------**)

(** ------------------------------ Start: Example DFA 1 -------------------------------------------- **)

(** This DFA has the properties 

Alphbet: {0, 1} 
States: {A, B}
Start State: A
Accepting State: A 
Transition Function (Current, Input, Next): 
         {
             (A, 0, A)
             (A, 1, B)
             (B, 0, B)
            (B, 1, B)
       } 
Accepted Language: All strings containing an even number of 1's
**)


Inductive dfa1_alphabet : Type := 
| one
| zero.

Inductive dfa1_states : Type :=
| A
| B.

(** s indicates it is a list of states, a indicates it is a list alphabet input **)
Notation "s[ x ; .. ; y ]" := (cons dfa1_states  x .. (cons dfa1_states y(nil dfa1_states))..).
Notation "a[ x ; .. ; y ]" := (cons dfa1_alphabet  x .. (cons dfa1_alphabet y(nil dfa1_alphabet))..).

Example test1 : length_of_list dfa1_alphabet a[one;zero] = S(S O). 
Proof. simpl. reflexivity. Qed.

Definition dfa1 : dfa dfa1_states dfa1_alphabet := {|
  start_state := A;
  all_states := s[A;B];
  is_accepting_state state := 
  match state with 
  | A => true
  | B => false end; 
  transition s x :=
    match s, x with
    | A, zero => A
    | A, one => B
    | B, zero => B
    | B, one => A
    end;
|}.


(** To show that this DFA only accepts input with even number of 1's
we must first define what evenness is, then count how many 1's there are.
This is done with the following fixpoint **)

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Fixpoint count_occurrences_of_ones (s : list dfa1_alphabet) : nat := 
  match s with
    | nil _ => O
    | cons _ h t => 
      match h with
        | one => S ( count_occurrences_of_ones t)
        | zero => (count_occurrences_of_ones t)
        end 
end.

Example test_even_ones_true : even (count_occurrences_of_ones a[one;one]) = true.
Proof. simpl. reflexivity. Qed.

Example test_even_ones_false : even (count_occurrences_of_ones a[one;zero]) = false.
Proof. simpl. reflexivity. Qed.

(** Now we will get to the more interesting part of this example...proving that **)

(*------------------------------------DFA accepts all lists with even number of 1s-----------------------------*)
Definition dfa1_accept (is_accepting_state : bool):=
  if is_accepting_state then true else false.


(** ------------------------------ End: Example DFA 1 -------------------------------------------- **)

















