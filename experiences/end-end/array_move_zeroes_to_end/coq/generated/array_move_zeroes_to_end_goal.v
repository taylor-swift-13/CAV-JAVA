Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_move_zeroes_to_end.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function array_move_zeroes_to_end -----*)

Definition array_move_zeroes_to_end_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "write" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_move_zeroes_to_end_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "write" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_move_zeroes_to_end_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_move_zeroes_to_end_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i lc 0) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (write) ((Znth i lc 0)) (lc)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((write + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (write + 1 )) |]
.

Definition array_move_zeroes_to_end_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i lc 0) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_move_zeroes_to_end_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i lc 0) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (write) ((Znth i lc 0)) (lc)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "write" ) )) # Int  |-> (write + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_move_zeroes_to_end_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) (lc_2: (@list Z)) (write_2: Z) ,
  [| (write_2 < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write_2) |] 
  &&  [| (write_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_4: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_4) /\ (k_4 < write_2)) -> ((Znth k_4 lc_2 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "write" ) )) # Int  |-> write_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre write_2 0 n_pre lc_2 )
  **  (((a_pre + (write_2 * sizeof(INT) ) )) # Int  |-> (Znth write_2 lc_2 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_move_zeroes_to_end_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write_2: Z) (i: Z) (lc_2: (@list Z)) (write: Z) (lc1: (@list Z)) ,
  [| ((Zlength (lc1)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc1 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < (write + 1 ))) -> ((Znth k_6 lc1 0) = 0)) |] 
  &&  [| (write < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_4: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_4) /\ (k_4 < write)) -> ((Znth k_4 lc_2 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write_2) |] 
  &&  [| (write_2 <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write_2 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write_2)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre lc1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((write + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (write + 1 )) |]
.

Definition array_move_zeroes_to_end_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (0 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (0) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (0) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_move_zeroes_to_end_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i lc_2 0) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc_2 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth (write) ((Znth i lc_2 0)) (lc_2)) )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (write + 1 )) |] 
  &&  [| ((write + 1 ) <= (i + 1 )) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| ((write + 1 ) = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) ((i + 1 )) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (write + 1 ))) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) ((i + 1 )) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , ((((i + 1 ) <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_move_zeroes_to_end_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i lc_2 0) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc_2 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc_2 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  EX (lc: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= (i + 1 )) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) ((i + 1 )) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) ((i + 1 )) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , ((((i + 1 ) <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_move_zeroes_to_end_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  EX (lc_2: (@list Z)) ,
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_4: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_4) /\ (k_4 < write)) -> ((Znth k_4 lc_2 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
.

Definition array_move_zeroes_to_end_entail_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) (lc_3: (@list Z)) (write_2: Z) (lc1: (@list Z)) ,
  [| ((Zlength (lc1)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc1 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < (write_2 + 1 ))) -> ((Znth k_6 lc1 0) = 0)) |] 
  &&  [| (write_2 < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write_2) |] 
  &&  [| (write_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_3)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_3 lc_3 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_4: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_4) /\ (k_4 < write_2)) -> ((Znth k_4 lc_3 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc1 )
|--
  EX (lc_2: (@list Z)) ,
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= (write_2 + 1 )) |] 
  &&  [| ((write_2 + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_4: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_4) /\ (k_4 < (write_2 + 1 ))) -> ((Znth k_4 lc_2 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
.

Definition array_move_zeroes_to_end_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) (lc_2: (@list Z)) (write_2: Z) ,
  [| (write_2 >= n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write_2) |] 
  &&  [| (write_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_4: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_4) /\ (k_4 < write_2)) -> ((Znth k_4 lc_2 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc_2 )
|--
  [| ((Zlength ((array_move_zeroes_to_end_spec (l)))) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (array_move_zeroes_to_end_spec (l)) )
.

Definition array_move_zeroes_to_end_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lc 0))
  **  (IntArray.missing_i a_pre i 0 n_pre lc )
.

Definition array_move_zeroes_to_end_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i lc 0) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i lc 0) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lc 0))
  **  (IntArray.missing_i a_pre i 0 n_pre lc )
.

Definition array_move_zeroes_to_end_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i lc 0) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Znth i lc 0) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < write)) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_2: Z) , (((i <= k_2) /\ (k_2 < n_pre)) -> ((Znth k_2 lc 0) = (Znth k_2 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (write * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre write 0 n_pre lc )
.

Definition array_move_zeroes_to_end_partial_solve_wit_4_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (write_2: Z) (i: Z) (lc: (@list Z)) (write: Z) ,
  [| (write < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < write)) -> ((Znth k_6 lc 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write_2) |] 
  &&  [| (write_2 <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write_2 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < write_2)) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lc_2 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre lc )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_2: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_2) /\ (k_2 < write)) -> ((Znth k_2 lc 0) = 0)) |]
.

Definition array_move_zeroes_to_end_partial_solve_wit_4_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (write_2: Z) (i: Z) (lc: (@list Z)) (write: Z) ,
  [| (write < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < write)) -> ((Znth k_6 lc 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write_2) |] 
  &&  [| (write_2 <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write_2 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < write_2)) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lc_2 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
|--
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_2: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_2) /\ (k_2 < write)) -> ((Znth k_2 lc 0) = 0)) |] 
  &&  [| (write < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < write)) -> ((Znth k_6 lc 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write_2) |] 
  &&  [| (write_2 <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write_2 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < write_2)) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lc_2 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre lc )
.

Definition array_move_zeroes_to_end_partial_solve_wit_4 := array_move_zeroes_to_end_partial_solve_wit_4_pure -> array_move_zeroes_to_end_partial_solve_wit_4_aux.

Definition array_move_zeroes_to_end_partial_solve_wit_5_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (write_2: Z) (i: Z) (lc: (@list Z)) (write: Z) ,
  [| (write < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < write)) -> ((Znth k_6 lc 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write_2) |] 
  &&  [| (write_2 <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write_2 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < write_2)) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lc_2 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre write 0 n_pre lc )
  **  (((a_pre + (write * sizeof(INT) ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_2: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_2) /\ (k_2 < write)) -> ((Znth k_2 lc 0) = 0)) |]
.

Definition array_move_zeroes_to_end_partial_solve_wit_5_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (lc_2: (@list Z)) (write_2: Z) (i: Z) (lc: (@list Z)) (write: Z) ,
  [| (write < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < write)) -> ((Znth k_6 lc 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write_2) |] 
  &&  [| (write_2 <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write_2 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < write_2)) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lc_2 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.missing_i a_pre write 0 n_pre lc )
  **  (((a_pre + (write * sizeof(INT) ) )) # Int  |-> 0)
|--
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_2: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_2) /\ (k_2 < write)) -> ((Znth k_2 lc 0) = 0)) |] 
  &&  [| (write < n_pre) |] 
  &&  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_5 lc 0) = (Znth k_5 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_6: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_6) /\ (k_6 < write)) -> ((Znth k_6 lc 0) = 0)) |] 
  &&  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write_2) |] 
  &&  [| (write_2 <= i) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc_2)) = n_pre) |] 
  &&  [| (write_2 = (Zlength ((array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l))))))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < write_2)) -> ((Znth k_3 lc_2 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero ((sublist (0) (i) (l)))) 0))) |] 
  &&  [| forall (k_4: Z) , (((i <= k_4) /\ (k_4 < n_pre)) -> ((Znth k_4 lc_2 0) = (Znth k_4 l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.missing_i a_pre write 0 n_pre lc )
  **  (((a_pre + (write * sizeof(INT) ) )) # Int  |-> 0)
.

Definition array_move_zeroes_to_end_partial_solve_wit_5 := array_move_zeroes_to_end_partial_solve_wit_5_pure -> array_move_zeroes_to_end_partial_solve_wit_5_aux.

Definition array_move_zeroes_to_end_which_implies_wit_1 := 
forall (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (a: Z) ,
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k lc 0) = (Znth k (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_2: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_2) /\ (k_2 < write)) -> ((Znth k_2 lc 0) = 0)) |]
  &&  (IntArray.full a n_pre lc )
|--
  (IntArray.missing_i a write 0 n_pre lc )
  **  (((a + (write * sizeof(INT) ) )) # Int  |-> (Znth write lc 0))
.

Definition array_move_zeroes_to_end_which_implies_wit_2 := 
forall (n_pre: Z) (l: (@list Z)) (lc: (@list Z)) (write: Z) (a: Z) ,
  [| ((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= write) |] 
  &&  [| (write < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (lc)) = n_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k_3 lc 0) = (Znth k_3 (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_4: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_4) /\ (k_4 < write)) -> ((Znth k_4 lc 0) = 0)) |]
  &&  (IntArray.missing_i a write 0 n_pre lc )
  **  (((a + (write * sizeof(INT) ) )) # Int  |-> 0)
|--
  EX (lc1: (@list Z)) ,
  [| ((Zlength (lc1)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((array_move_zeroes_to_end_nonzero (l)))))) -> ((Znth k lc1 0) = (Znth k (array_move_zeroes_to_end_nonzero (l)) 0))) |] 
  &&  [| forall (k_2: Z) , ((((Zlength ((array_move_zeroes_to_end_nonzero (l)))) <= k_2) /\ (k_2 < (write + 1 ))) -> ((Znth k_2 lc1 0) = 0)) |]
  &&  (IntArray.full a n_pre lc1 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_move_zeroes_to_end_safety_wit_1 : array_move_zeroes_to_end_safety_wit_1.
Axiom proof_of_array_move_zeroes_to_end_safety_wit_2 : array_move_zeroes_to_end_safety_wit_2.
Axiom proof_of_array_move_zeroes_to_end_safety_wit_3 : array_move_zeroes_to_end_safety_wit_3.
Axiom proof_of_array_move_zeroes_to_end_safety_wit_4 : array_move_zeroes_to_end_safety_wit_4.
Axiom proof_of_array_move_zeroes_to_end_safety_wit_5 : array_move_zeroes_to_end_safety_wit_5.
Axiom proof_of_array_move_zeroes_to_end_safety_wit_6 : array_move_zeroes_to_end_safety_wit_6.
Axiom proof_of_array_move_zeroes_to_end_safety_wit_7 : array_move_zeroes_to_end_safety_wit_7.
Axiom proof_of_array_move_zeroes_to_end_safety_wit_8 : array_move_zeroes_to_end_safety_wit_8.
Axiom proof_of_array_move_zeroes_to_end_entail_wit_1 : array_move_zeroes_to_end_entail_wit_1.
Axiom proof_of_array_move_zeroes_to_end_entail_wit_2_1 : array_move_zeroes_to_end_entail_wit_2_1.
Axiom proof_of_array_move_zeroes_to_end_entail_wit_2_2 : array_move_zeroes_to_end_entail_wit_2_2.
Axiom proof_of_array_move_zeroes_to_end_entail_wit_3 : array_move_zeroes_to_end_entail_wit_3.
Axiom proof_of_array_move_zeroes_to_end_entail_wit_4 : array_move_zeroes_to_end_entail_wit_4.
Axiom proof_of_array_move_zeroes_to_end_return_wit_1 : array_move_zeroes_to_end_return_wit_1.
Axiom proof_of_array_move_zeroes_to_end_partial_solve_wit_1 : array_move_zeroes_to_end_partial_solve_wit_1.
Axiom proof_of_array_move_zeroes_to_end_partial_solve_wit_2 : array_move_zeroes_to_end_partial_solve_wit_2.
Axiom proof_of_array_move_zeroes_to_end_partial_solve_wit_3 : array_move_zeroes_to_end_partial_solve_wit_3.
Axiom proof_of_array_move_zeroes_to_end_partial_solve_wit_4_pure : array_move_zeroes_to_end_partial_solve_wit_4_pure.
Axiom proof_of_array_move_zeroes_to_end_partial_solve_wit_4 : array_move_zeroes_to_end_partial_solve_wit_4.
Axiom proof_of_array_move_zeroes_to_end_partial_solve_wit_5_pure : array_move_zeroes_to_end_partial_solve_wit_5_pure.
Axiom proof_of_array_move_zeroes_to_end_partial_solve_wit_5 : array_move_zeroes_to_end_partial_solve_wit_5.
Axiom proof_of_array_move_zeroes_to_end_which_implies_wit_1 : array_move_zeroes_to_end_which_implies_wit_1.
Axiom proof_of_array_move_zeroes_to_end_which_implies_wit_2 : array_move_zeroes_to_end_which_implies_wit_2.

End VC_Correct.
