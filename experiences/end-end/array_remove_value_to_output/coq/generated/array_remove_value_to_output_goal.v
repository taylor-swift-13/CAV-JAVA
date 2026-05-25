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
Require Import array_remove_value_to_output.
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

(*----- Function array_remove_value_to_output -----*)

Definition array_remove_value_to_output_safety_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "write" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_remove_value_to_output_safety_wit_2 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "write" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_remove_value_to_output_safety_wit_3 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i la 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (write) ((Znth i la 0)) (lout)) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  [| ((write + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (write + 1 )) |]
.

Definition array_remove_value_to_output_safety_wit_4 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i la 0) = k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "write" ) )) # Int  |-> write)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full out_pre n_pre lout )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_remove_value_to_output_safety_wit_5 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i la 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (write) ((Znth i la 0)) (lout)) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "write" ) )) # Int  |-> (write + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_remove_value_to_output_entail_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  EX (lout: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (0 = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (0) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < 0)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (0) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
.

Definition array_remove_value_to_output_entail_wit_2_1 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout_2: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i la 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout_2)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout_2 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout_2 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (write) ((Znth i la 0)) (lout_2)) )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (lout: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (write + 1 )) |] 
  &&  [| ((write + 1 ) <= (i + 1 )) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| ((write + 1 ) = (Zlength ((array_remove_value_to_output_spec ((sublist (0) ((i + 1 )) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < (write + 1 ))) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) ((i + 1 )) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , ((((write + 1 ) <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
.

Definition array_remove_value_to_output_entail_wit_2_2 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout_2: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i la 0) = k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout_2)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout_2 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout_2 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout_2 )
|--
  EX (lout: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= (i + 1 )) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) ((i + 1 )) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) ((i + 1 )) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
.

Definition array_remove_value_to_output_entail_wit_3 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout_2: (@list Z)) (write: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout_2)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < write)) -> ((Znth p_3 lout_2 0) = (Znth p_3 (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_4: Z) , (((write <= p_4) /\ (p_4 < n_pre)) -> ((Znth p_4 lout_2 0) = (Znth p_4 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout_2 )
|--
  EX (lout: (@list Z)) ,
  [| (0 <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec (la) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec (la) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |]
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
.

Definition array_remove_value_to_output_return_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout: (@list Z)) (write: Z) ,
  [| (0 <= write) |] 
  &&  [| (write <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec (la) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec (la) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
|--
  EX (tail: (@list Z)) ,
  [| (write = (Zlength ((array_remove_value_to_output_spec (la) (k_pre))))) |] 
  &&  [| ((Zlength (tail)) = (n_pre - (Zlength ((array_remove_value_to_output_spec (la) (k_pre)))) )) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app ((array_remove_value_to_output_spec (la) (k_pre))) (tail)) )
.

Definition array_remove_value_to_output_partial_solve_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout: (@list Z)) (write: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full out_pre n_pre lout )
.

Definition array_remove_value_to_output_partial_solve_wit_2 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i la 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
|--
  [| ((Znth i la 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full out_pre n_pre lout )
.

Definition array_remove_value_to_output_partial_solve_wit_3 := 
forall (out_pre: Z) (k_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lout: (@list Z)) (write: Z) (i: Z) ,
  [| ((Znth i la 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lout )
|--
  [| ((Znth i la 0) <> k_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= write) |] 
  &&  [| (write <= i) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lout)) = n_pre) |] 
  &&  [| (write = (Zlength ((array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre))))) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < write)) -> ((Znth p lout 0) = (Znth p (array_remove_value_to_output_spec ((sublist (0) (i) (la))) (k_pre)) 0))) |] 
  &&  [| forall (p_2: Z) , (((write <= p_2) /\ (p_2 < n_pre)) -> ((Znth p_2 lout 0) = (Znth p_2 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((out_pre + (write * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre write 0 n_pre lout )
  **  (IntArray.full a_pre n_pre la )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_remove_value_to_output_safety_wit_1 : array_remove_value_to_output_safety_wit_1.
Axiom proof_of_array_remove_value_to_output_safety_wit_2 : array_remove_value_to_output_safety_wit_2.
Axiom proof_of_array_remove_value_to_output_safety_wit_3 : array_remove_value_to_output_safety_wit_3.
Axiom proof_of_array_remove_value_to_output_safety_wit_4 : array_remove_value_to_output_safety_wit_4.
Axiom proof_of_array_remove_value_to_output_safety_wit_5 : array_remove_value_to_output_safety_wit_5.
Axiom proof_of_array_remove_value_to_output_entail_wit_1 : array_remove_value_to_output_entail_wit_1.
Axiom proof_of_array_remove_value_to_output_entail_wit_2_1 : array_remove_value_to_output_entail_wit_2_1.
Axiom proof_of_array_remove_value_to_output_entail_wit_2_2 : array_remove_value_to_output_entail_wit_2_2.
Axiom proof_of_array_remove_value_to_output_entail_wit_3 : array_remove_value_to_output_entail_wit_3.
Axiom proof_of_array_remove_value_to_output_return_wit_1 : array_remove_value_to_output_return_wit_1.
Axiom proof_of_array_remove_value_to_output_partial_solve_wit_1 : array_remove_value_to_output_partial_solve_wit_1.
Axiom proof_of_array_remove_value_to_output_partial_solve_wit_2 : array_remove_value_to_output_partial_solve_wit_2.
Axiom proof_of_array_remove_value_to_output_partial_solve_wit_3 : array_remove_value_to_output_partial_solve_wit_3.

End VC_Correct.
