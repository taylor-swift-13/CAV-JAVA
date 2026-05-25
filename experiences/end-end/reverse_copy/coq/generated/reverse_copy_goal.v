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

(*----- Function reverse_copy -----*)

Definition reverse_copy_safety_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre ld )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_copy_safety_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
|--
  [| (((n_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((n_pre - 1 ) - i )) |]
.

Definition reverse_copy_safety_wit_3 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition reverse_copy_safety_wit_4 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition reverse_copy_safety_wit_5 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full dst_pre n_pre (replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) ls 0)) ((app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))))) )
  **  (IntArray.full src_pre n_pre ls )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition reverse_copy_entail_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre ld )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - 0 )) (n_pre) (ls))))) ((sublist (0) (n_pre) (ld)))) )
.

Definition reverse_copy_entail_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full dst_pre n_pre (replace_Znth (i) ((Znth ((n_pre - 1 ) - i ) ls 0)) ((app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))))) )
  **  (IntArray.full src_pre n_pre ls )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - (i + 1 ) )) (n_pre) (ls))))) ((sublist ((i + 1 )) (n_pre) (ld)))) )
.

Definition reverse_copy_return_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
|--
  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (rev (ls)) )
.

Definition reverse_copy_partial_solve_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (((src_pre + (((n_pre - 1 ) - i ) * sizeof(INT) ) )) # Int  |-> (Znth ((n_pre - 1 ) - i ) ls 0))
  **  (IntArray.missing_i src_pre ((n_pre - 1 ) - i ) 0 n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
.

Definition reverse_copy_partial_solve_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (((dst_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i dst_pre i 0 n_pre (app ((rev ((sublist ((n_pre - i )) (n_pre) (ls))))) ((sublist (i) (n_pre) (ld)))) )
  **  (IntArray.full src_pre n_pre ls )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_reverse_copy_safety_wit_1 : reverse_copy_safety_wit_1.
Axiom proof_of_reverse_copy_safety_wit_2 : reverse_copy_safety_wit_2.
Axiom proof_of_reverse_copy_safety_wit_3 : reverse_copy_safety_wit_3.
Axiom proof_of_reverse_copy_safety_wit_4 : reverse_copy_safety_wit_4.
Axiom proof_of_reverse_copy_safety_wit_5 : reverse_copy_safety_wit_5.
Axiom proof_of_reverse_copy_entail_wit_1 : reverse_copy_entail_wit_1.
Axiom proof_of_reverse_copy_entail_wit_2 : reverse_copy_entail_wit_2.
Axiom proof_of_reverse_copy_return_wit_1 : reverse_copy_return_wit_1.
Axiom proof_of_reverse_copy_partial_solve_wit_1 : reverse_copy_partial_solve_wit_1.
Axiom proof_of_reverse_copy_partial_solve_wit_2 : reverse_copy_partial_solve_wit_2.

End VC_Correct.
