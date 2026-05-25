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

(*----- Function copy_array -----*)

Definition copy_array_safety_wit_1 := 
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

Definition copy_array_safety_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i + 1 )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l1' 0) = (Znth k_3 ls 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (IntArray.full dst_pre n_pre (app (l1') ((sublist ((i + 1 )) (n_pre) (ld)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition copy_array_entail_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre ld )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l2)) = (n_pre - 0 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - 0 ))) -> ((Znth k_2 l2 0) = (Znth (0 + k_2 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1) (l2)) )
.

Definition copy_array_entail_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2_2: (@list Z)) (l1_2: (@list Z)) (i: Z) (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i + 1 )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l1' 0) = (Znth k_3 ls 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l2_2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1_2 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2_2 0) = (Znth (i + k_2 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1') ((sublist ((i + 1 )) (n_pre) (ld)))) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = (n_pre - (i + 1 ) )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - (i + 1 ) ))) -> ((Znth k_2 l2 0) = (Znth ((i + 1 ) + k_2 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1) (l2)) )
.

Definition copy_array_return_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1) (l2)) )
|--
  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre ls )
.

Definition copy_array_partial_solve_wit_1_pure := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 ls 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1) (l2)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) ld 0))) |]
.

Definition copy_array_partial_solve_wit_1_aux := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 ls 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1) (l2)) )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) ld 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 ls 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1) (l2)) )
.

Definition copy_array_partial_solve_wit_1 := copy_array_partial_solve_wit_1_pure -> copy_array_partial_solve_wit_1_aux.

Definition copy_array_partial_solve_wit_2_pure := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 ls 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (IntArray.missing_i dst_pre i 0 n_pre (app (l1) (l2)) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) ld 0))) |]
.

Definition copy_array_partial_solve_wit_2_aux := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 ls 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app (l1) (l2)) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) ld 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = (Znth k_3 ls 0))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) ld 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app (l1) (l2)) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
.

Definition copy_array_partial_solve_wit_2 := copy_array_partial_solve_wit_2_pure -> copy_array_partial_solve_wit_2_aux.

Definition copy_array_which_implies_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (Znth k ls 0))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) ld 0))) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1) (l2)) )
|--
  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app (l1) (l2)) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ld 0))
.

Definition copy_array_which_implies_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 l1 0) = (Znth k_2 ls 0))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre - i ))) -> ((Znth k_3 l2 0) = (Znth (i + k_3 ) ld 0))) |]
  &&  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app (l1) (l2)) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
|--
  EX (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k l1' 0) = (Znth k ls 0))) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app (l1') ((sublist ((i + 1 )) (n_pre) (ld)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_copy_array_safety_wit_1 : copy_array_safety_wit_1.
Axiom proof_of_copy_array_safety_wit_2 : copy_array_safety_wit_2.
Axiom proof_of_copy_array_entail_wit_1 : copy_array_entail_wit_1.
Axiom proof_of_copy_array_entail_wit_2 : copy_array_entail_wit_2.
Axiom proof_of_copy_array_return_wit_1 : copy_array_return_wit_1.
Axiom proof_of_copy_array_partial_solve_wit_1_pure : copy_array_partial_solve_wit_1_pure.
Axiom proof_of_copy_array_partial_solve_wit_1 : copy_array_partial_solve_wit_1.
Axiom proof_of_copy_array_partial_solve_wit_2_pure : copy_array_partial_solve_wit_2_pure.
Axiom proof_of_copy_array_partial_solve_wit_2 : copy_array_partial_solve_wit_2.
Axiom proof_of_copy_array_which_implies_wit_1 : copy_array_which_implies_wit_1.
Axiom proof_of_copy_array_which_implies_wit_2 : copy_array_which_implies_wit_2.

End VC_Correct.
