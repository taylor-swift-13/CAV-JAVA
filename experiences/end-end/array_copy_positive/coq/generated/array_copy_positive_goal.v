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

(*----- Function array_copy_positive -----*)

Definition array_copy_positive_safety_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_copy_positive_safety_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full out_pre n_pre lr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_copy_positive_safety_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full out_pre n_pre lr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_copy_positive_safety_wit_4 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i) (0) (lr)) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_copy_positive_safety_wit_5 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i) ((Znth i la 0)) (lr)) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_copy_positive_entail_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < 0)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < 0)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_copy_positive_entail_wit_2_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr_2: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr_2)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr_2 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr_2 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr_2 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i) ((Znth i la 0)) (lr_2)) )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < (i + 1 ))) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , ((((i + 1 ) <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_copy_positive_entail_wit_2_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr_2: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr_2)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr_2 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr_2 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr_2 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i) (0) (lr_2)) )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (lr: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < (i + 1 ))) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , ((((i + 1 ) <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_copy_positive_entail_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr_2: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr_2)) = n_pre) |] 
  &&  [| forall (k_3: Z) , ((((0 <= k_3) /\ (k_3 < i)) /\ ((Znth k_3 la 0) > 0)) -> ((Znth k_3 lr_2 0) = (Znth k_3 la 0))) |] 
  &&  [| forall (k_4: Z) , ((((0 <= k_4) /\ (k_4 < i)) /\ ((Znth k_4 la 0) <= 0)) -> ((Znth k_4 lr_2 0) = 0)) |] 
  &&  [| forall (k_5: Z) , (((i <= k_5) /\ (k_5 < n_pre)) -> ((Znth k_5 lr_2 0) = (Znth k_5 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr_2 )
|--
  EX (lr: (@list Z)) ,
  [| (i = n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < n_pre)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < n_pre)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_copy_positive_return_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr_2: (@list Z)) (i_2: Z) ,
  [| (i_2 = n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr_2)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < n_pre)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr_2 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < n_pre)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr_2 0) = 0)) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr_2 )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((Znth i la 0) > 0) -> ((Znth i lr 0) = (Znth i la 0))) /\ (((Znth i la 0) <= 0) -> ((Znth i lr 0) = 0)))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_copy_positive_partial_solve_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_copy_positive_partial_solve_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
|--
  [| ((Znth i la 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_copy_positive_partial_solve_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
|--
  [| ((Znth i la 0) > 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre i 0 n_pre lr )
  **  (IntArray.full a_pre n_pre la )
.

Definition array_copy_positive_partial_solve_wit_4 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (lr: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
|--
  [| ((Znth i la 0) <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (k: Z) , ((((0 <= k) /\ (k < i)) /\ ((Znth k la 0) > 0)) -> ((Znth k lr 0) = (Znth k la 0))) |] 
  &&  [| forall (k_2: Z) , ((((0 <= k_2) /\ (k_2 < i)) /\ ((Znth k_2 la 0) <= 0)) -> ((Znth k_2 lr 0) = 0)) |] 
  &&  [| forall (k_3: Z) , (((i <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 lr 0) = (Znth k_3 lo 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre i 0 n_pre lr )
  **  (IntArray.full a_pre n_pre la )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_copy_positive_safety_wit_1 : array_copy_positive_safety_wit_1.
Axiom proof_of_array_copy_positive_safety_wit_2 : array_copy_positive_safety_wit_2.
Axiom proof_of_array_copy_positive_safety_wit_3 : array_copy_positive_safety_wit_3.
Axiom proof_of_array_copy_positive_safety_wit_4 : array_copy_positive_safety_wit_4.
Axiom proof_of_array_copy_positive_safety_wit_5 : array_copy_positive_safety_wit_5.
Axiom proof_of_array_copy_positive_entail_wit_1 : array_copy_positive_entail_wit_1.
Axiom proof_of_array_copy_positive_entail_wit_2_1 : array_copy_positive_entail_wit_2_1.
Axiom proof_of_array_copy_positive_entail_wit_2_2 : array_copy_positive_entail_wit_2_2.
Axiom proof_of_array_copy_positive_entail_wit_3 : array_copy_positive_entail_wit_3.
Axiom proof_of_array_copy_positive_return_wit_1 : array_copy_positive_return_wit_1.
Axiom proof_of_array_copy_positive_partial_solve_wit_1 : array_copy_positive_partial_solve_wit_1.
Axiom proof_of_array_copy_positive_partial_solve_wit_2 : array_copy_positive_partial_solve_wit_2.
Axiom proof_of_array_copy_positive_partial_solve_wit_3 : array_copy_positive_partial_solve_wit_3.
Axiom proof_of_array_copy_positive_partial_solve_wit_4 : array_copy_positive_partial_solve_wit_4.

End VC_Correct.
