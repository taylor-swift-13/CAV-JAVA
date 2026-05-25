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
Require Import max_subarray_sum.
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

(*----- Function max_subarray_sum -----*)

Definition max_subarray_sum_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition max_subarray_sum_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  ((( &( "best" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition max_subarray_sum_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "best" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition max_subarray_sum_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((cur + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cur + (Znth i l 0) )) |]
.

Definition max_subarray_sum_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| ((cur + (Znth i l 0) ) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((cur + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cur + (Znth i l 0) )) |]
.

Definition max_subarray_sum_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (best >= (Znth i l 0)) |] 
  &&  [| ((cur + (Znth i l 0) ) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition max_subarray_sum_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (best >= (cur + (Znth i l 0) )) |] 
  &&  [| ((cur + (Znth i l 0) ) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> (cur + (Znth i l 0) ))
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition max_subarray_sum_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (best < (cur + (Znth i l 0) )) |] 
  &&  [| ((cur + (Znth i l 0) ) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> (cur + (Znth i l 0) ))
  **  ((( &( "best" ) )) # Int  |-> (cur + (Znth i l 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition max_subarray_sum_safety_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (best < (Znth i l 0)) |] 
  &&  [| ((cur + (Znth i l 0) ) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "best" ) )) # Int  |-> (Znth i l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition max_subarray_sum_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lo_2: Z) ,
  [| (1 <= 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < 1) |] 
  &&  [| ((Znth 0 l 0) = (sum ((sublist (lo_2) (1) (l))))) |] 
  &&  [| (INT_MIN <= (Znth 0 l 0)) |] 
  &&  [| ((Znth 0 l 0) <= INT_MAX) |] 
  &&  [| (INT_MIN <= (Znth 0 l 0)) |] 
  &&  [| ((Znth 0 l 0) <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc ((Znth 0 l 0)) ((Znth 0 l 0)) ((sublist (1) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition max_subarray_sum_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_3: Z) (i: Z) ,
  [| (best < (Znth i l 0)) |] 
  &&  [| ((cur + (Znth i l 0) ) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_3) |] 
  &&  [| (lo_3 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_3) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lo_2: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < (i + 1 )) |] 
  &&  [| ((Znth i l 0) = (sum ((sublist (lo_2) ((i + 1 )) (l))))) |] 
  &&  [| (INT_MIN <= (Znth i l 0)) |] 
  &&  [| ((Znth i l 0) <= INT_MAX) |] 
  &&  [| (INT_MIN <= (Znth i l 0)) |] 
  &&  [| ((Znth i l 0) <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc ((Znth i l 0)) ((Znth i l 0)) ((sublist ((i + 1 )) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition max_subarray_sum_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_3: Z) (i: Z) ,
  [| (best < (cur + (Znth i l 0) )) |] 
  &&  [| ((cur + (Znth i l 0) ) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_3) |] 
  &&  [| (lo_3 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_3) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lo_2: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < (i + 1 )) |] 
  &&  [| ((cur + (Znth i l 0) ) = (sum ((sublist (lo_2) ((i + 1 )) (l))))) |] 
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |] 
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |] 
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc ((cur + (Znth i l 0) )) ((cur + (Znth i l 0) )) ((sublist ((i + 1 )) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition max_subarray_sum_entail_wit_2_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_3: Z) (i: Z) ,
  [| (best >= (cur + (Znth i l 0) )) |] 
  &&  [| ((cur + (Znth i l 0) ) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_3) |] 
  &&  [| (lo_3 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_3) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lo_2: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < (i + 1 )) |] 
  &&  [| ((cur + (Znth i l 0) ) = (sum ((sublist (lo_2) ((i + 1 )) (l))))) |] 
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |] 
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc ((cur + (Znth i l 0) )) (best) ((sublist ((i + 1 )) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition max_subarray_sum_entail_wit_2_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_3: Z) (i: Z) ,
  [| (best >= (Znth i l 0)) |] 
  &&  [| ((cur + (Znth i l 0) ) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_3) |] 
  &&  [| (lo_3 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_3) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lo_2: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < (i + 1 )) |] 
  &&  [| ((Znth i l 0) = (sum ((sublist (lo_2) ((i + 1 )) (l))))) |] 
  &&  [| (INT_MIN <= (Znth i l 0)) |] 
  &&  [| ((Znth i l 0) <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc ((Znth i l 0)) (best) ((sublist ((i + 1 )) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition max_subarray_sum_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (best = (max_subarray_sum_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition max_subarray_sum_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition max_subarray_sum_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition max_subarray_sum_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition max_subarray_sum_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition max_subarray_sum_partial_solve_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| ((cur + (Znth i l 0) ) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((cur + (Znth i l 0) ) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition max_subarray_sum_partial_solve_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (lo_2: Z) (i: Z) ,
  [| ((cur + (Znth i l 0) ) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((cur + (Znth i l 0) ) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= lo_2) |] 
  &&  [| (lo_2 < i) |] 
  &&  [| (cur = (sum ((sublist (lo_2) (i) (l))))) |] 
  &&  [| (INT_MIN <= cur) |] 
  &&  [| (cur <= INT_MAX) |] 
  &&  [| (INT_MIN <= best) |] 
  &&  [| (best <= INT_MAX) |] 
  &&  [| ((max_subarray_sum_acc (cur) (best) ((sublist (i) (n_pre) (l)))) = (max_subarray_sum_spec (l))) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (lo: Z) , forall (hi: Z) , ((((0 <= lo) /\ (lo < hi)) /\ (hi <= n_pre)) -> ((INT_MIN <= (sum ((sublist (lo) (hi) (l))))) /\ ((sum ((sublist (lo) (hi) (l)))) <= INT_MAX))) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_max_subarray_sum_safety_wit_1 : max_subarray_sum_safety_wit_1.
Axiom proof_of_max_subarray_sum_safety_wit_2 : max_subarray_sum_safety_wit_2.
Axiom proof_of_max_subarray_sum_safety_wit_3 : max_subarray_sum_safety_wit_3.
Axiom proof_of_max_subarray_sum_safety_wit_4 : max_subarray_sum_safety_wit_4.
Axiom proof_of_max_subarray_sum_safety_wit_5 : max_subarray_sum_safety_wit_5.
Axiom proof_of_max_subarray_sum_safety_wit_6 : max_subarray_sum_safety_wit_6.
Axiom proof_of_max_subarray_sum_safety_wit_7 : max_subarray_sum_safety_wit_7.
Axiom proof_of_max_subarray_sum_safety_wit_8 : max_subarray_sum_safety_wit_8.
Axiom proof_of_max_subarray_sum_safety_wit_9 : max_subarray_sum_safety_wit_9.
Axiom proof_of_max_subarray_sum_entail_wit_1 : max_subarray_sum_entail_wit_1.
Axiom proof_of_max_subarray_sum_entail_wit_2_1 : max_subarray_sum_entail_wit_2_1.
Axiom proof_of_max_subarray_sum_entail_wit_2_2 : max_subarray_sum_entail_wit_2_2.
Axiom proof_of_max_subarray_sum_entail_wit_2_3 : max_subarray_sum_entail_wit_2_3.
Axiom proof_of_max_subarray_sum_entail_wit_2_4 : max_subarray_sum_entail_wit_2_4.
Axiom proof_of_max_subarray_sum_return_wit_1 : max_subarray_sum_return_wit_1.
Axiom proof_of_max_subarray_sum_partial_solve_wit_1 : max_subarray_sum_partial_solve_wit_1.
Axiom proof_of_max_subarray_sum_partial_solve_wit_2 : max_subarray_sum_partial_solve_wit_2.
Axiom proof_of_max_subarray_sum_partial_solve_wit_3 : max_subarray_sum_partial_solve_wit_3.
Axiom proof_of_max_subarray_sum_partial_solve_wit_4 : max_subarray_sum_partial_solve_wit_4.
Axiom proof_of_max_subarray_sum_partial_solve_wit_5 : max_subarray_sum_partial_solve_wit_5.
Axiom proof_of_max_subarray_sum_partial_solve_wit_6 : max_subarray_sum_partial_solve_wit_6.

End VC_Correct.
