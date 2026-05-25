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
Require Import longest_increasing_run.
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

(*----- Function longest_increasing_run -----*)

Definition longest_increasing_run_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition longest_increasing_run_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition longest_increasing_run_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition longest_increasing_run_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition longest_increasing_run_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "best" ) )) # Int  |-> 1)
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition longest_increasing_run_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition longest_increasing_run_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition longest_increasing_run_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| ((Znth (i - 1 ) l 0) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((cur + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cur + 1 )) |]
.

Definition longest_increasing_run_safety_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| ((Znth (i - 1 ) l 0) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition longest_increasing_run_safety_wit_10 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (best < 1) |] 
  &&  [| ((Znth (i - 1 ) l 0) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| False |]
.

Definition longest_increasing_run_safety_wit_11 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (best >= (cur + 1 )) |] 
  &&  [| ((Znth (i - 1 ) l 0) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition longest_increasing_run_safety_wit_12 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (best >= 1) |] 
  &&  [| ((Znth (i - 1 ) l 0) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> 1)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition longest_increasing_run_safety_wit_13 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (best < (cur + 1 )) |] 
  &&  [| ((Znth (i - 1 ) l 0) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "best" ) )) # Int  |-> (cur + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition longest_increasing_run_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((1 - 1 )) (l) (0))) (1) (1) ((sublist (1) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition longest_increasing_run_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (best < (cur + 1 )) |] 
  &&  [| ((Znth (i - 1 ) l 0) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= (cur + 1 )) |] 
  &&  [| ((cur + 1 ) <= (i + 1 )) |] 
  &&  [| (1 <= (cur + 1 )) |] 
  &&  [| ((cur + 1 ) <= (i + 1 )) |] 
  &&  [| ((longest_increasing_run_acc ((Znth (((i + 1 ) - 1 )) (l) (0))) ((cur + 1 )) ((cur + 1 )) ((sublist ((i + 1 )) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition longest_increasing_run_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (best >= 1) |] 
  &&  [| ((Znth (i - 1 ) l 0) >= (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= (i + 1 )) |] 
  &&  [| ((longest_increasing_run_acc ((Znth (((i + 1 ) - 1 )) (l) (0))) (1) (best) ((sublist ((i + 1 )) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition longest_increasing_run_entail_wit_2_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (best >= (cur + 1 )) |] 
  &&  [| ((Znth (i - 1 ) l 0) < (Znth i l 0)) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= (cur + 1 )) |] 
  &&  [| ((cur + 1 ) <= (i + 1 )) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= (i + 1 )) |] 
  &&  [| ((longest_increasing_run_acc ((Znth (((i + 1 ) - 1 )) (l) (0))) ((cur + 1 )) (best) ((sublist ((i + 1 )) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition longest_increasing_run_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 = (longest_increasing_run_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition longest_increasing_run_return_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (best = (longest_increasing_run_spec (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition longest_increasing_run_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (i - 1 ) l 0))
  **  (IntArray.missing_i a_pre (i - 1 ) 0 n_pre l )
.

Definition longest_increasing_run_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (best: Z) (cur: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (1 <= cur) |] 
  &&  [| (cur <= i) |] 
  &&  [| (1 <= best) |] 
  &&  [| (best <= i) |] 
  &&  [| ((longest_increasing_run_acc ((Znth ((i - 1 )) (l) (0))) (cur) (best) ((sublist (i) (n_pre) (l)))) = (longest_increasing_run_spec (l))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_longest_increasing_run_safety_wit_1 : longest_increasing_run_safety_wit_1.
Axiom proof_of_longest_increasing_run_safety_wit_2 : longest_increasing_run_safety_wit_2.
Axiom proof_of_longest_increasing_run_safety_wit_3 : longest_increasing_run_safety_wit_3.
Axiom proof_of_longest_increasing_run_safety_wit_4 : longest_increasing_run_safety_wit_4.
Axiom proof_of_longest_increasing_run_safety_wit_5 : longest_increasing_run_safety_wit_5.
Axiom proof_of_longest_increasing_run_safety_wit_6 : longest_increasing_run_safety_wit_6.
Axiom proof_of_longest_increasing_run_safety_wit_7 : longest_increasing_run_safety_wit_7.
Axiom proof_of_longest_increasing_run_safety_wit_8 : longest_increasing_run_safety_wit_8.
Axiom proof_of_longest_increasing_run_safety_wit_9 : longest_increasing_run_safety_wit_9.
Axiom proof_of_longest_increasing_run_safety_wit_10 : longest_increasing_run_safety_wit_10.
Axiom proof_of_longest_increasing_run_safety_wit_11 : longest_increasing_run_safety_wit_11.
Axiom proof_of_longest_increasing_run_safety_wit_12 : longest_increasing_run_safety_wit_12.
Axiom proof_of_longest_increasing_run_safety_wit_13 : longest_increasing_run_safety_wit_13.
Axiom proof_of_longest_increasing_run_entail_wit_1 : longest_increasing_run_entail_wit_1.
Axiom proof_of_longest_increasing_run_entail_wit_2_1 : longest_increasing_run_entail_wit_2_1.
Axiom proof_of_longest_increasing_run_entail_wit_2_2 : longest_increasing_run_entail_wit_2_2.
Axiom proof_of_longest_increasing_run_entail_wit_2_3 : longest_increasing_run_entail_wit_2_3.
Axiom proof_of_longest_increasing_run_return_wit_1 : longest_increasing_run_return_wit_1.
Axiom proof_of_longest_increasing_run_return_wit_2 : longest_increasing_run_return_wit_2.
Axiom proof_of_longest_increasing_run_partial_solve_wit_1 : longest_increasing_run_partial_solve_wit_1.
Axiom proof_of_longest_increasing_run_partial_solve_wit_2 : longest_increasing_run_partial_solve_wit_2.

End VC_Correct.
