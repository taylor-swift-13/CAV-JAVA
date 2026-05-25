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
Require Import insertion_sort.
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

(*----- Function insertion_sort -----*)

Definition insertion_sort_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "key" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition insertion_sort_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "key" ) )) # Int  |-> (Znth i l_outer 0))
  **  ((( &( "j" ) )) # Int  |->_)
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition insertion_sort_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "key" ) )) # Int  |-> (Znth i l_outer 0))
  **  ((( &( "j" ) )) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition insertion_sort_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l_cur )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insertion_sort_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition insertion_sort_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition insertion_sort_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) ((Znth j l_cur 0)) (l_cur)) )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition insertion_sort_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| (j < 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l_cur )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition insertion_sort_safety_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition insertion_sort_safety_wit_10 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition insertion_sort_safety_wit_11 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| (j < 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l_cur )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition insertion_sort_safety_wit_12 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i_2: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i: Z) ,
  [| (j < 0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i) |] 
  &&  [| (key = (Znth i l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i) (l_base))) ((sublist ((i + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i_2 <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i_2)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) (key) (l_cur)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition insertion_sort_safety_wit_13 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i_2: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i: Z) ,
  [| ((Znth j l_cur 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i) |] 
  &&  [| (key = (Znth i l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i) (l_base))) ((sublist ((i + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i_2 <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i_2)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) (key) (l_cur)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition insertion_sort_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (l_outer: (@list Z)) ,
  [| (1 <= 1) |] 
  &&  [| (1 <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (1 <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < 1)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
.

Definition insertion_sort_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
|--
  EX (l_cur: (@list Z))  (l_base: (@list Z)) ,
  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((-1) <= (i - 1 )) |] 
  &&  [| ((i - 1 ) < i) |] 
  &&  [| ((Znth i l_outer 0) = (Znth i l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , ((((i - 1 ) < k_3) /\ (k_3 < i)) -> ((Znth i l_outer 0) < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) (((i - 1 ) + 2 )) (l_base))) ((app ((sublist (((i - 1 ) + 1 )) (i) (l_base))) ((sublist ((i + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
.

Definition insertion_sort_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur_2: (@list Z)) (l_base_2: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur_2 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base_2 0)) |] 
  &&  [| ((Zlength (l_base_2)) = n_pre) |] 
  &&  [| (Permutation l l_base_2 ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base_2 0) <= (Znth (k_2 + 1 ) l_base_2 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base_2 0))) |] 
  &&  [| (l_cur_2 = (app ((sublist (0) ((j + 2 )) (l_base_2))) ((app ((sublist ((j + 1 )) (i_2) (l_base_2))) ((sublist ((i_2 + 1 )) (n_pre) (l_base_2))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) ((Znth j l_cur_2 0)) (l_cur_2)) )
|--
  EX (l_cur: (@list Z))  (l_base: (@list Z)) ,
  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= (j - 1 )) |] 
  &&  [| ((j - 1 ) < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , ((((j - 1 ) < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) (((j - 1 ) + 2 )) (l_base))) ((app ((sublist (((j - 1 ) + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
.

Definition insertion_sort_entail_wit_4_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer_2: (@list Z)) (i_2: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i: Z) ,
  [| ((Znth j l_cur 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i) |] 
  &&  [| (key = (Znth i l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i) (l_base))) ((sublist ((i + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i_2 <= n_pre)) |] 
  &&  [| ((Zlength (l_outer_2)) = n_pre) |] 
  &&  [| (Permutation l l_outer_2 ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i_2)) -> ((Znth k l_outer_2 0) <= (Znth (k + 1 ) l_outer_2 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) (key) (l_cur)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
|--
  EX (l_outer: (@list Z)) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> ((i + 1 ) <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < (i + 1 ))) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
  **  ((( &( "key" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
.

Definition insertion_sort_entail_wit_4_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer_2: (@list Z)) (i_2: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i: Z) ,
  [| (j < 0) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i) |] 
  &&  [| (key = (Znth i l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i) (l_base))) ((sublist ((i + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i_2 <= n_pre)) |] 
  &&  [| ((Zlength (l_outer_2)) = n_pre) |] 
  &&  [| (Permutation l l_outer_2 ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i_2)) -> ((Znth k l_outer_2 0) <= (Znth (k + 1 ) l_outer_2 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre (replace_Znth ((j + 1 )) (key) (l_cur)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "key" ) )) # Int  |-> key)
|--
  EX (l_outer: (@list Z)) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> ((i + 1 ) <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < (i + 1 ))) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
  **  ((( &( "key" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
.

Definition insertion_sort_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| (insertion_sort_spec l lr ) |]
  &&  (IntArray.full a_pre n_pre lr )
.

Definition insertion_sort_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_outer )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l_outer 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l_outer )
.

Definition insertion_sort_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
|--
  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l_cur 0))
  **  (IntArray.missing_i a_pre j 0 n_pre l_cur )
.

Definition insertion_sort_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
|--
  [| ((Znth j l_cur 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l_cur 0))
  **  (IntArray.missing_i a_pre j 0 n_pre l_cur )
.

Definition insertion_sort_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
|--
  [| ((Znth j l_cur 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre (j + 1 ) 0 n_pre l_cur )
.

Definition insertion_sort_partial_solve_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| ((Znth j l_cur 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
|--
  [| ((Znth j l_cur 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre (j + 1 ) 0 n_pre l_cur )
.

Definition insertion_sort_partial_solve_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l_outer: (@list Z)) (i: Z) (l_cur: (@list Z)) (l_base: (@list Z)) (key: Z) (j: Z) (i_2: Z) ,
  [| (j < 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre l_cur )
|--
  [| (j < 0) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| ((-1) <= j) |] 
  &&  [| (j < i_2) |] 
  &&  [| (key = (Znth i_2 l_base 0)) |] 
  &&  [| ((Zlength (l_base)) = n_pre) |] 
  &&  [| (Permutation l l_base ) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ ((k_2 + 1 ) < i_2)) -> ((Znth k_2 l_base 0) <= (Znth (k_2 + 1 ) l_base 0))) |] 
  &&  [| forall (k_3: Z) , (((j < k_3) /\ (k_3 < i_2)) -> (key < (Znth k_3 l_base 0))) |] 
  &&  [| (l_cur = (app ((sublist (0) ((j + 2 )) (l_base))) ((app ((sublist ((j + 1 )) (i_2) (l_base))) ((sublist ((i_2 + 1 )) (n_pre) (l_base))))))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| ((n_pre > 0) -> (i <= n_pre)) |] 
  &&  [| ((Zlength (l_outer)) = n_pre) |] 
  &&  [| (Permutation l l_outer ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ ((k + 1 ) < i)) -> ((Znth k l_outer 0) <= (Znth (k + 1 ) l_outer 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  (((a_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre (j + 1 ) 0 n_pre l_cur )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_insertion_sort_safety_wit_1 : insertion_sort_safety_wit_1.
Axiom proof_of_insertion_sort_safety_wit_2 : insertion_sort_safety_wit_2.
Axiom proof_of_insertion_sort_safety_wit_3 : insertion_sort_safety_wit_3.
Axiom proof_of_insertion_sort_safety_wit_4 : insertion_sort_safety_wit_4.
Axiom proof_of_insertion_sort_safety_wit_5 : insertion_sort_safety_wit_5.
Axiom proof_of_insertion_sort_safety_wit_6 : insertion_sort_safety_wit_6.
Axiom proof_of_insertion_sort_safety_wit_7 : insertion_sort_safety_wit_7.
Axiom proof_of_insertion_sort_safety_wit_8 : insertion_sort_safety_wit_8.
Axiom proof_of_insertion_sort_safety_wit_9 : insertion_sort_safety_wit_9.
Axiom proof_of_insertion_sort_safety_wit_10 : insertion_sort_safety_wit_10.
Axiom proof_of_insertion_sort_safety_wit_11 : insertion_sort_safety_wit_11.
Axiom proof_of_insertion_sort_safety_wit_12 : insertion_sort_safety_wit_12.
Axiom proof_of_insertion_sort_safety_wit_13 : insertion_sort_safety_wit_13.
Axiom proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Axiom proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Axiom proof_of_insertion_sort_entail_wit_3 : insertion_sort_entail_wit_3.
Axiom proof_of_insertion_sort_entail_wit_4_1 : insertion_sort_entail_wit_4_1.
Axiom proof_of_insertion_sort_entail_wit_4_2 : insertion_sort_entail_wit_4_2.
Axiom proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_1 : insertion_sort_partial_solve_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_2 : insertion_sort_partial_solve_wit_2.
Axiom proof_of_insertion_sort_partial_solve_wit_3 : insertion_sort_partial_solve_wit_3.
Axiom proof_of_insertion_sort_partial_solve_wit_4 : insertion_sort_partial_solve_wit_4.
Axiom proof_of_insertion_sort_partial_solve_wit_5 : insertion_sort_partial_solve_wit_5.
Axiom proof_of_insertion_sort_partial_solve_wit_6 : insertion_sort_partial_solve_wit_6.

End VC_Correct.
