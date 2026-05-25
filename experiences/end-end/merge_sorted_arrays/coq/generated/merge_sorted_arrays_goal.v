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
Require Import merge_sorted_arrays.
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

(*----- Function merge_sorted_arrays -----*)

Definition merge_sorted_arrays_safety_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sorted_arrays_safety_wit_2 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sorted_arrays_safety_wit_3 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sorted_arrays_safety_wit_4 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i: Z) ,
  [| ((Znth i la 0) <= (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((0 <= i_2) /\ (i_2 <= j)) /\ (j < n_pre)) -> ((Znth i_2 la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_3: Z) , forall (j_2: Z) , ((((0 <= i_3) /\ (i_3 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_3 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth i la 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j_3)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition merge_sorted_arrays_safety_wit_5 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) > (Znth j lb 0)) |] 
  &&  [| (j < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i_3 + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j_2: Z) , ((((0 <= i) /\ (i <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i la 0) <= (Znth j_2 la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_3: Z) , ((((0 <= i_2) /\ (i_2 <= j_3)) /\ (j_3 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_3 lb 0))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth j lb 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i_3)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition merge_sorted_arrays_safety_wit_6 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) > (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth j_3 lb 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i_3)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> (j_3 + 1 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition merge_sorted_arrays_safety_wit_7 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) <= (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth i_3 la 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  ((( &( "i" ) )) # Int  |-> (i_3 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j_3)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition merge_sorted_arrays_safety_wit_8 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (i = n_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| False |]
.

Definition merge_sorted_arrays_safety_wit_9 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth i la 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full b_pre m_pre lb )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition merge_sorted_arrays_safety_wit_10 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth i la 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full b_pre m_pre lb )
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition merge_sorted_arrays_safety_wit_11 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (j < m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth j lb 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full b_pre m_pre lb )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre la )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition merge_sorted_arrays_safety_wit_12 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (j < m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth j lb 0)) ((app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full b_pre m_pre lb )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre la )
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition merge_sorted_arrays_entail_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) lo )
|--
  EX (lout_done: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| (0 = (0 + 0 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < 0)) /\ (0 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < 0)) /\ (0 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = 0) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (0) (la))) ((sublist (0) (0) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (0) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_entail_wit_2_1 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) <= (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth i_3 la 0)) ((app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  EX (lout_done: (@list Z)) ,
  [| (0 <= (i_3 + 1 )) |] 
  &&  [| ((i_3 + 1 ) <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| ((k + 1 ) = ((i_3 + 1 ) + j_3 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ ((i_3 + 1 ) <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < (i_3 + 1 ))) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = (k + 1 )) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) ((i_3 + 1 )) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist ((k + 1 )) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_entail_wit_2_2 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) > (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth j_3 lb 0)) ((app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (lout_done: (@list Z)) ,
  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= (j_3 + 1 )) |] 
  &&  [| ((j_3 + 1 ) <= m_pre) |] 
  &&  [| ((k + 1 ) = (i_3 + (j_3 + 1 ) )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < (j_3 + 1 ))) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ ((j_3 + 1 ) <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = (k + 1 )) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) ((j_3 + 1 )) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist ((k + 1 )) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_entail_wit_3_1 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (j >= m_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai_3: Z) , forall (aj_2: Z) , ((((0 <= ai_3) /\ (ai_3 <= aj_2)) /\ (aj_2 < n_pre)) -> ((Znth (ai_3) (la) (0)) <= (Znth (aj_2) (la) (0)))) |] 
  &&  [| forall (bi_3: Z) , forall (bj_2: Z) , ((((0 <= bi_3) /\ (bi_3 <= bj_2)) /\ (bj_2 < m_pre)) -> ((Znth (bi_3) (lb) (0)) <= (Znth (bj_2) (lb) (0)))) |] 
  &&  [| forall (bp_2: Z) , forall (ai_4: Z) , (((((0 <= bp_2) /\ (bp_2 < j)) /\ (i <= ai_4)) /\ (ai_4 < n_pre)) -> ((Znth (bp_2) (lb) (0)) < (Znth (ai_4) (la) (0)))) |] 
  &&  [| forall (ap_2: Z) , forall (bi_4: Z) , (((((0 <= ap_2) /\ (ap_2 < i)) /\ (j <= bi_4)) /\ (bi_4 < m_pre)) -> ((Znth (ap_2) (la) (0)) <= (Znth (bi_4) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 la 0) <= (Znth j_2 la 0))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < m_pre)) -> ((Znth i_3 lb 0) <= (Znth j_3 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  (EX (lout_done: (@list Z)) ,
  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (i = n_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) ))
  ||
  (EX (lout_done: (@list Z)) ,
  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) ))
.

Definition merge_sorted_arrays_entail_wit_3_2 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai_3: Z) , forall (aj_2: Z) , ((((0 <= ai_3) /\ (ai_3 <= aj_2)) /\ (aj_2 < n_pre)) -> ((Znth (ai_3) (la) (0)) <= (Znth (aj_2) (la) (0)))) |] 
  &&  [| forall (bi_3: Z) , forall (bj_2: Z) , ((((0 <= bi_3) /\ (bi_3 <= bj_2)) /\ (bj_2 < m_pre)) -> ((Znth (bi_3) (lb) (0)) <= (Znth (bj_2) (lb) (0)))) |] 
  &&  [| forall (bp_2: Z) , forall (ai_4: Z) , (((((0 <= bp_2) /\ (bp_2 < j)) /\ (i <= ai_4)) /\ (ai_4 < n_pre)) -> ((Znth (bp_2) (lb) (0)) < (Znth (ai_4) (la) (0)))) |] 
  &&  [| forall (ap_2: Z) , forall (bi_4: Z) , (((((0 <= ap_2) /\ (ap_2 < i)) /\ (j <= bi_4)) /\ (bi_4 < m_pre)) -> ((Znth (ap_2) (la) (0)) <= (Znth (bi_4) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < n_pre)) -> ((Znth i_2 la 0) <= (Znth j_2 la 0))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < m_pre)) -> ((Znth i_3 lb 0) <= (Znth j_3 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  (EX (lout_done: (@list Z)) ,
  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (i = n_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) ))
  ||
  (EX (lout_done: (@list Z)) ,
  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) ))
.

Definition merge_sorted_arrays_entail_wit_4 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth i la 0)) ((app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
|--
  (EX (lout_done: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| ((k + 1 ) = ((i + 1 ) + j )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= (n_pre + m_pre )) |] 
  &&  [| ((i + 1 ) = n_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ ((i + 1 ) <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < (i + 1 ))) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = (k + 1 )) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) ((i + 1 )) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist ((k + 1 )) ((n_pre + m_pre )) (lo)))) ))
  ||
  (EX (lout_done: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| ((k + 1 ) = ((i + 1 ) + j )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ ((i + 1 ) <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < (i + 1 ))) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = (k + 1 )) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) ((i + 1 )) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist ((k + 1 )) ((n_pre + m_pre )) (lo)))) ))
.

Definition merge_sorted_arrays_entail_wit_5_1 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai_3: Z) , forall (aj_2: Z) , ((((0 <= ai_3) /\ (ai_3 <= aj_2)) /\ (aj_2 < n_pre)) -> ((Znth (ai_3) (la) (0)) <= (Znth (aj_2) (la) (0)))) |] 
  &&  [| forall (bi_3: Z) , forall (bj_2: Z) , ((((0 <= bi_3) /\ (bi_3 <= bj_2)) /\ (bj_2 < m_pre)) -> ((Znth (bi_3) (lb) (0)) <= (Znth (bj_2) (lb) (0)))) |] 
  &&  [| forall (bp_2: Z) , forall (ai_4: Z) , (((((0 <= bp_2) /\ (bp_2 < j)) /\ (i <= ai_4)) /\ (ai_4 < n_pre)) -> ((Znth (bp_2) (lb) (0)) < (Znth (ai_4) (la) (0)))) |] 
  &&  [| forall (ap_2: Z) , forall (bi_4: Z) , (((((0 <= ap_2) /\ (ap_2 < i)) /\ (j <= bi_4)) /\ (bi_4 < m_pre)) -> ((Znth (ap_2) (la) (0)) <= (Znth (bi_4) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  EX (lout_done: (@list Z)) ,
  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_entail_wit_5_2 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (i = n_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai_3: Z) , forall (aj_2: Z) , ((((0 <= ai_3) /\ (ai_3 <= aj_2)) /\ (aj_2 < n_pre)) -> ((Znth (ai_3) (la) (0)) <= (Znth (aj_2) (la) (0)))) |] 
  &&  [| forall (bi_3: Z) , forall (bj_2: Z) , ((((0 <= bi_3) /\ (bi_3 <= bj_2)) /\ (bj_2 < m_pre)) -> ((Znth (bi_3) (lb) (0)) <= (Znth (bj_2) (lb) (0)))) |] 
  &&  [| forall (bp_2: Z) , forall (ai_4: Z) , (((((0 <= bp_2) /\ (bp_2 < j)) /\ (i <= ai_4)) /\ (ai_4 < n_pre)) -> ((Znth (bp_2) (lb) (0)) < (Znth (ai_4) (la) (0)))) |] 
  &&  [| forall (ap_2: Z) , forall (bi_4: Z) , (((((0 <= ap_2) /\ (ap_2 < i)) /\ (j <= bi_4)) /\ (bi_4 < m_pre)) -> ((Znth (ap_2) (la) (0)) <= (Znth (bi_4) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  EX (lout_done: (@list Z)) ,
  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_entail_wit_6 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done_2: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (j < m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done_2)) = k) |] 
  &&  [| (lout_done_2 = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full out_pre (n_pre + m_pre ) (replace_Znth (k) ((Znth j lb 0)) ((app (lout_done_2) ((sublist (k) ((n_pre + m_pre )) (lo)))))) )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (lout_done: (@list Z)) ,
  [| (i = n_pre) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m_pre) |] 
  &&  [| ((k + 1 ) = (n_pre + (j + 1 ) )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < (j + 1 ))) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ ((j + 1 ) <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = (k + 1 )) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) ((j + 1 )) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist ((k + 1 )) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_return_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (j >= m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| ((Zlength ((merge_sorted_arrays_spec (la) (lb)))) = (n_pre + m_pre )) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (merge_sorted_arrays_spec (la) (lb)) )
.

Definition merge_sorted_arrays_partial_solve_wit_1 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((a_pre + (i_3 * sizeof(INT) ) )) # Int  |-> (Znth i_3 la 0))
  **  (IntArray.missing_i a_pre i_3 0 n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_partial_solve_wit_2 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((b_pre + (j_3 * sizeof(INT) ) )) # Int  |-> (Znth j_3 lb 0))
  **  (IntArray.missing_i b_pre j_3 0 m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_partial_solve_wit_3 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) <= (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| ((Znth i_3 la 0) <= (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((a_pre + (i_3 * sizeof(INT) ) )) # Int  |-> (Znth i_3 la 0))
  **  (IntArray.missing_i a_pre i_3 0 n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_partial_solve_wit_4 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) <= (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| ((Znth i_3 la 0) <= (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((out_pre + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre k 0 (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition merge_sorted_arrays_partial_solve_wit_5 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) > (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| ((Znth i_3 la 0) > (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((b_pre + (j_3 * sizeof(INT) ) )) # Int  |-> (Znth j_3 lb 0))
  **  (IntArray.missing_i b_pre j_3 0 m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_partial_solve_wit_6 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j_3: Z) (i_3: Z) ,
  [| ((Znth i_3 la 0) > (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| ((Znth i_3 la 0) > (Znth j_3 lb 0)) |] 
  &&  [| (j_3 < m_pre) |] 
  &&  [| (i_3 < n_pre) |] 
  &&  [| (0 <= i_3) |] 
  &&  [| (i_3 <= n_pre) |] 
  &&  [| (0 <= j_3) |] 
  &&  [| (j_3 <= m_pre) |] 
  &&  [| (k = (i_3 + j_3 )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j_3)) /\ (i_3 <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i_3)) /\ (j_3 <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i_3) (la))) ((sublist (0) (j_3) (lb))))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i la 0) <= (Znth j la 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 <= j_2)) /\ (j_2 < m_pre)) -> ((Znth i_2 lb 0) <= (Znth j_2 lb 0))) |]
  &&  (((out_pre + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre k 0 (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
.

Definition merge_sorted_arrays_partial_solve_wit_7 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_partial_solve_wit_8 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (i + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| (j = m_pre) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (((out_pre + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre k 0 (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
.

Definition merge_sorted_arrays_partial_solve_wit_9 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (j < m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| (j < m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (((b_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j lb 0))
  **  (IntArray.missing_i b_pre j 0 m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
.

Definition merge_sorted_arrays_partial_solve_wit_10 := 
forall (out_pre: Z) (b_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (lb: (@list Z)) (la: (@list Z)) (lout_done: (@list Z)) (k: Z) (j: Z) (i: Z) ,
  [| (j < m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
|--
  [| (j < m_pre) |] 
  &&  [| (i = n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m_pre) |] 
  &&  [| (k = (n_pre + j )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (n_pre + m_pre )) |] 
  &&  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lb)) = m_pre) |] 
  &&  [| ((Zlength (lo)) = (n_pre + m_pre )) |] 
  &&  [| forall (ai: Z) , forall (aj: Z) , ((((0 <= ai) /\ (ai <= aj)) /\ (aj < n_pre)) -> ((Znth (ai) (la) (0)) <= (Znth (aj) (la) (0)))) |] 
  &&  [| forall (bi: Z) , forall (bj: Z) , ((((0 <= bi) /\ (bi <= bj)) /\ (bj < m_pre)) -> ((Znth (bi) (lb) (0)) <= (Znth (bj) (lb) (0)))) |] 
  &&  [| forall (bp: Z) , forall (ai_2: Z) , (((((0 <= bp) /\ (bp < j)) /\ (i <= ai_2)) /\ (ai_2 < n_pre)) -> ((Znth (bp) (lb) (0)) < (Znth (ai_2) (la) (0)))) |] 
  &&  [| forall (ap: Z) , forall (bi_2: Z) , (((((0 <= ap) /\ (ap < i)) /\ (j <= bi_2)) /\ (bi_2 < m_pre)) -> ((Znth (ap) (la) (0)) <= (Znth (bi_2) (lb) (0)))) |] 
  &&  [| ((Zlength (lout_done)) = k) |] 
  &&  [| (lout_done = (merge_sorted_arrays_spec ((sublist (0) (i) (la))) ((sublist (0) (j) (lb))))) |]
  &&  (((out_pre + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre k 0 (n_pre + m_pre ) (app (lout_done) ((sublist (k) ((n_pre + m_pre )) (lo)))) )
  **  (IntArray.full b_pre m_pre lb )
  **  (IntArray.full a_pre n_pre la )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_merge_sorted_arrays_safety_wit_1 : merge_sorted_arrays_safety_wit_1.
Axiom proof_of_merge_sorted_arrays_safety_wit_2 : merge_sorted_arrays_safety_wit_2.
Axiom proof_of_merge_sorted_arrays_safety_wit_3 : merge_sorted_arrays_safety_wit_3.
Axiom proof_of_merge_sorted_arrays_safety_wit_4 : merge_sorted_arrays_safety_wit_4.
Axiom proof_of_merge_sorted_arrays_safety_wit_5 : merge_sorted_arrays_safety_wit_5.
Axiom proof_of_merge_sorted_arrays_safety_wit_6 : merge_sorted_arrays_safety_wit_6.
Axiom proof_of_merge_sorted_arrays_safety_wit_7 : merge_sorted_arrays_safety_wit_7.
Axiom proof_of_merge_sorted_arrays_safety_wit_8 : merge_sorted_arrays_safety_wit_8.
Axiom proof_of_merge_sorted_arrays_safety_wit_9 : merge_sorted_arrays_safety_wit_9.
Axiom proof_of_merge_sorted_arrays_safety_wit_10 : merge_sorted_arrays_safety_wit_10.
Axiom proof_of_merge_sorted_arrays_safety_wit_11 : merge_sorted_arrays_safety_wit_11.
Axiom proof_of_merge_sorted_arrays_safety_wit_12 : merge_sorted_arrays_safety_wit_12.
Axiom proof_of_merge_sorted_arrays_entail_wit_1 : merge_sorted_arrays_entail_wit_1.
Axiom proof_of_merge_sorted_arrays_entail_wit_2_1 : merge_sorted_arrays_entail_wit_2_1.
Axiom proof_of_merge_sorted_arrays_entail_wit_2_2 : merge_sorted_arrays_entail_wit_2_2.
Axiom proof_of_merge_sorted_arrays_entail_wit_3_1 : merge_sorted_arrays_entail_wit_3_1.
Axiom proof_of_merge_sorted_arrays_entail_wit_3_2 : merge_sorted_arrays_entail_wit_3_2.
Axiom proof_of_merge_sorted_arrays_entail_wit_4 : merge_sorted_arrays_entail_wit_4.
Axiom proof_of_merge_sorted_arrays_entail_wit_5_1 : merge_sorted_arrays_entail_wit_5_1.
Axiom proof_of_merge_sorted_arrays_entail_wit_5_2 : merge_sorted_arrays_entail_wit_5_2.
Axiom proof_of_merge_sorted_arrays_entail_wit_6 : merge_sorted_arrays_entail_wit_6.
Axiom proof_of_merge_sorted_arrays_return_wit_1 : merge_sorted_arrays_return_wit_1.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_1 : merge_sorted_arrays_partial_solve_wit_1.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_2 : merge_sorted_arrays_partial_solve_wit_2.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_3 : merge_sorted_arrays_partial_solve_wit_3.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_4 : merge_sorted_arrays_partial_solve_wit_4.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_5 : merge_sorted_arrays_partial_solve_wit_5.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_6 : merge_sorted_arrays_partial_solve_wit_6.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_7 : merge_sorted_arrays_partial_solve_wit_7.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_8 : merge_sorted_arrays_partial_solve_wit_8.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_9 : merge_sorted_arrays_partial_solve_wit_9.
Axiom proof_of_merge_sorted_arrays_partial_solve_wit_10 : merge_sorted_arrays_partial_solve_wit_10.

End VC_Correct.
