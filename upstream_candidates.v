From mathcomp.boot Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp.boot Require Import div fintype tuple bigop path.

(* Proposed PR A: singleton and partition big operators over sequences. *)
Lemma big_pred1_seq (R : Type) (idx : R) (op : Monoid.law idx)
    (I : eqType) r i (P : pred I) F :
  i \in r -> uniq r -> P =1 pred1 i ->
  \big[op/idx]_(j <- r | P j) F j = F i.
Proof.
by move=> ir ur Pi; rewrite (eq_bigl (pred1 i)) //
  -big_filter filter_pred1_uniq // big_seq1.
Qed.

(* Proposed PR A: singleton and partition big operators over sequences. *)
Lemma partition_big_seq (R : Type) (idx : R) (op : Monoid.com_law idx)
    (I J : eqType) s t (P : pred I) (p : I -> J) F :
  uniq t -> {in s, forall i, P i -> p i \in t} ->
  \big[op/idx]_(i <- s | P i) F i =
    \big[op/idx]_(j <- t) \big[op/idx]_(i <- s | P i && (p i == j)) F i.
Proof.
move=> ut pt.
under [RHS]eq_bigr do rewrite big_mkcond.
rewrite [RHS]exchange_big big_mkcond.
apply: eq_big_seq => i si; case Pi: (P i) => /=.
  rewrite -big_mkcond; apply/esym/(@big_pred1_seq R idx op J t (p i)) => //.
  by apply: pt => //; rewrite Pi.
by rewrite big1.
Qed.

(* Proposed PR B: uniqueness and membership of concatenated sequences. *)
Lemma bigcatE (I T : Type) r (P : pred I) (F : I -> seq T) :
  \big[cat/[::]]_(i <- r | P i) F i =
    flatten [seq F i | i <- r & P i].
Proof. by rewrite -big_filter /flatten foldrE big_map. Qed.

(* Proposed PR B: uniqueness and membership of concatenated sequences. *)
Lemma mem_bigcatP (I T : eqType) r (P : pred I) (F : I -> seq T) x :
  reflect (exists2 i, i \in r & P i /\ x \in F i)
    (x \in \big[cat/[::]]_(i <- r | P i) F i).
Proof.
rewrite bigcatE; apply: (iffP flatten_mapP).
  by case=> i /[!mem_filter]/andP[Pi ir] xi; exists i => //; split.
by case=> i ir [Pi xi]; exists i => //; rewrite mem_filter Pi ir.
Qed.

(* Proposed PR B: uniqueness and membership of concatenated sequences. *)
Lemma bigcat_uniq (I T : eqType) r (P : pred I) (F : I -> seq T) :
  uniq r -> (forall i, P i -> uniq (F i)) ->
  (forall x i j, x \in F i -> x \in F j -> i = j) ->
  uniq (\big[cat/[::]]_(i <- r | P i) F i).
Proof.
move=> ur uF sep; elim: r ur => [|i r IHr]; first by rewrite big_nil.
move=> /= /andP[ni ur].
rewrite big_cons; case Pi: (P i); last exact: IHr ur.
rewrite cat_uniq uF // IHr // andbT; apply/hasPn => x.
move/mem_bigcatP=> [j jr [_ xj]].
apply/negP => xi; have ij := sep x i j xi xj.
by move: ni; rewrite ij jr.
Qed.

(* Proposed PR B: uniqueness and membership of concatenated sequences. *)
Lemma bigcat_nat_uniq (T : eqType) m n (F : nat -> seq T) :
  (forall i, uniq (F i)) ->
  (forall x i j, x \in F i -> x \in F j -> i = j) ->
  uniq (\big[cat/[::]]_(m <= i < n) F i).
Proof.
move=> uF sep; apply: bigcat_uniq => //.
exact: iota_uniq.
Qed.

(* Proposed PR C: sequence bounds for least common multiples. *)
Lemma biglcmn_sup_seq (I : eqType) r i (P : pred I) (F : I -> nat) m :
  i \in r -> P i -> m %| F i -> m %| \big[lcmn/1]_(j <- r | P j) F j.
Proof.
by move=> ir Pi mFi; rewrite (dvdn_trans mFi) // (big_rem i) //= Pi dvdn_lcml.
Qed.

(* Proposed PR D: remainder comparison under equal quotients. *)
Lemma eqdivn_leqmodn m n d :
  m %/ d = n %/ d -> (m %% d <= n %% d) = (m <= n).
Proof.
by move=> eqdiv; rewrite [in RHS](divn_eq m d) [in RHS](divn_eq n d)
  eqdiv leq_add2l.
Qed.

(* Proposed PR F: natural-number sum bounds over sequence support. *)
Lemma leq_sum_seq (I : eqType) r (P : pred I) (F G : I -> nat) :
  {in r, forall i, P i -> F i <= G i} ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Proof.
move=> leFG; rewrite big_seq_cond [leqRHS]big_seq_cond.
by apply: leq_sum => i /andP[ir Pi]; exact: leFG.
Qed.

(* Proposed PR F: natural-number sum bounds over sequence support. *)
Lemma sum_nat_lt_size (I : eqType) r (F : I -> nat) :
  \sum_(i <- r) F i < size r -> has (fun i => F i == 0) r.
Proof.
apply: contraLR => /hasPn Fneq.
rewrite -leqNgt -sum1_size [leqLHS]big_seq [leqRHS]big_seq.
by apply: leq_sum => i ir; rewrite lt0n; exact: Fneq.
Qed.

(* Proposed PR A: singleton and partition big operators over sequences. *)
Lemma leq_sum_partition (I J : eqType) s t (P : pred I)
    (p : I -> J) (F : I -> nat) :
  {in s, forall i, P i -> p i \in t} ->
  \sum_(i <- s | P i) F i <=
    \sum_(j <- t) \sum_(i <- s | P i && (p i == j)) F i.
Proof.
move=> pt; under [leqRHS]eq_bigr do rewrite big_mkcond.
rewrite [leqRHS]exchange_big big_mkcond.
rewrite big_seq [leqRHS]big_seq.
apply: leq_sum => i si; case Pi: (P i) => //=.
rewrite -big_mkcond big_const_seq iter_addn_0.
apply: leq_pmulr; rewrite -has_count; apply/hasP; exists (p i).
  by apply: pt => //; rewrite Pi.
by rewrite eqxx.
Qed.

(* Proposed PR G: big operators over the unit type. *)
Lemma big_unit (R : Type) (idx : R) (op : Monoid.law idx) (F : unit -> R) :
  \big[op/idx]_(i : unit) F i = F tt.
Proof.
rewrite /index_enum unlock_with -enumT /=.
have -> : enum (unit : finType) = [:: tt] by rewrite /(enum _) unlock.
by rewrite big_seq1.
Qed.

(* Proposed PR H: partitioning sorted sequences by an antitone predicate. *)
Lemma sorted_filter_split (T : eqType) (le : rel T) (P : pred T) s :
  transitive le -> (forall x y, le x y -> P y -> P x) ->
  sorted le s -> s = filter P s ++ filter (predC P) s.
Proof.
move=> le_trans anti; elim: s => //= x s IHs.
rewrite path_sortedE // => /andP[xs ss].
case Px: (P x) => /=; first by rewrite -(IHs ss).
have nPs : ~~ has P s.
  apply/hasPn => y ys; apply/negP => Py.
  have : P x by apply: anti Py; exact: (allP xs y ys).
  by rewrite Px.
have -> : filter P s = [::] by move: nPs; rewrite has_filter negbK => /eqP.
rewrite /=; congr (_ :: _); apply/esym/all_filterP.
by rewrite all_predC.
Qed.

(* Proposed PR I: sequence predicates and nonemptiness. *)
Lemma all_has (T : Type) (P : pred T) s :
  all P s -> 0 < size s -> has P s.
Proof. by case: s => //= x s /andP[Px _] _; rewrite Px. Qed.

(* Proposed PR I: sequence predicates and nonemptiness. *)
Lemma nth_default_or_mem (T : eqType) (d : T) (s : seq T) n :
  nth d s n = d \/ nth d s n \in s.
Proof.
case: (ltnP n (size s)) => ns.
  right; exact: mem_nth.
left; exact: nth_default.
Qed.

(* Proposed PR I: sequence predicates and nonemptiness. *)
Lemma filter_last_mem (T : eqType) (s : seq T) (d : T) (P : pred T) :
  has P s -> last d (filter P s) \in s.
Proof.
move=> Ps; apply: (mem_subseq (filter_subseq P s)).
move: Ps; rewrite has_filter; case: (filter P s) => // x t _.
by rewrite last_cons mem_last.
Qed.

(* Proposed PR J: basic lemmas for endpoint-based intervals. *)
Lemma index_iota_cons a b :
  a < b -> index_iota a b = a :: index_iota a.+1 b.
Proof.
case: b => // b; rewrite ltnS => ab.
by rewrite /index_iota subSn //= subnS.
Qed.

(* Proposed PR J: basic lemmas for endpoint-based intervals. *)
Lemma index_iota_cat t m n :
  m <= t <= n -> index_iota m n = index_iota m t ++ index_iota t n.
Proof.
move=> /andP[mt tn].
rewrite /index_iota -[n - m](subnKC (leq_sub2r m tn)) iotaD.
by rewrite -subnDA (subnKC mt).
Qed.

(* Proposed PR I: sequence predicates and nonemptiness. *)
Lemma count_predUI_sub (T : Type) (P Q : pred T) (s : seq T) :
  count (predU P Q) s = count P s + count Q s - count (predI P Q) s.
Proof. by rewrite -(count_predUI P Q s) addnK. Qed.

(* Proposed PR F: natural-number sum bounds over sequence support. *)
Lemma sum_majorant_constant (I : eqType) (r : seq I) (P : pred I)
    (F : I -> nat) c :
  {in r, forall i, P i -> F i <= c} ->
  \sum_(i <- r | P i) F i <= c * size [seq i <- r | P i].
Proof.
move=> bound.
rewrite -sum1_size big_filter big_distrr /= muln1.
exact: leq_sum_seq bound.
Qed.

(* Proposed PR F: natural-number sum bounds over sequence support. *)
Lemma bigmax_leq_sum (I : Type) (r : seq I) (P : pred I) (F : I -> nat) :
  \max_(i <- r | P i) F i <= \sum_(i <- r | P i) F i.
Proof.
apply: (big_ind2 leq) => // m1 n1 m2 n2 le1 le2.
by rewrite geq_max; apply/andP; split;
  [exact: leq_trans le1 (leq_addr _ _)|exact: leq_trans le2 (leq_addl _ _)].
Qed.

(* Proposed PR F: natural-number sum bounds over sequence support. *)
Lemma leq_sum_subseq (I : eqType) (r s : seq I) (P : pred I) (F : I -> nat) :
  subseq r s -> \sum_(i <- r | P i) F i <= \sum_(i <- s | P i) F i.
Proof.
move=> rs; apply: sub_le_big_seq => //= [m n|i].
  exact: leq_addr.
exact: leq_count_subseq rs.
Qed.

(* Proposed PR F: support-local comparisons and equalities of big operators. *)
Lemma eq_big_in (R : Type) (idx : R) (op : Monoid.law idx)
    (I : eqType) (r : seq I) (P : pred I) (F G : I -> R) :
  {in r, forall i, P i -> F i = G i} ->
  \big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(i <- r | P i) G i.
Proof.
move=> FG; rewrite !(big_seq_cond P).
by apply: eq_bigr => i /andP[ir Pi]; exact: FG.
Qed.

(* Proposed PR F: generalize upstream uniq_sub_le_big by dropping uniq s'; sub_le_big_seq and leq_uniq_count prove the generic statement with only left uniqueness, covering Prosa leq_sum_sub_uniq. *)

(* Proposed PR I: sequence predicates and nonemptiness. *)
Lemma leq_count_predI (T : Type) (P Q : pred T) (s : seq T) :
  count P s + count Q s - size s <= count (predI P Q) s.
Proof.
rewrite leq_subLR -(count_predUI P Q s) leq_add2r.
exact: count_size.
Qed.
