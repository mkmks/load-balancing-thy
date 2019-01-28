theory LoadBalancing imports Complex_Main Groups_List "HOL-Library.Multiset"
begin

section \<open>The algorithm\<close>

text \<open>This job scheduling function takes a list of job execution times and uses it
      to mutate the schedule. The proofs about optimal upper bounds will assume that the function
      is called with an empty schedule, i.e., 'replicate m {#}',
      where 'm' stands for the number of machines available.

      The first element of the job list is scheduled last.\<close>

definition add_job :: "nat \<Rightarrow> (nat multiset) list \<Rightarrow> (nat multiset) list" where
  "add_job n ms \<equiv>  add_mset n (hd ms)#(tl ms)"

fun balance :: "nat list \<Rightarrow> (nat multiset) list \<Rightarrow> (nat multiset) list" where
"balance []     = id" |
"balance (t#ts) = add_job t \<circ> sort_key sum_mset \<circ> balance ts"

text \<open>Test cases\<close>
(* Figure 11.1 in KT*)
value \<open>balance (rev [2,3,4,6,2,2]) (replicate 3 {#})\<close>

section \<open>Some useful properties\<close>

subsection \<open>Valid schedules\<close>

text \<open>For each machine, we keep a set of assigned jobs represented as their execution times.
      The algorithm assumes that the jobs are always placed on the machine with the smallest load.
      We implement this assumption by sorting the list of machines by their load before placing jobs.
      The head of the sorted list will therefore have the smallest load.\<close>

definition schedule :: "nat list \<Rightarrow> (nat multiset) list \<Rightarrow> bool" where
  "schedule ts ms \<equiv> \<Union># (mset ms) = mset ts"

theorem loads_eq_times:
  fixes ms::"(nat multiset) list"
  assumes
    msch: "schedule ts ms"
  shows "sum_list (map sum_mset ms) = sum_list ts"
proof -
  have "sum_list (map sum_mset ms) = sum_mset (\<Union># (mset ms))" by (induction ms) simp_all
  also have "\<dots> = sum_mset (mset ts)" using msch schedule_def by simp
  also have "\<dots> = sum_list ts" by (simp add: sum_mset_sum_list)
  finally show ?thesis .
qed

lemma balance_length:
  assumes "length ms > 0"
  shows "length ms = length (balance ts ms)"
(* Suc_pred fails to apply in this:
  using assms add_job_def by (induction ts) simp_all *)
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then show ?case using assms add_job_def by simp
qed

lemma mset_add_job:
  assumes "length ms > 0"
  shows "\<Union># (mset (add_job n ms)) = add_mset n (\<Union># (mset ms))"
  using assms add_job_def by (induction ms) simp_all

theorem schedule_balance:
  assumes "m > 0"
  shows "schedule ts (balance ts (replicate m {#}))"
proof (induction ts)
  case Nil
  then show ?case using schedule_def by simp
next
  case (Cons a ts)
  have "length (balance ts (replicate m {#})) > 0" using assms balance_length by simp
  thus ?case using schedule_def mset_add_job
    by (metis (no_types, lifting) balance.simps(2) length_sort Cons mset.simps(2) mset_sort o_def)
qed

subsection \<open>The last job contributing to the makespan\<close>

definition makespan :: "(nat multiset) list \<Rightarrow> nat" where
  "makespan ms \<equiv> Max (set (map sum_mset ms))"

definition premakespan :: "(nat multiset) list \<Rightarrow> nat" where
  "premakespan ms \<equiv> Min (set (map sum_mset ms))"

lemma balance_append: "balance (xs @ ys) ms = balance xs (balance ys ms)"
  by (induction xs arbitrary:ys) simp_all

lemma balance_split: "balance ts ms = balance (take n ts) (balance (drop n ts) ms)"
  using append_take_drop_id balance_append by metis

lemma premakespan_mono:
  assumes "t > 0"  and "length ms > 0"
  shows "premakespan (balance (t#ts) ms) \<ge> premakespan (balance ts ms)"
    (is "premakespan (balance (t#ts) ms) \<ge> premakespan ?btm")
proof -
  have "sum_mset (add_mset t (hd (sort_key sum_mset ?btm)))
        \<ge> sum_mset (hd (sort_key sum_mset ?btm))" by simp
  moreover have "min (sum_mset (add_mset t (hd (sort_key sum_mset ?btm))))
                  (Min (set (map sum_mset (tl (sort_key sum_mset ?btm)))))
        \<ge> min (sum_mset (hd (sort_key sum_mset ?btm)))
                   (Min (set (map sum_mset (tl (sort_key sum_mset ?btm)))))" by simp
  ultimately have "Min (insert (sum_mset (add_mset t (hd (sort_key sum_mset ?btm))))
                  (set (map sum_mset (tl (sort_key sum_mset ?btm)))))
        \<ge> Min (insert (sum_mset (hd (sort_key sum_mset ?btm)))
                   (set (map sum_mset (tl (sort_key sum_mset ?btm)))))" 
    by (metis List.finite_set Min_insert Min_insert2 empty_iff)
  hence "Min (set (map sum_mset (add_mset t (hd (sort_key sum_mset ?btm))
                               #(tl (sort_key sum_mset ?btm)))))
        \<ge> Min (set (map sum_mset ((hd (sort_key sum_mset ?btm))
                               #(tl (sort_key sum_mset ?btm)))))"
    by (simp add: premakespan_def)
  thus ?thesis using add_job_def premakespan_def balance_length assms
    by (metis balance.simps(2) comp_apply length_sort list.collapse list.size(3)
        not_less_zero set_map set_sort)
qed

lemma premakespan_balance_drop:
  assumes
    mlen: "length ms > 0" and
    tpos: "\<forall> t. t \<in> set xs \<longrightarrow> t > 0"
  shows "premakespan (balance (xs@ys) ms) \<ge> premakespan (balance ys ms)"
proof -
  show ?thesis using tpos
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    have "premakespan (balance as ms) \<le> premakespan (balance (a # as) ms)"
      using premakespan_mono mlen by (simp add: Cons.prems balance_append)
    hence "premakespan (balance (a # (as @ ys)) ms) \<ge> premakespan (balance ys ms)"
      using balance_append balance_length premakespan_mono mlen Cons 
      by (metis insert_iff list.simps(15) order_trans)
    thus ?case by simp
  qed
qed

section \<open>Some general lemmas\<close>

lemma mult_max_ge_sum_list:
  assumes "x = Max (set xs)"
  shows "length xs * x \<ge> sum_list xs"
proof -
  have "\<forall>y. y \<in> set xs \<longrightarrow> id y \<le> (\<lambda>_. x) y" using assms by simp
  hence "sum_list (replicate (length xs) x) \<ge> sum_list xs"
    using sum_list_mono
    by (metis id_apply list.map_id0 map_replicate_const)
  moreover have "length xs * x = sum_list (replicate (length xs) x)" by (induction xs) simp_all
  ultimately show ?thesis by simp
qed

lemma mult_min_le_sum_list:
  assumes "x = Min (set xs)"
  shows "length xs * x \<le> sum_list xs"
proof -
  have "\<forall>y. y \<in> set xs \<longrightarrow> id y \<ge> (\<lambda>_. x) y" using assms by simp
  hence "sum_list (replicate (length xs) x) \<le> sum_list xs"
    using sum_list_mono
    by (metis id_apply list.map_id0 map_replicate_const)
  moreover have "length xs * x = sum_list (replicate (length xs) x)" by (induction xs) simp_all
  ultimately show ?thesis by simp
qed

lemma mult_size_sum_mset: "sum_mset xs \<ge> size xs * Min_mset xs"
  by (metis (no_types) mult_min_le_sum_list mset_sorted_list_of_multiset
      set_sorted_list_of_multiset size_mset sum_mset_sum_list)

lemma sum_mset_mult_size: 
  assumes "\<forall>x. x \<in># xs \<longrightarrow> x > 0" and "\<forall>x. x \<in># xs \<longrightarrow> x \<ge> a"
  shows "sum_mset xs \<ge> size xs * a"
  using assms
  by (metis Min_in finite_set_mset mult_not_zero nat_mult_le_cancel_disj order_trans
      set_mset_eq_empty_iff size_empty mult_size_sum_mset)

lemma size_Union_mset: "size (\<Union># (mset xs)) = sum_list (map size xs)"
  by (induction xs) simp_all

lemma sum_mset_subset_eq:
  fixes M N :: "('a :: ordered_cancel_comm_monoid_diff) multiset"
  shows "M \<subseteq># N \<Longrightarrow> sum_mset M \<le> sum_mset N"
  by (metis le_iff_add mset_subset_eq_exists_conv sum_mset.union)

lemma sum_mset_plus:
  fixes x y :: nat
  shows "sum_mset (mset [x, y]) = x + y"
  by simp

lemma pair_in_mset:
  assumes "x \<noteq> y" and "x \<in># A" and "y \<in># A"
  shows "mset [x, y] \<subseteq># A"
  using assms by (metis insert_DiffM insert_noteq_member mset.simps(1) mset.simps(2)
      mset_subset_eq_add_mset_cancel single_subset_iff)

lemma sum_mset_replicate:
  assumes "replicate_mset n x \<subseteq># A"
  shows "n * x \<le> sum_mset A"
  using assms sum_mset_subset_eq by fastforce

lemma mset_replicate:
  shows "mset (replicate n x) = replicate_mset n x"
  by (induction n) simp_all

section \<open>Time bounds\<close>

text \<open>If the makespan computed by 'balance' is smaller
      than the makespan of any schedule by some constant factor,
      it includes the optimal makespan.

      Therefore, we do not need to specify explicitly that the optimal makespan
      is the minimal one of all possible makespans.

      Otherwise, we follow the textbook proof by Kleinberg and Tardos, mostly.
      For simplicity, we avoid reasoning about reals.\<close>

lemma makespan_ge_avg: (* Lemma 11.1 in KT *)
  fixes ms::"(nat multiset) list"
  assumes "schedule ts ms" and "length ms > 0"
  shows "length ms * makespan ms \<ge> sum_list ts"
  using assms makespan_def loads_eq_times
  by (metis length_map mult_max_ge_sum_list)

text \<open>The textbook proof employs reasoning about array indices which is cumbersome to formalize.
      Encoding the index 'j' used in the textbook proof to denote the last job placed on a machine
      that attains the makespan is particularly difficult.

      We keep ourselves to reasoning about lists instead.
      To that end, we define the list of jobs 'ts' as a concatenation of two lists 'us' and 'vs',
      where the second list is non-empty and contains jobs 1..j.
      The length of 'vs' is equal to 'j', and we encode this idea with the 'j_def' assumption.
      The head of 'vs' corresponds to 't_j' in the textbook proof.

      By observation made in the first paragraph of the textbook proof of Theorem 11.3,
      a makespan is attained after placing a job on a machine with the _smallest_ load.
      We define that load as 'premakespan'.

      Thus, 'j_def' should be understood as follows: the last job contributing to the makespan
      is the head element of some suffix of the job list for which a makespan is computed
      that is equal to the makespan for the unmodified job list.

      The elements of 'us' are placed on other machines and do not contribute to makespan.
      Lemma 'premakespan_balance_drop' contains the proof of this fact.

      It is possible, indeed, to rewrite the proof without defining 'ts' as a concatenation
      of lists by using 'take' and 'drop' as needed, but such a proof would turn out _less_ readable
      and more difficult to maintain.\<close>

lemma balance_optimal_common:
  fixes ms::"(nat multiset) list"
  assumes
    mpos:    "m > 0" and
    mrep:    "ms = replicate m {#}" and
    ts_def:  "ts = us@vs \<and> length vs > 0 \<and> (\<forall> t. t \<in> set ts \<longrightarrow> t > 0)" and
    mos_def: "schedule ts mos \<and> length mos = m" and
    topt:    "Topt = makespan mos" and
    T_def:   "T = makespan (balance ts ms)" and
    j_def:   "T = hd vs + premakespan (balance (tl vs) ms)"
  shows "T - hd vs \<le> Topt"
proof -
  have "premakespan (balance (tl vs) ms) \<le> premakespan (balance vs ms)"
    using premakespan_mono ts_def mpos mrep
    by (metis in_set_conv_decomp length_replicate less_irrefl list.exhaust_sel list.size(3))
  hence "T - hd vs \<le> premakespan (balance ts ms)"
    using premakespan_balance_drop ts_def T_def j_def mpos mrep
    by (metis Un_iff add_diff_cancel_left' length_replicate order_trans set_append)
  moreover have "length (balance ts ms) = m" using mpos mrep balance_length by simp
  ultimately have  "m * (T - hd vs) \<le> sum_list (map sum_mset (balance ts ms))"
    using premakespan_def mpos
    by (metis mult_min_le_sum_list length_map nat_mult_le_cancel_disj order_trans)
  hence "m * (T - hd vs) \<le> sum_list ts"
    using schedule_balance loads_eq_times mpos mrep by metis
  hence "m * (T - hd vs) \<le> m * Topt"
    using makespan_ge_avg mos_def topt order_trans by fastforce
  thus ?thesis using mpos by simp
qed

subsection \<open>Greedy-Balance\<close>

lemma makespan_ge_t: (* Lemma 11.2 in KT *)
  fixes ms::"(nat multiset) list"
  assumes msch: "schedule ts ms"
  shows "t \<in> set ts \<longrightarrow> makespan ms \<ge> t"
proof -
  have "t \<in> set ts \<longrightarrow> (\<exists>m. m \<in> set ms \<and> t \<in># m)"
    using schedule_def msch by (metis in_Union_mset_iff set_mset_mset)
  then obtain m where t_in_m: "t \<in> set ts \<longrightarrow> (m \<in> set ms \<and> t \<in># m)" by auto
  hence "t \<in> set ts \<longrightarrow> t \<le> sum_mset m" using sum_mset.remove by fastforce
  moreover have "m \<in> set ms \<longrightarrow> makespan ms \<ge> sum_mset m" using makespan_def by simp
  ultimately show ?thesis using t_in_m order_trans by fastforce
qed

theorem greedy_balance_optimal: (* Theorem 11.3 in KT *)
  assumes
    mpos:    "m > 0" and
    mrep:    "ms = replicate m {#}" and
    ts_def:  "ts = us@vs \<and> length vs > 0 \<and> (\<forall> t. t \<in> set ts \<longrightarrow> t > 0)" and
    mos_def: "schedule ts mos \<and> length mos = m" and
    topt:    "Topt = makespan mos" and
    T_def:   "T = makespan (balance ts ms)" and
    j_def:   "T = hd vs + premakespan (balance (tl vs) ms)"
  shows "T \<le> 2 * Topt"
proof -
  have "hd vs \<in> set ts" using ts_def by simp
  hence "T - hd vs + hd vs \<le> 2 * Topt"
    using balance_optimal_common makespan_ge_t assms by (metis add_mono mult_2)
  thus  ?thesis by linarith
qed

subsection \<open>Sorted-Balance\<close>

text \<open>Note that 'balance' schedules jobs starting from the end of the job list.
      Its head is scheduled last. Therefore, it must be sorted in the _increasing_ order.\<close>

lemma makespan_ge_2t: (* Lemma 11.4 in KT*)
  fixes ms::"(nat multiset) list"
  assumes
    ts_def:  "ts = us@vs \<and> length vs > 0 \<and> (\<forall> t. t \<in> set ts \<longrightarrow> t > 0)" and
    msch: "schedule ts ms" and
    ms_le_ts: "vs = qs@rs \<and> length qs > 0 \<and> length rs = length ms" and
    ts_sorted: "sorted ts" and
    opt_greedy: "\<forall>m. m \<in> set ms \<longrightarrow> (\<exists>u. u \<in> set rs \<and> u \<in># m)"
  shows "t \<in> set qs \<longrightarrow> makespan ms \<ge> 2 * t"
proof -
  have "t \<in> set qs \<longrightarrow> (\<exists>m. m \<in> set ms \<and> t \<in># m)"
    using schedule_def msch ms_le_ts
     by (metis (no_types, hide_lams) Un_iff in_Union_mset_iff set_append set_mset_mset ts_def)
  then obtain m where t_in_m: "t \<in> set qs \<longrightarrow> (m \<in> set ms \<and> t \<in># m)" by auto
  obtain u where u_in_m: "m \<in> set ms \<longrightarrow> u \<in> set rs \<and> u \<in># m" using opt_greedy by auto
  have "t \<in> set qs \<and> m \<in> set ms \<longrightarrow> t + u \<le> sum_mset m"
  proof (cases "t \<noteq> u")
    case True
    hence "t \<in> set qs \<and> m \<in> set ms \<longrightarrow> mset [t, u] \<subseteq># m" by (meson pair_in_mset t_in_m u_in_m)
    thus ?thesis using sum_mset_subset_eq by fastforce
  next
    case False
    have "t \<in> set qs \<and> m \<in> set ms \<longrightarrow> count m t \<ge> 2" sorry
    thus ?thesis using False sum_mset_replicate
      by (metis count_le_replicate_mset_subset_eq mult_2)
  qed
  moreover have "t \<in> set qs \<and> m \<in> set ms \<longrightarrow> t \<le> u"
    using ts_def ts_sorted ms_le_ts sorted_append u_in_m by blast
  moreover have "m \<in> set ms \<longrightarrow> makespan ms \<ge> sum_mset m" using makespan_def by simp
  ultimately show ?thesis using ms_le_ts t_in_m u_in_m by auto
qed

text \<open>As before, we avoid reasoning about array indices by defining the structure of 'ts'.
      In addition to 'j' (the index of the last job contributing to the makespan),
      the textbook proof of the stronger Theorem 11.5 also uses the index 'm',
      which is equal to the number of machines available. We encode it by defining 'vs'
      as a concatenation of lists 'qs' (jobs m+1..j) and 'rs' (jobs 1..m).

      This means that 'j' is implicitly assumed to be greater than 'm'.
      This assumption is present in the second paragraph of textbook proof.\<close>

theorem sorted_balance_optimal: (* Theorem 11.5 in KT *)
  assumes
    mpos:    "m > 0" and
    mrep:    "ms = replicate m {#}" and
    ts_def:  "ts = us@vs \<and> length vs > 0 \<and> (\<forall> t. t \<in> set ts \<longrightarrow> t > 0)" and
    mos_def:  "schedule ts mos \<and> length mos = m" and
    topt:    "Topt = makespan mos" and
    T_def:   "T = makespan (balance ts ms)" and
    j_def:   "T = hd vs + premakespan (balance (tl vs) ms)" and
    (* Additional assumptions allow us to prove a tighter upper bound: *)
    ms_le_ts: "vs = qs@rs \<and> length qs > 0 \<and> length rs = m" and
    ts_sorted: "sorted ts" and
    opt_greedy: "\<forall>m. m \<in> set mos \<longrightarrow> (\<exists>u. u \<in> set rs \<and> u \<in># m)"
  shows "2 * T \<le> 3 * Topt"
proof -
  have "hd vs \<in> set qs" using ms_le_ts by simp
  moreover have "2 * T - 2 * hd vs \<le> 2 * Topt" using balance_optimal_common assms
    by (metis nat_mult_le_cancel_disj right_diff_distrib')
  ultimately have "2 * T - 2 * hd vs + 2 * hd vs \<le> 3 * Topt" using makespan_ge_2t assms
    by (metis add.commute add_mono mult_Suc numeral_2_eq_2 numeral_3_eq_3)
  thus ?thesis using add_increasing2 by linarith
qed