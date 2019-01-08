theory LoadBalancing imports Complex_Main Groups_List "HOL-Library.Multiset"
begin

text \<open>For each machine, we keep a set of assigned jobs represented as their execution times.
      The algorithm assumes that the jobs are always placed on the machine with the smallest load.
      We implement this assumption by sorting the list of machines by their load before placing jobs.
      The head of the sorted list will therefore have the smallest load.\<close>

definition schedule :: "nat list \<Rightarrow> (nat multiset) list \<Rightarrow> bool" where
  "schedule ts ms \<equiv> \<Union># (mset ms) = mset ts"

definition makespan :: "(nat multiset) list \<Rightarrow> nat" where
  "makespan ms \<equiv> Max (set (map sum_mset ms))"

definition add_job :: "nat \<Rightarrow> (nat multiset) list \<Rightarrow> (nat multiset) list" where
  "add_job n ms \<equiv>  add_mset n (hd ms)#(tl ms)"

text \<open>This job scheduling function takes a list of job execution times and uses it
      to mutate the schedule. The proofs about optimal upper bounds will assume that the function
      is called with an empty schedule, i.e., 'replicate m {#}',
      where 'm' stands for the number of machines available.

      The first element of the job list is scheduled last.\<close>

fun balance :: "nat list \<Rightarrow> (nat multiset) list \<Rightarrow> (nat multiset) list" where
"balance []     = id" |
"balance (t#ts) = add_job t \<circ> sort_key sum_mset \<circ> balance ts"

text \<open>Test cases\<close>
(* Figure 11.1 in KT*)
value \<open>balance (rev [2,3,4,6,2,2]) (replicate 3 {#})\<close>

theorem balance_length:
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

text \<open>We translate 'max' operators with universal quantification.
      The translations are equivalent to original statements because maximum elements
      only appear in inequalities.
      If all elements of a set are not greater than 'n', it includes the maximum element as well.
      If the maximum element is not greater than 'n', it is true for all other elements as well.

      In particular, if all machine loads in a schedule computed by 'balance' are smaller
      than all machine loads in all possible schedules by some constant factor, it includes
      the makespan computed by 'balance' and the optimal makespan.\<close>

text \<open>Otherwise, we follow the textbook proof by Kleinberg and Tardos, mostly.
      For simplicity, we avoid reasoning about reals.\<close>

lemma mult_max_ge_sumlist:
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

lemma mult_min_le_sumlist:
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

text \<open>The following lemmas encode the lower bounds for ANY makespan,
      including the optimal one.\<close>

lemma premakespan: (* second paragraph the proof of Theorem 11.3 in KT *)
  assumes "ms = replicate m {#}" and "\<forall> t. t \<in> set ts \<longrightarrow> t > 0"
  shows "makespan (balance ts ms) - hd ts = Min (set (map sum_mset (balance ts ms)))"
  sorry

lemma makespan_ge_avg: (* Lemma 11.1 in KT *)
  fixes ms::"(nat multiset) list"
  assumes "schedule ts ms" and "length ms > 0"
  shows "length ms * makespan ms \<ge> sum_list ts"
  using assms makespan_def loads_eq_times mult_max_ge_sumlist
  by (metis length_map)

lemma makespan_ge_t: (* Lemma 11.2 in KT *)
  fixes ms::"(nat multiset) list"
  assumes msch: "schedule ts ms"
  shows "t \<in> set ts \<longrightarrow> makespan ms \<ge> t"
proof -
  have "t \<in> set ts \<longrightarrow> (\<exists>m. m \<in> set ms \<and> t \<in># m)"
    using msch by (metis in_Union_mset_iff schedule_def set_mset_mset)
  then obtain m where "t \<in> set ts \<longrightarrow> (m \<in> set ms \<and> t \<in># m)" by auto
  hence "t \<in> set ts \<longrightarrow> t \<le> sum_mset m" using sum_mset.remove by fastforce
  moreover have "m \<in> set ms \<longrightarrow> makespan ms \<ge> sum_mset m" using makespan_def by simp
  ultimately have "t \<in> set ts \<longrightarrow> makespan ms \<ge> t"
    using \<open>t \<in> set ts \<longrightarrow> m \<in> set ms \<and> t \<in># m\<close> order_trans by fastforce
  then show ?thesis .
qed

theorem greedy_balance_optimal:               (* Theorem 11.3 in KT *)
  assumes
    mpos: "m > 0" and
    mrep: "ms = replicate m {#}" and
    tpos: "\<forall> t. t \<in> set ts \<longrightarrow> t > 0" and
    tspos: "length ts > 0" and
    mopt: "schedule ts mos \<and> length mos = m" and
    topt: "Topt = makespan mos" and
    tmsp: "T = makespan (balance ts ms)"
  shows "T \<le> 2 * Topt"
proof -
  have "length (balance ts ms) = m" using mpos mrep balance_length by simp
  moreover have "T - hd ts = Min (set (map sum_mset (balance ts ms)))"
    using mrep tmsp tpos premakespan by simp
  ultimately have  "m * (T - hd ts) \<le> sum_list (map sum_mset (balance ts ms))"
    using mult_min_le_sumlist mpos by fastforce
  hence "m * (T - hd ts) \<le> sum_list ts"
    using mpos mrep schedule_balance loads_eq_times by metis
  hence "m * (T - hd ts) \<le> m * Topt"
    using mopt topt makespan_ge_avg order_trans by fastforce
  hence "T - hd ts \<le> Topt"
    using mpos by simp
  hence "T - hd ts + hd ts \<le> 2 * Topt"
    using tspos mopt topt makespan_ge_t
    by (metis add_mono length_greater_0_conv list.set_sel(1) mult_2)
  thus  ?thesis by linarith
qed

lemma makespan_ge_2t: (* Lemma 11.4 in KT*)
  fixes ms::"(nat multiset) list"
  assumes
    msch: "schedule ts ms" and
    tlen: "length ts > length ms"
  shows "makespan ms \<ge> 2 * ts ! (Suc (length ms))"
  sorry

theorem sorted_balance_optimal:                   (* Theorem 11.5 in KT *)
  assumes
    mpos: "m > 0" and
    mrep: "ms = replicate m {#}" and
    tpos: "\<forall> t. t \<in> set ts \<longrightarrow> t > 0" and
    tspos: "length ts > 0" and
    mopt: "schedule ts mos \<and> length mos = m" and
    topt: "Topt = makespan mos" and
    tmsp: "T = makespan (balance ts ms)" and
    (* Additional assumptions allow us to prove a tighter upper bound: *)
    tslen: "length ts > length ms" and
    tssorted: "i < j \<longrightarrow> ts ! i \<ge> ts ! j"
  shows "2 * T \<le> 3 * Topt"
proof -
  have "length (balance ts ms) = m" using mpos mrep balance_length by simp
  moreover have "T - hd ts = Min (set (map sum_mset (balance ts ms)))"
    using mrep tmsp tpos premakespan by simp
  ultimately have  "m * (T - hd ts) \<le> sum_list (map sum_mset (balance ts ms))"
    using mult_min_le_sumlist mpos by fastforce
  hence "m * (T - hd ts) \<le> sum_list ts"
    using mpos mrep schedule_balance loads_eq_times by metis
  hence "m * (T - hd ts) \<le> m * Topt"
    using mopt topt makespan_ge_avg order_trans by fastforce
  hence "2 * T - 2 * hd ts \<le> 2 * Topt"
    using mpos by simp
  hence "2 * T - 2 * hd ts + 2 * ts ! (Suc m) \<le> 3 * Topt"
    using mpos mopt topt tspos tslen makespan_ge_2t order_trans sorry
  moreover have "ts ! 0 \<ge> ts ! (Suc m)"
    using tspos tssorted sorry
  ultimately show ?thesis using tspos sorry
qed