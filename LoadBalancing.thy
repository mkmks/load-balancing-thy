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

section \<open>Some useful properties\<close>

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

lemma balance_append:
  shows "balance (xs @ ys) ms = balance xs (balance ys ms)"
  by (induction xs arbitrary:ys) simp_all

(* no 'zipWith' or even 'uncurry' in the standard library? *)
definition zip_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zip_with f xs ys \<equiv> map (scomp id f) (zip xs ys)"

lemma schedule_mono:
  assumes
    "schedule ys ms" and "schedule (xs@ys) (zip_with (op +) ms ns)" and
    "\<forall> y. y \<in> set ys \<longrightarrow> y > 0" and
    "length ms = length ns"
  shows "makespan ms \<le> makespan (zip_with (op +) ms ns)"
proof -
  have "\<Union># (mset (zip_with (op +) ms ns)) = \<Union># (mset ms) + \<Union># (mset ns)"
    sorry
  have "\<Union># (mset ms) = mset ys \<and> \<Union># (mset (zip_with (op +) ms ns)) = mset (xs@ys)"
    using schedule_def assms by simp
  have "Max (set (map sum_mset ms)) \<le> Max (set (map sum_mset (zip_with (op +) ms ns)))" sorry
  thus ?thesis by (simp add: makespan_def)
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
  using mult_min_le_sum_list
  by (metis (no_types) mset_sorted_list_of_multiset
      set_sorted_list_of_multiset size_mset sum_mset_sum_list)

lemma size_Union_mset: "size (\<Union># (mset xs)) = sum_list (map size xs)"
  by (induction xs) simp_all

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
  using assms makespan_def loads_eq_times mult_max_ge_sum_list
  by (metis length_map)

lemma balance_optimal_common:
  fixes ms::"(nat multiset) list"
  assumes
    mpos:    "m > 0" and
    mrep:    "ms = replicate m {#}" and
    tpos:    "\<forall> t. t \<in> set ts \<longrightarrow> t > 0" and
    mos_def: "schedule ts mos \<and> length mos = m" and
    topt:    "Topt = makespan mos" and
    T_def:   "T = makespan (balance ts ms)" and
    j_def:   "j = Max_mset (last (sort_key sum_mset ms)) \<and> j < length ts"
  shows "T - ts ! j \<le> Topt"
proof -
  have "T - ts ! j = Min (set (map sum_mset (balance ts ms)))"
    using mrep tpos T_def j_def sorry
  moreover have "length (balance ts ms) = m" using mpos mrep balance_length by simp
  ultimately have  "m * (T - ts ! j) \<le> sum_list (map sum_mset (balance ts ms))"
    using mult_min_le_sum_list mpos by fastforce
  hence "m * (T - ts ! j) \<le> sum_list ts"
    using schedule_balance loads_eq_times mpos mrep by metis
  hence "m * (T - ts ! j) \<le> m * Topt"
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
    tpos:    "\<forall> t. t \<in> set ts \<longrightarrow> t > 0" and
    mos_def: "schedule ts mos \<and> length mos = m" and
    topt:    "Topt = makespan mos" and
    T_def:   "T = makespan (balance ts ms)" and
    j_def:   "j = Max_mset (last (sort_key sum_mset ms)) \<and> j < length ts"
  shows "T \<le> 2 * Topt"
proof -
  have "T - ts ! j + ts ! j \<le> 2 * Topt"
    using balance_optimal_common makespan_ge_t assms
    by (metis add_mono mult_2 nth_mem)
  thus  ?thesis by linarith
qed

subsection \<open>Sorted-Balance\<close>

text \<open>Note that 'balance' schedules jobs starting from the end of the job list.
      Its head is scheduled last. Therefore, it must be sorted in the _increasing_ order.\<close>

lemma makespan_ge_2t: (* Lemma 11.4 in KT*)
  fixes ms::"(nat multiset) list"
  assumes
    tpos: "\<forall> t. t \<in> set ts \<longrightarrow> t > 0" and
    msch: "schedule ts ms" and
    ms_le_ts: "length ms < length ts" and
    tssorted: "sorted ts"
  shows "makespan ms \<ge> 2 * ts ! (length ts - Suc (length ms))"
proof -
  have "\<exists>ns. schedule (drop (length ts - Suc (length ms)) ts) ns \<and> length ns = length ms"
    using schedule_balance balance_length loads_eq_times member_le_sum_list
    using tpos msch ms_le_ts
    by (metis Suc_le_eq last_in_set length_map length_replicate less_imp_Suc_add
        list.exhaust list.size(4) nat.simps(3) neq0_conv replicate.simps(2)sum_list_simps(1))
  then obtain ns where ns_def: "schedule (drop (length ts - Suc (length ms)) ts) ns \<and>
                                length ns = length ms" by auto
  hence "\<exists>n. n \<in> set ns \<and> size n \<ge> 2" (* holy pigeons! *)
  proof -    
    have 1: "sum_list (map size ns) = size (\<Union># (mset ns))" by (simp add: size_Union_mset)
    moreover have 2: "\<dots> = length (drop (length ts - Suc (length ms)) ts)"
      using ns_def schedule_def by auto
    moreover have 3: "\<dots> = Suc (length ns)" by (simp add: Suc_leI ms_le_ts ns_def)
    moreover have 4: "Max (set (map size ns)) \<ge> 2" using 1 2 3
      by (metis One_nat_def Suc_n_not_le_n le_less_linear le_zero_eq length_map
          less_2_cases mult.right_neutral mult_eq_0_iff mult_max_ge_sum_list nat.simps(3))
    ultimately have "\<exists>n. n \<in> size ` set ns \<and> n \<ge> 2"
      by (metis List.finite_set Max_in nat.simps(3) set_empty set_map sum_list_simps(1))
    thus ?thesis by auto
  qed
  then obtain n where nsize: "n \<in> set ns \<and> size n \<ge> 2" by auto
  moreover have "Min_mset n \<ge> ts ! (length ts - Suc (length ms))"
  proof -
    have "sorted (drop (length ts - Suc (length ms)) ts)" using tssorted sorted_drop by auto
    moreover have "ts ! (length ts - Suc (length ms)) = hd (drop (length ts - Suc (length ms)) ts)"
      using ms_le_ts ns_def nsize
      by (metis diff_less dual_order.strict_trans hd_drop_conv_nth
          length_pos_if_in_set zero_less_Suc)
    ultimately have "\<forall>t. t \<in> set (drop (length ts - Suc (length ms)) ts) \<longrightarrow>
              t \<ge> ts ! (length ts - Suc (length ms))"
      using tssorted ms_le_ts
      by (metis Suc_leI diff_diff_cancel length_drop list.collapse list.size(3)
          nat.simps(3) nat_neq_iff not_le set_ConsD sorted_Cons)
    moreover have "\<forall>t. t \<in># n \<longrightarrow> t \<in> set (drop (length ts - Suc (length ms)) ts)"
      using schedule_def nsize
      by (metis in_Union_mset_iff ns_def set_mset_mset)
    moreover have "Min_mset n \<in># n"
      by (metis Min_in empty_iff finite_set_mset le_zero_eq multiset_nonemptyE nat.simps(3)
          nsize numeral_2_eq_2 size_empty)
    ultimately show ?thesis by simp
  qed
  ultimately have "sum_mset n \<ge> 2 * ts ! (length ts - Suc (length ms))"
    using mult_size_sum_mset by (metis mult.commute mult_le_mono1 order_trans)
  hence "makespan ns \<ge> 2 * ts ! (length ts - Suc (length ms))"
    using nsize makespan_def by (metis List.finite_set Max_ge image_eqI order_trans set_map)
  moreover have "schedule (drop (length ts - Suc (length ms)) ts) ns" using ns_def by auto
  moreover have "schedule ((take (length ts - Suc (length ms)) ts)
                          @(drop (length ts - Suc (length ms)) ts)) ms" by (simp add: msch)
  moreover have "\<forall> t. t \<in> set (drop (length ts - Suc (length ms)) ts) \<longrightarrow> t > 0" using tpos
    by (meson in_set_dropD)
  ultimately show ?thesis using schedule_mono order_trans by blast
qed

theorem sorted_balance_optimal: (* Theorem 11.5 in KT *)
  assumes
    mpos:    "m > 0" and
    mrep:    "ms = replicate m {#}" and
    tpos:    "\<forall> t. t \<in> set ts \<longrightarrow> t > 0" and
    mos_def:  "schedule ts mos \<and> length mos = m" and
    topt:    "Topt = makespan mos" and
    T_def:   "T = makespan (balance ts ms)" and
    j_def:   "j = Max_mset (last (sort_key sum_mset ms)) \<and> j < length ts" and
    (* Additional assumptions allow us to prove a tighter upper bound: *)
    ms_le_ts: "length ms < length ts" and
    tssorted: "sorted ts"
  shows "2 * T \<le> 3 * Topt"
proof -
  have "length ms = length mos" using mos_def mrep by simp
  hence mos_le_ts: "length mos < length ts" using ms_le_ts by simp
  moreover have "ts ! (length ts - Suc m) \<in> set (take (length ts - length ms) ts)"
    using mos_def ms_le_ts \<open>length ms = length mos\<close>
    by (metis Suc_diff_Suc drop_rev in_set_conv_nth length_drop length_rev lessI nth_take)
  ultimately have "2 * T - 2 * ts ! j + 2 * ts ! (length ts - Suc m) \<le> 3 * Topt"
    using balance_optimal_common makespan_ge_2t \<open>length ms = length mos\<close> assms
    by (metis add.commute add_mono mult_Suc nat_mult_le_cancel_disj
        numeral_2_eq_2 numeral_3_eq_3 right_diff_distrib')
  moreover have "ts ! j \<le> ts ! (length ts - Suc m)"
  proof -
    have "j < length ts - m" using j_def sorry
    moreover have "m < length ts" using mrep ms_le_ts by simp
    ultimately show ?thesis using j_def tssorted by (simp add: sorted_nth_mono)
  qed
  ultimately show ?thesis using add_increasing2 by linarith
qed