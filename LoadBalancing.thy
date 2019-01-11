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

lemma balance_append: "balance (xs @ ys) ms = balance xs (balance ys ms)"
  by (induction xs arbitrary:ys) simp_all

lemma balance_split: "balance ts ms = balance (take n ts) (balance (drop n ts) ms)"
  using append_take_drop_id balance_append by metis

definition premakespan :: "(nat multiset) list \<Rightarrow> nat" where
  "premakespan ms \<equiv> Min (set (map sum_mset ms))"

lemma premakespan_mono:
  assumes "t > 0"  and "length ms > 0"
  shows "premakespan (balance (t#ts) ms) \<ge> premakespan (balance ts ms)"
proof -
  have "sum_mset (add_mset t (hd (sort_key sum_mset (balance ts ms))))
        \<ge> sum_mset (hd (sort_key sum_mset (balance ts ms)))" by simp
  moreover have "min (sum_mset (add_mset t (hd (sort_key sum_mset (balance ts ms)))))
                  (Min (set (map sum_mset (tl (sort_key sum_mset (balance ts ms))))))
        \<ge> min (sum_mset (hd (sort_key sum_mset (balance ts ms))))
                   (Min (set (map sum_mset (tl (sort_key sum_mset (balance ts ms))))))" by simp
  ultimately have "Min (insert (sum_mset (add_mset t (hd (sort_key sum_mset (balance ts ms)))))
                  (set (map sum_mset (tl (sort_key sum_mset (balance ts ms))))))
        \<ge> Min (insert (sum_mset (hd (sort_key sum_mset (balance ts ms))))
                   (set (map sum_mset (tl (sort_key sum_mset (balance ts ms))))))" 
    by (metis List.finite_set Min_insert Min_insert2 empty_iff)
  hence "Min (set (map sum_mset (add_mset t (hd (sort_key sum_mset (balance ts ms)))
                               #(tl (sort_key sum_mset (balance ts ms))))))
        \<ge> Min (set (map sum_mset ((hd (sort_key sum_mset (balance ts ms)))
                               #(tl (sort_key sum_mset (balance ts ms))))))"
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
    have "balance (a # as @ ys) ms = balance (a # as) (balance ys ms)"
      by (simp add: balance_append)
    moreover have "premakespan (balance as ms) \<le> premakespan (balance (a # as) ms)"
      using balance_append premakespan_mono mlen by (simp add: Cons.prems)
    ultimately have "premakespan (balance (a # (as @ ys)) ms) \<ge> premakespan (balance ys ms)"
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
  using mult_min_le_sum_list
  by (metis (no_types) mset_sorted_list_of_multiset
      set_sorted_list_of_multiset size_mset sum_mset_sum_list)

lemma sum_mset_mult_size: 
  assumes "\<forall>x. x \<in># xs \<longrightarrow> x > 0" and "\<forall>x. x \<in># xs \<longrightarrow> x \<ge> a"
  shows "sum_mset xs \<ge> size xs * a"
  using assms mult_size_sum_mset
  by (metis Min_in finite_set_mset mult_not_zero nat_mult_le_cancel_disj order_trans
      set_mset_eq_empty_iff size_empty)

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
    j_def:   "T - ts ! j = premakespan (balance (drop (length ts - j) ts) ms) \<and> j > 0"
  shows "T - ts ! j \<le> Topt"
proof -
  have "\<forall>t. t \<in> set (take (length ts - j) ts) \<longrightarrow> t > 0"
    using tpos j_def by (meson in_set_takeD)
  hence "T - ts ! j \<le> premakespan (balance ts ms)"
    using mpos mrep tpos j_def premakespan_balance_drop
    by (metis append_take_drop_id length_replicate)
  moreover have "length (balance ts ms) = m" using mpos mrep balance_length by simp
  ultimately have  "m * (T - ts ! j) \<le> sum_list (map sum_mset (balance ts ms))"
    using premakespan_def mult_min_le_sum_list mpos
    by (metis length_map nat_mult_le_cancel_disj order_trans)
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
    j_def:   "T - ts ! j = premakespan (balance (drop (length ts - j) ts) ms) \<and>
                           j > 0 \<and> j < length ts"
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
    ts_sorted: "sorted ts"
  shows "makespan ms \<ge> 2 * ts ! (length ts - Suc (length ms))"
proof -
  have "\<exists>m. m \<in> set ms \<and> size m \<ge> 2" (* holy pigeons! *)
  proof -    
    have 1: "sum_list (map size ms) = size (\<Union># (mset ms))" by (simp add: size_Union_mset)
    moreover have 2: "\<dots> = length ts"
      using schedule_def msch by auto
    moreover have "Max (set (map size ms)) \<ge> 2" using 1 2 ms_le_ts
      by (metis One_nat_def leD le_less_linear le_zero_eq length_map less_2_cases
          mult.right_neutral mult_max_ge_sum_list mult_not_zero not_less0)
    ultimately have "\<exists>m. m \<in> size ` set ms \<and> m \<ge> 2" using ms_le_ts
      by (metis List.finite_set Max_in image_set not_le set_empty sum_list_simps(1) zero_le)
    thus ?thesis by auto
  qed
  then obtain m where msize: "m \<in> set ms \<and> size m \<ge> 2" by auto
  moreover have "\<forall>t. t \<in># m \<longrightarrow> t > 0"
  proof -
    have "m \<in> set ms" by (simp add: msize)
    moreover have "\<forall>t. t \<in># \<Union># (mset ms) \<longrightarrow> t \<in> set ts" using msch by (simp add: schedule_def)
    ultimately show ?thesis using tpos by auto
  qed
  moreover have "\<forall>t. t \<in># m \<longrightarrow> t \<ge> ts ! (length ts - Suc (length ms))"
  proof -
    have "ts ! (length ts - Suc (length ms)) = hd (drop (length ts - Suc (length ms)) ts)"
      using ms_le_ts msize by (metis Suc_diff_Suc diff_less_Suc hd_drop_conv_nth not_less_eq)
    moreover have "sorted (drop (length ts - length ms) ts)"
      using ts_sorted sorted_drop by auto
    ultimately have "\<forall>t. t \<in> set (drop (length ts - length ms) ts) \<longrightarrow>
                t \<ge> ts ! (length ts - length ms)" using ms_le_ts  ts_sorted msize
      by (metis Cons_nth_drop_Suc diff_less drop_Nil le_less_linear length_greater_0_conv
          length_pos_if_in_set nat_neq_iff set_ConsD sorted_Cons)
    then have "\<forall>n. n \<in> set ms \<and> size n \<ge> 2 \<longrightarrow>
                     (\<exists>t. t \<in># n \<and> t \<in> set (take (length ts - length ms) ts))"
      using schedule_def msch ms_le_ts sorry
    then show ?thesis using msize ts_sorted sorry
  qed
  ultimately have "sum_mset m \<ge> 2 * ts ! (length ts - Suc (length ms))"
    using sum_mset_mult_size  by (meson mult_le_mono1 order_trans)
  thus ?thesis using makespan_def msize
    by (metis List.finite_set Max_ge image_eqI order_trans set_map)
qed

theorem sorted_balance_optimal: (* Theorem 11.5 in KT *)
  assumes
    mpos:    "m > 0" and
    mrep:    "ms = replicate m {#}" and
    tpos:    "\<forall> t. t \<in> set ts \<longrightarrow> t > 0" and
    mos_def:  "schedule ts mos \<and> length mos = m" and
    topt:    "Topt = makespan mos" and
    T_def:   "T = makespan (balance ts ms)" and
    j_def:   "T - ts ! j = premakespan (balance (drop (length ts - j) ts) ms) \<and>
                           j > 0 \<and> j < length ts" and
    (* Additional assumptions allow us to prove a tighter upper bound: *)
    ms_le_ts: "length ms < length ts" and
    ts_sorted: "sorted ts"
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
    ultimately show ?thesis using j_def ts_sorted by (simp add: sorted_nth_mono)
  qed
  ultimately show ?thesis using add_increasing2 by linarith
qed