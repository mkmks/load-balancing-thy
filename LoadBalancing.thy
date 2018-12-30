theory LoadBalancing imports Complex_Main Groups_Big Groups_List "HOL-Library.Multiset"
begin

(* For each machine, we keep a set of jobs assigned to it (represented as indices into the job list)
   together with the sum of their execution times. The algorithm assumes that the jobs are
   always placed on the machine with the smallest load. We implement this assumption by sorting
   the list of machines by their load before placing jobs. The head of the sorted list will
   therefore have the smallest load. *)

definition add_job :: "nat \<Rightarrow> nat \<Rightarrow> (nat set \<times> nat) list \<Rightarrow> (nat set \<times> nat) list" where
  "add_job n t ms \<equiv> map_prod (insert n) (plus t) (hd ms)#(tl ms)"

(* This job scheduling function takes a list of job execution times and uses it
   to mutate the schedule. The proofs about optimal upper bounds will assume that the function
   is called with an empty schedule, i.e., 'replicate m ({}, 0)',
   where 'm' stands for the number of machines available.

   The first element of the job list is scheduled last.*)

fun balance :: "nat list \<Rightarrow> (nat set \<times> nat) list \<Rightarrow> (nat set \<times> nat) list" where
"balance []     = id" |
"balance (t#ts) = add_job (length ts) t \<circ> sort_key snd \<circ> balance ts"

text \<open>Test cases\<close>
(* Figure 11.1 in KT*)
value \<open>balance (rev [2,3,4,6,2,2]) (replicate 3 ({}, 0))\<close>

(* Note that job indices increase right to left because we manipulate lists and not arrays.
   Read an index as "nth element put on the stack". *)

fun totalTime :: "nat list \<Rightarrow> nat set \<Rightarrow> nat" where
"totalTime ts A = (\<Sum>i\<in>A. ts ! (length ts - i))"

(* The two makespan definitions should lead to identical answers. *)

theorem times_consistent:
  fixes m ts
  shows "\<forall> i. i < m \<Longrightarrow> let ms = balance ts (replicate m ({}, 0))
              in totalTime ts (fst (ms ! i)) = snd (ms ! i)"
  by auto

theorem length_ms_constant:
  fixes m ts
  assumes mpos: "m > 0"
  shows "length (balance ts (replicate m ({}, 0))) = m"
  using mpos add_job_def by (induction rule:balance.induct) auto

lemma sum_list_map_collapse:
  fixes f xs
  assumes len: "length xs > 0"
  shows "f (hd xs) + sum_list (map f (tl xs)) = sum_list (map f xs)"
  using len by (induction xs) auto

lemma sum_list_sort_key_snd:
  fixes xs::"(nat set \<times> nat) list"
  assumes len: "length xs > 0"
  shows "sum_list (map snd (sort_key snd xs)) = sum_list (map snd xs)"
proof -
  have "sum_list (map snd (sort_key snd xs)) = sum_mset (mset (map snd (sort_key snd xs)))"
    using sum_mset_sum_list by metis
  also have "\<dots> = sum_mset (mset (map snd xs))" by simp
  also have "\<dots> = sum_list (map snd xs)"
    using sum_mset_sum_list by metis
  finally show ?thesis .
qed

theorem loads_eq_times:
  fixes m ts
  assumes mpos:"m > 1"
  shows "sum_list (map snd (balance ts (replicate m ({}, 0)))) = sum_list ts"
    (is "sum_list (map snd ?ms) = sum_list ts")
proof (induction ts rule:balance.induct)
  case 1
  then show ?case by simp
next
  case (2 t ts)
  have "length (sort_key snd (balance ts (replicate m ({}, 0)))) > 0"
    using mpos by (simp add:length_ms_constant)
  then show ?case using 2 add_job_def by (simp add: sum_list_map_collapse sum_list_sort_key_snd)
qed

lemma mult_min_le_sumlist:
  fixes m xs
  assumes
    mtwo: "m > 1" and
    mrep: "length xs = m"
  shows "\<exists>x. \<forall>y. x \<in> set xs \<and> y \<in> set xs \<Longrightarrow> x \<le> y \<and> m * x \<le> sum_list xs"
  using le_imp_less_Suc member_le_sum_list by blast
  
(* The following definition uses sets internally and would result in a counterexample:
       topt_avg_t: "Topt \<ge> (1/m)*(\<Sum>i<m. ts ! i)"
   Therefore, all jobs that have identical execution times would collapse into a single job.
   We use sums over lists to avoid this issue.*)

(* We translate 'max' operators with universal quantification.
   The translations are equivalent to original statements because maximum elements
   only appear in inequalities.
   If all elements of a list are not greater than 'n', it includes the maximum element as well.
   If the maximum element is not greater than 'n', it is true for all other elements as well. *)

(* Otherwise, we follow the textbook proof by Kleinberg and Tardos, mostly.
   For simplicity, we avoid reasoning about reals. *)

theorem greedy_balance_optimal:               (* Theorem 11.3 in KT *)
  fixes m ms ts
  assumes
    mtwo: "m > 1" and
    mrep: "ms = replicate m ({}, 0)" and
    topt_avg_t: "m * Topt \<ge> sum_list ts" and  (* Statement 11.1 in KT *)
    topt_max_t: "\<forall>t. t \<in> set ts \<Longrightarrow> Topt \<ge> t" (* Statement 11.2 in KT *)
  shows "\<forall>T. T \<in> set (map snd (balance ts ms)) \<Longrightarrow> T \<le> 2 * Topt"
    (is "\<forall>T. T \<in> set ?B \<Longrightarrow> T \<le> 2 * Topt")
proof -
  have  "\<forall>T. T \<in> set ?B \<Longrightarrow> m * (T - hd ts) \<le> sum_list ?B"
    using mult_min_le_sumlist member_le_sum_list by blast
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> m * (T - hd ts) \<le> sum_list ts"
    using mtwo mrep by (simp add:loads_eq_times)
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> m * (T - hd ts) \<le> m * Topt"
    using mtwo mrep topt_avg_t order_trans by blast
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> T - hd ts \<le> Topt"
    using mtwo by auto
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> T - hd ts + t \<le> 2 * Topt"
    using topt_max_t le_imp_less_Suc member_le_sum_list by blast
  thus  "\<forall>T. T \<in> set ?B \<Longrightarrow> T \<le> 2 * Topt"
    using le_imp_less_Suc member_le_sum_list by blast
qed

theorem sorted_balance_optimal:                   (* Theorem 11.5 in KT *)
  fixes m ms ts
  assumes
    mtwo: "m > 1" and
    mrep: "ms = replicate m ({}, 0)" and
    topt_avg_t: "m * Topt \<ge> sum_list ts" and      (* Statement 11.1 in KT *)
    topt_max_t: "\<forall>t. t \<in> set ts \<Longrightarrow> Topt \<ge> t" and (* Statement 11.2 in KT *)
    (* Additional assumptions allow us to prove a tighter upper bound: *)
    tlen: "length ts > length ms" and
    tssort: "sorted_wrt (op \<ge>) ts" and
    topt_dbl_t: "Topt \<ge> 2 * ts ! (Suc m)"         (* Lemma 11.4 *)
  shows "\<forall>T. T \<in> set (map snd (balance ts ms)) \<Longrightarrow> 2 * T \<le> 3 * Topt"
    (is "\<forall>T. T \<in> set ?B \<Longrightarrow> 2 * T \<le> 3 * Topt")
proof -
  have  "\<forall>T. T \<in> set ?B \<Longrightarrow> m * (T - hd ts) \<le> sum_list ?B"
    using member_le_sum_list by blast
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> m * (T - hd ts) \<le> sum_list ts"
    using mtwo mrep by (simp add:loads_eq_times)
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> m * (T - hd ts) \<le> m * Topt"
    using mtwo mrep topt_avg_t order_trans by blast
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> T - hd ts \<le> Topt"
    using mtwo by auto
  hence "\<forall>T. T \<in> set ?B \<Longrightarrow> 2 * (T - hd ts) + 2 * hd ts \<le> 3 * Topt"
    using topt_dbl_t le_imp_less_Suc member_le_sum_list by blast
  thus "\<forall>T. T \<in> set ?B \<Longrightarrow> 2 * T \<le> 3 * Topt"
    using le_imp_less_Suc member_le_sum_list by blast
qed