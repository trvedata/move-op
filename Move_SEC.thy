theory Move_SEC
  imports Move CRDT.Network
begin

section \<open>Strong Eventual Consistency\<close>

definition apply_op' :: \<open>('t::{linorder}, 'n, 'm) operation \<Rightarrow> ('t, 'n, 'm) state \<rightharpoonup> ('t, 'n, 'm) state\<close> where
  \<open>apply_op' x s \<equiv> case s of (log, tree) \<Rightarrow>
    if unique_parent tree \<and> distinct (map log_time log @ [move_time x]) then
      Some (apply_op x s)
    else None\<close>

fun valid_move_opers :: \<open>('t, 'n, 'm) state \<Rightarrow> 't \<times>('t, 'n, 'm) operation \<Rightarrow> bool\<close> where
  \<open>valid_move_opers _ (i, Move t _ _ _) = (i = t)\<close>

locale move = network_with_constrained_ops _ apply_op' \<open>([], {})\<close> valid_move_opers
begin

lemma kleisli_apply_op' [iff]:
  shows \<open>apply_op' (x :: ('t :: {linorder}, 'n, 'm) operation) \<rhd> apply_op' y = apply_op' y \<rhd> apply_op' x\<close>
proof (unfold kleisli_def, rule ext, clarify)
  fix log :: \<open>('t, 'n, 'm) log_op list\<close> and tree :: \<open>('n \<times> 'm \<times> 'n) set\<close>
  { assume *: \<open>unique_parent tree\<close> \<open>distinct (map log_time log @ [move_time x])\<close> \<open>distinct (map log_time log @ [move_time y])\<close> \<open>move_time x \<noteq> move_time y\<close>
    obtain logx treex where 1: \<open>apply_op x (log, tree) = (logx, treex)\<close>
      using * by (clarsimp simp: apply_op'_def)  (metis surj_pair)
    hence \<open>set (map log_time logx) = {move_time x} \<union> set (map log_time log)\<close>
      using * by (cases x) (rule apply_op_timestampI2; force)
    moreover have \<open>distinct (map log_time logx)\<close>
      using * 1 by (cases x) (rule apply_op_timestampI1; force)
    ultimately have 2: \<open>distinct (map log_time logx @ [move_time y])\<close>
      using * by simp
    obtain logy treey where 3: \<open>apply_op y (log, tree) = (logy, treey)\<close>
      using * by (clarsimp simp: apply_op'_def)  (metis surj_pair)
    hence \<open>set (map log_time logy) = {move_time y} \<union> set (map log_time log)\<close>
      using * by (cases y) (rule apply_op_timestampI2; force)
    moreover have \<open>distinct (map log_time logy)\<close>
      using * 3 by (cases y) (rule apply_op_timestampI1, force, force)
    ultimately have 4: \<open>distinct (map log_time logy @ [move_time x])\<close>
      using * by simp
    have \<open>unique_parent treex\<close> \<open>unique_parent treey\<close>
      using * 1 3 apply_op_unique_parent by blast+
    hence \<open>apply_op' x (log, tree) \<bind> apply_op' y = apply_op' y (log, tree) \<bind> apply_op' x\<close>
      using * 1 2 3 4 by (cases x, cases y, clarsimp simp: apply_op'_def) (rule apply_op_commute2I; force)
  }
  moreover {
    assume *: \<open>unique_parent tree\<close> \<open>distinct (map log_time log @ [move_time x])\<close> \<open>distinct (map log_time log @ [move_time y])\<close> \<open>move_time x = move_time y\<close>
    obtain logx treex where 1: \<open>apply_op x (log, tree) = (logx, treex)\<close>
      using * by (clarsimp simp: apply_op'_def)  (metis surj_pair)
    hence \<open>set (map log_time logx) = {move_time x} \<union> set (map log_time log)\<close>
      using * by (cases x) (rule apply_op_timestampI2; force)
    hence 2: \<open>\<not> distinct (map log_time logx @ [move_time y])\<close>
      using * by simp
    obtain logy treey where 3: \<open>apply_op y (log, tree) = (logy, treey)\<close>
      using * by (clarsimp simp: apply_op'_def)  (metis surj_pair)
    hence \<open> set (map log_time logy) = {move_time y} \<union> set (map log_time log)\<close>
      using * by (cases y) (rule apply_op_timestampI2; force)
    hence 4: \<open>\<not> distinct (map log_time logy @ [move_time x])\<close>
      using * by simp
    have \<open>apply_op' x (log, tree) \<bind> apply_op' y = apply_op' y (log, tree) \<bind> apply_op' x\<close>
      using * 1 2 3 4 by (clarsimp simp: apply_op'_def)
  }
  moreover {
    assume *: \<open>unique_parent tree\<close> \<open>\<not> distinct (map log_time log @ [move_time x])\<close> \<open>distinct (map log_time log @ [move_time y])\<close>
    then have **: \<open>move_time x \<in> set (map log_time log)\<close>
      by auto 
    obtain log1 tree1 where \<open>apply_op y (log, tree) = (log1, tree1)\<close>
      using * by (clarsimp simp: apply_op'_def)  (metis surj_pair)
    moreover hence \<open> set (map log_time log1) = {move_time y} \<union> set (map log_time log)\<close>
      using * by (cases y) (rule apply_op_timestampI2; force)
    hence \<open>move_time x \<in> set (map log_time log1)\<close>
      using ** by blast
    moreover hence \<open>\<not> distinct (map log_time log1 @ [move_time x])\<close>
      by simp
    ultimately have \<open>apply_op' x (log, tree) \<bind> apply_op' y = apply_op' y (log, tree) \<bind> apply_op' x\<close>
      using * by (clarsimp simp: apply_op'_def)
  }
  moreover {
    assume *: \<open>unique_parent tree\<close> \<open>distinct (map log_time log @ [move_time x])\<close> \<open>\<not> distinct (map log_time log @ [move_time y])\<close>
    then have **: \<open>move_time y \<in> set (map log_time log)\<close>
      by auto 
    obtain log1 tree1 where \<open>apply_op x (log, tree) = (log1, tree1)\<close>
      using * by (clarsimp simp: apply_op'_def)  (metis surj_pair)
    moreover hence \<open> set (map log_time log1) = {move_time x} \<union> set (map log_time log)\<close>
      using * by (cases x) (rule apply_op_timestampI2; force)
    hence \<open>move_time y \<in> set (map log_time log1)\<close>
      using ** by blast
    moreover hence \<open>\<not> distinct (map log_time log1 @ [move_time y])\<close>
      by simp
    ultimately have \<open>apply_op' x (log, tree) \<bind> apply_op' y = apply_op' y (log, tree) \<bind> apply_op' x\<close>
      using * by (clarsimp simp: apply_op'_def)
  }
  ultimately show \<open>apply_op' x (log, tree) \<bind> apply_op' y = apply_op' y (log, tree) \<bind> apply_op' x\<close>
    by (clarsimp simp: apply_op'_def) fastforce
qed
  
lemma concurrent_operations_commute:
  assumes \<open>xs prefix of i\<close>
  shows \<open>hb.concurrent_ops_commute (node_deliver_messages xs)\<close>
  using assms by (clarsimp simp add: hb.concurrent_ops_commute_def) (unfold interp_msg_def; simp)

corollary apply_operations_Snoc2:
  \<open>hb.apply_operations (xs @ [x]) s = (hb.apply_operations xs \<rhd> interp_msg x) s\<close>
  using hb.apply_operations_Snoc by auto

lemma unique_parent_empty[simp]:
  shows \<open>unique_parent {}\<close>
  by (auto simp: unique_parent_def)

lemma log_tree_invariant:
  assumes \<open>xs prefix of i\<close>  \<open>apply_operations xs = Some (log, tree)\<close>
  shows   \<open>distinct (map log_time log) \<and> unique_parent tree\<close>
using assms proof (induct xs arbitrary: log tree rule: rev_induct, clarsimp)
  case (snoc x xs)
  hence \<open>apply_operations xs \<noteq> None\<close>
    by (case_tac x; clarsimp simp: apply_operations_def node_deliver_messages_append kleisli_def)
       (metis (no_types, hide_lams) bind_eq_Some_conv surj_pair)
  then obtain log1 tree1 where *: \<open>apply_operations xs = Some (log1, tree1)\<close>
    by auto
  moreover have \<open>xs prefix of i\<close>
    using snoc.prems(1) by blast
  ultimately have **: \<open>distinct (map log_time log1)\<close> \<open>unique_parent tree1\<close>
    using snoc.hyps by blast+
  show ?case
  proof (case_tac x)
    fix m assume \<open>x = Broadcast m\<close>
    hence \<open>apply_operations (xs @ [x]) = apply_operations xs\<close>
      by simp
    thus \<open>distinct (map log_time log) \<and> unique_parent tree\<close>
      using \<open>xs prefix of i\<close> snoc.hyps snoc.prems(2) by presburger
  next
    fix m assume 1: \<open>x = Deliver m\<close>
    obtain t oper where 2: "m = (t, oper)"
      by force
    hence \<open>interp_msg (t, oper) (log1, tree1) = Some (log, tree)\<close>
      using \<open>apply_operations xs = Some (log1, tree1)\<close> snoc.prems(2) 1 2 by simp
    hence 4: \<open>apply_op' oper (log1, tree1) = Some (log, tree)\<close>
      by (clarsimp simp: interp_msg_def apply_op'_def)
    hence \<open>distinct ((map log_time log1) @ [move_time oper])\<close>
      by (clarsimp simp: apply_op'_def) (meson option.distinct(1))
    moreover hence 5: \<open>apply_op oper (log1, tree1) = (log, tree)\<close>
      using 4 ** by (clarsimp simp: apply_op'_def)
    ultimately have \<open>distinct (map log_time log)\<close>
      by (case_tac oper, clarsimp) (rule apply_op_timestampI1, assumption, clarsimp)
    thus \<open>distinct (map log_time log) \<and> unique_parent tree\<close>
      using ** 5 apply_op_unique_parent by blast
  qed
qed

definition indices :: "('id \<times> ('id, 'v, 'm) operation) event list \<Rightarrow> 'id list" where
  \<open>indices xs \<equiv> List.map_filter (\<lambda>x. case x of Deliver (i, _) \<Rightarrow> Some i | _ \<Rightarrow> None) xs\<close>

lemma indices_Nil [simp]:
  shows \<open>indices [] = []\<close>
by(auto simp: indices_def map_filter_def)

lemma indices_append [simp]:
  shows \<open>indices (xs@ys) = indices xs @ indices ys\<close>
by(auto simp: indices_def map_filter_def)

lemma indices_Broadcast_singleton [simp]:
  shows \<open>indices [Broadcast b] = []\<close>
by(auto simp: indices_def map_filter_def)

lemma indices_Deliver_Insert [simp]:
  shows \<open>indices [Deliver (i, x)] = [i]\<close>
  by(auto simp: indices_def map_filter_def)

lemma idx_in_elem[intro]:
  assumes \<open>Deliver (i, x) \<in> set xs\<close>
  shows   \<open>i \<in> set (indices xs)\<close>
using assms by(induction xs, auto simp add: indices_def map_filter_def)

lemma valid_move_oper_delivered:
  assumes \<open>xs@[Deliver (t, oper)] prefix of i\<close>
  shows   \<open>move_time oper = t\<close>
by (metis assms deliver_in_prefix_is_valid in_set_conv_decomp operation.set_cases(1) operation.set_sel(1) valid_move_opers.simps)

find_theorems "apply_operations (?xs @ [?x])"

lemma apply_opers_idx_elems:
  assumes \<open>xs prefix of i\<close> \<open>apply_operations xs = Some (log, tree)\<close>
  shows   \<open>set (map log_time log) = set (indices xs)\<close>
using assms proof (induction xs arbitrary: log tree rule: rev_induct, force)
  case (snoc x xs)
  moreover have prefix: \<open>xs prefix of i\<close>
    using snoc by force
  ultimately show ?case
  proof (cases x, force)
    case (Deliver m)
    then obtain t oper where m: \<open>m = (t, oper)\<close>
      by fastforce
    from Deliver and snoc show ?thesis
    proof (cases \<open>apply_operations xs\<close>, force)
      case (Some st)
      then obtain log' tree' where st: \<open>st = (log', tree')\<close>
        by (meson surj_pair)
      have set_indices: \<open>log_time ` set log' = set (indices xs)\<close>
        using Some prefix snoc.IH st by auto
      hence *:\<open>unique_parent tree' \<and> distinct (map log_time log')\<close>
        using st Some prefix by (simp add: log_tree_invariant)
      hence **: \<open>apply_operations (xs @ [x]) =
             (if move_time oper \<notin> set (indices xs) then Some (apply_op (snd (t, oper)) (log', tree'))
             else None)\<close>
        using Deliver Some st m set_indices by (auto simp: interp_msg_def apply_op'_def)
      hence ***: \<open>move_time oper \<notin> set (indices xs)\<close>
        using snoc.prems(2) by auto
      obtain t' p m c where oper: \<open>oper = Move t' p m c\<close>
        using operation.exhaust by blast
      hence \<open>t = t'\<close>
        using valid_move_oper_delivered Deliver m snoc.prems(1) by fastforce
      hence \<open>apply_op (Move t p m c) (log', tree') = (log, tree)\<close>
        by (metis ** oper option.discI option.simps(1) prod.sel(2) snoc.prems(2))
      hence \<open>set (map log_time log) = {t} \<union> set (map log_time log')\<close>
        apply (rule apply_op_timestampI2)
        using Deliver * *** m set_indices snoc.prems(1) valid_move_oper_delivered by auto
      thus ?thesis
        using Deliver m set_indices by (clarsimp simp: interp_msg_def apply_op'_def)
    qed
  qed                                
qed

lemma indices_distinct_aux:
  assumes \<open>xs @ [Deliver (a, b)] prefix of i\<close>
    shows \<open>a \<notin> set (indices xs)\<close>
proof 
  have 1: \<open>xs prefix of i\<close>
    using assms by force
  assume \<open>a \<in> set (indices xs)\<close>
  hence \<open>\<exists>x. Deliver (a, x) \<in> set xs\<close>
    by (clarsimp simp: indices_def map_filter_def, case_tac x; force)
  then obtain c where 2: \<open>Deliver (a, c) \<in> set xs\<close>
    by auto
  moreover then obtain j where \<open>Broadcast (a, c) \<in> set (history j)\<close>
    using 1 delivery_has_a_cause prefix_elem_to_carriers by blast
  moreover obtain k where \<open>Broadcast (a, b) \<in> set (history k)\<close>
    by (meson assms delivery_has_a_cause in_set_conv_decomp prefix_elem_to_carriers)
  ultimately have \<open>b = c\<close>
    by (metis fst_conv network.msg_id_unique network_axioms old.prod.inject)
  hence \<open>\<not> distinct (xs @ [Deliver (a, b)])\<close>
    by (simp add: 2)
  thus \<open>False\<close>
    using assms prefix_distinct by blast
qed


lemma indices_distinct:
  assumes \<open>xs prefix of i\<close>
  shows   \<open>distinct (indices xs)\<close>
using assms proof (induct xs rule: rev_induct, clarsimp)
  case (snoc x xs)
  hence \<open>xs prefix of i\<close>
    by force
  moreover hence \<open>distinct (indices xs)\<close>
    by (simp add: snoc.hyps)
  ultimately show ?case
    using indices_distinct_aux snoc.prems by (case_tac x; force)
qed

lemma log_time_invariant:
  assumes \<open>xs@[Deliver (t, oper)] prefix of i\<close>  \<open>apply_operations xs = Some (log, tree)\<close>
  shows   \<open>move_time oper \<notin> set (map log_time log)\<close>
proof -
  have \<open>xs prefix of i\<close>
    using assms by force
  have \<open>move_time oper = t\<close>
    using assms valid_move_oper_delivered by auto
  moreover have \<open>indices (xs @ [Deliver (t, oper)]) = indices xs @ [t]\<close>
    by simp
  moreover have \<open>distinct (indices (xs @ [Deliver (t, oper)]))\<close>
    using assms indices_distinct by blast
  ultimately show ?thesis
    using apply_opers_idx_elems assms indices_distinct_aux by blast
qed    

lemma apply_operations_never_fails:
  assumes \<open>xs prefix of i\<close>
  shows   \<open>apply_operations xs \<noteq> None\<close>
using assms proof(induct xs rule: rev_induct, clarsimp)
  case (snoc x xs)
  hence \<open>apply_operations xs \<noteq> None\<close>
    by blast
  then obtain log1 tree1 where *: \<open>apply_operations xs = Some (log1, tree1)\<close>
    by auto
  moreover hence \<open>distinct (map log_time log1) \<and> unique_parent tree1\<close>
    using log_tree_invariant snoc.prems by blast
  ultimately show ?case
    using log_time_invariant snoc.prems
    by (cases x; clarsimp simp: interp_msg_def) (clarsimp simp: apply_op'_def)
qed

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  \<open>\<lambda>os. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = os\<close> \<open>([], {})\<close>
proof (standard; clarsimp)
  fix xsa i
  assume \<open>xsa prefix of i\<close>
  thus \<open>hb.hb_consistent (node_deliver_messages xsa)\<close>
    by(auto simp add: hb_consistent_prefix)
next
  fix xsa i
  assume \<open>xsa prefix of i\<close>
  thus \<open>distinct (node_deliver_messages xsa)\<close>
    by(auto simp add: node_deliver_messages_distinct)
next
  fix xsa i
  assume \<open>xsa prefix of i\<close>
  thus \<open>hb.concurrent_ops_commute (node_deliver_messages xsa)\<close>
    by(auto simp add: concurrent_operations_commute)
next
  fix xs a b state xsa x
  assume \<open>hb.apply_operations xs ([], {}) = Some state\<close>
         \<open>node_deliver_messages xsa = xs @ [(a, b)]\<close>
         \<open>xsa prefix of x\<close>
  moreover hence \<open>apply_operations xsa \<noteq> None\<close>
    using apply_operations_never_fails by blast
  ultimately show \<open>\<exists>ab bb. interp_msg (a, b) state = Some (ab, bb)\<close>
    by (clarsimp simp: apply_operations_def kleisli_def)
next
  fix xs a b xsa x
  assume \<open>node_deliver_messages xsa = xs @ [(a, b)]\<close>
    and  \<open>xsa prefix of x\<close>
  thus \<open>\<exists>xsa. (\<exists>x. xsa prefix of x) \<and> node_deliver_messages xsa = xs\<close>
    using drop_last_message by blast
qed

end

end