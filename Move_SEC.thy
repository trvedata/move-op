theory Move_SEC
  imports Move CRDT.Network
begin

definition interp_op' :: \<open>('t::{linorder}, 'n, 'm) operation \<Rightarrow> ('t, 'n, 'm) state \<rightharpoonup> ('t, 'n, 'm) state\<close> where
  \<open>interp_op' x s \<equiv> case s of (log, tree) \<Rightarrow>
    if unique_parent tree \<and> distinct (map log_time log @ [move_time x]) then
      Some (interp_op x s)
    else None\<close>

fun valid_move_opers :: "('t, 'n, 'm) state \<Rightarrow> 't \<times>('t, 'n, 'm) operation \<Rightarrow> bool" where
  \<open>valid_move_opers (log, _) (_, Move t _ _ _) = (t \<notin> set (map log_time log))\<close>

locale move = network_with_constrained_ops _ "interp_op'" "([], {})" valid_move_opers
begin

lemma kleisli_interp_op' [iff]:
  shows \<open>interp_op' (x :: ('t :: {linorder}, 'n, 'm) operation) \<rhd> interp_op' y = interp_op' y \<rhd> interp_op' x\<close>
proof (unfold kleisli_def, rule ext, clarify)
  fix log :: \<open>('t, 'n, 'm) log_op list\<close> and tree :: \<open>('n \<times> 'm \<times> 'n) set\<close>
  { assume *: \<open>unique_parent tree\<close> \<open>distinct (map log_time log @ [move_time x])\<close> \<open>distinct (map log_time log @ [move_time y])\<close> \<open>move_time x \<noteq> move_time y\<close>
    obtain logx treex where 1: \<open>interp_op x (log, tree) = (logx, treex)\<close>
      using * by (clarsimp simp: interp_op'_def)  (metis surj_pair)
    hence \<open>set (map log_time logx) = {move_time x} \<union> set (map log_time log)\<close>
      using * by (cases x) (rule interp_op_timestampI2; force)
    moreover have \<open>distinct (map log_time logx)\<close>
      using * 1 by (cases x) (rule interp_op_timestampI1; force)
    ultimately have 2: \<open>distinct (map log_time logx @ [move_time y])\<close>
      using * by simp
    obtain logy treey where 3: \<open>interp_op y (log, tree) = (logy, treey)\<close>
      using * by (clarsimp simp: interp_op'_def)  (metis surj_pair)
    hence \<open>set (map log_time logy) = {move_time y} \<union> set (map log_time log)\<close>
      using * by (cases y) (rule interp_op_timestampI2; force)
    moreover have \<open>distinct (map log_time logy)\<close>
      using * 3 by (cases y) (rule interp_op_timestampI1, force, force)
    ultimately have 4: \<open>distinct (map log_time logy @ [move_time x])\<close>
      using * by simp
    have \<open>unique_parent treex\<close> \<open>unique_parent treey\<close>
      using * 1 3 interp_op_unique_parent by blast+
    hence \<open>interp_op' x (log, tree) \<bind> interp_op' y = interp_op' y (log, tree) \<bind> interp_op' x\<close>
      using * 1 2 3 4 by (cases x, cases y, clarsimp simp: interp_op'_def) (rule interp_op_commute2I; force)
  }
  moreover {
    assume *: \<open>unique_parent tree\<close> \<open>distinct (map log_time log @ [move_time x])\<close> \<open>distinct (map log_time log @ [move_time y])\<close> \<open>move_time x = move_time y\<close>
    obtain logx treex where 1: \<open>interp_op x (log, tree) = (logx, treex)\<close>
      using * by (clarsimp simp: interp_op'_def)  (metis surj_pair)
    hence \<open>set (map log_time logx) = {move_time x} \<union> set (map log_time log)\<close>
      using * by (cases x) (rule interp_op_timestampI2; force)
    hence 2: \<open>\<not> distinct (map log_time logx @ [move_time y])\<close>
      using * by simp
    obtain logy treey where 3: \<open>interp_op y (log, tree) = (logy, treey)\<close>
      using * by (clarsimp simp: interp_op'_def)  (metis surj_pair)
    hence \<open> set (map log_time logy) = {move_time y} \<union> set (map log_time log)\<close>
      using * by (cases y) (rule interp_op_timestampI2; force)
    hence 4: \<open>\<not> distinct (map log_time logy @ [move_time x])\<close>
      using * by simp
    have \<open>interp_op' x (log, tree) \<bind> interp_op' y = interp_op' y (log, tree) \<bind> interp_op' x\<close>
      using * 1 2 3 4 by (clarsimp simp: interp_op'_def)
  }
  moreover {
    assume *: \<open>unique_parent tree\<close> \<open>\<not> distinct (map log_time log @ [move_time x])\<close> \<open>distinct (map log_time log @ [move_time y])\<close>
    then have **: \<open>move_time x \<in> set (map log_time log)\<close>
      by auto 
    obtain log1 tree1 where \<open>interp_op y (log, tree) = (log1, tree1)\<close>
      using * by (clarsimp simp: interp_op'_def)  (metis surj_pair)
    moreover hence \<open> set (map log_time log1) = {move_time y} \<union> set (map log_time log)\<close>
      using * by (cases y) (rule interp_op_timestampI2; force)
    hence \<open>move_time x \<in> set (map log_time log1)\<close>
      using ** by blast
    moreover hence \<open>\<not> distinct (map log_time log1 @ [move_time x])\<close>
      by simp
    ultimately have \<open>interp_op' x (log, tree) \<bind> interp_op' y = interp_op' y (log, tree) \<bind> interp_op' x\<close>
      using * by (clarsimp simp: interp_op'_def)
  }
  moreover {
    assume *: \<open>unique_parent tree\<close> \<open>distinct (map log_time log @ [move_time x])\<close> \<open>\<not> distinct (map log_time log @ [move_time y])\<close>
    then have **: \<open>move_time y \<in> set (map log_time log)\<close>
      by auto 
    obtain log1 tree1 where \<open>interp_op x (log, tree) = (log1, tree1)\<close>
      using * by (clarsimp simp: interp_op'_def)  (metis surj_pair)
    moreover hence \<open> set (map log_time log1) = {move_time x} \<union> set (map log_time log)\<close>
      using * by (cases x) (rule interp_op_timestampI2; force)
    hence \<open>move_time y \<in> set (map log_time log1)\<close>
      using ** by blast
    moreover hence \<open>\<not> distinct (map log_time log1 @ [move_time y])\<close>
      by simp
    ultimately have \<open>interp_op' x (log, tree) \<bind> interp_op' y = interp_op' y (log, tree) \<bind> interp_op' x\<close>
      using * by (clarsimp simp: interp_op'_def)
  }
  ultimately show \<open>interp_op' x (log, tree) \<bind> interp_op' y = interp_op' y (log, tree) \<bind> interp_op' x\<close>
    by (clarsimp simp: interp_op'_def) fastforce
qed
  
lemma concurrent_operations_commute:
  assumes \<open>xs prefix of i\<close>
  shows \<open>hb.concurrent_ops_commute (node_deliver_messages xs)\<close>
  using assms by (clarsimp simp add: hb.concurrent_ops_commute_def) (unfold interp_msg_def; simp)

corollary apply_operations_Snoc2:
  "hb.apply_operations (xs @ [x]) s = (hb.apply_operations xs \<rhd> interp_msg x) s"
  using hb.apply_operations_Snoc by auto

lemma unique_parent_empty[simp]:
  shows "unique_parent {}"
  by (auto simp: unique_parent_def)

lemma log_tree_invariant:
  assumes "xs prefix of i"  "apply_operations xs = Some (log, tree)"
  shows   "distinct (map log_time log) \<and> unique_parent tree"
using assms proof (induct xs arbitrary: log tree rule: rev_induct, clarsimp)
  case (snoc x xs)
  hence "apply_operations xs \<noteq> None"
    by (case_tac x; clarsimp simp: apply_operations_def node_deliver_messages_append kleisli_def)
       (metis (no_types, hide_lams) bind_eq_Some_conv surj_pair)
  then obtain log1 tree1 where *: "apply_operations xs = Some (log1, tree1)"
    by auto
  moreover have "xs prefix of i"
    using snoc.prems(1) by blast
  ultimately have **: "distinct (map log_time log1)" "unique_parent tree1"
    using snoc.hyps by blast+
  show ?case
  proof (case_tac x)
    fix m assume "x = Broadcast m"
    hence "apply_operations (xs @ [x]) = apply_operations xs"
      by simp
    thus "distinct (map log_time log) \<and> unique_parent tree"
      using \<open>xs prefix of i\<close> snoc.hyps snoc.prems(2) by presburger
  next
    fix m assume 1: "x = Deliver m"
    obtain t oper where 2: "m = (t, oper)"
      by force
    hence "interp_msg (t, oper) (log1, tree1) = Some (log, tree)"
      using \<open>apply_operations xs = Some (log1, tree1)\<close> snoc.prems(2) 1 2 by simp
    hence 4: "interp_op' oper (log1, tree1) = Some (log, tree)"
      by (clarsimp simp: interp_msg_def interp_op'_def)
    hence "distinct ((map log_time log1) @ [move_time oper])"
      by (clarsimp simp: interp_op'_def) (meson option.distinct(1))
    moreover hence 5: "interp_op oper (log1, tree1) = (log, tree)"
      using 4 ** by (clarsimp simp: interp_op'_def)
    ultimately have "distinct (map log_time log)"
      apply (case_tac oper, clarsimp)
      apply (rule interp_op_timestampI1, assumption)
      by (clarsimp simp add: \<open>distinct (map log_time log1)\<close>)
    thus "distinct (map log_time log) \<and> unique_parent tree"
      using ** 5 interp_op_unique_parent by blast
  qed
qed


lemma log_time_invariant:
  assumes "xs@[Deliver (t, oper)] prefix of i"  "apply_operations xs = Some (log, tree)"
  shows   "move_time oper \<notin> set (map log_time log)"
  sorry

lemma apply_operations_never_fails:
  assumes "xs prefix of i"
  shows "apply_operations xs \<noteq> None"
using assms proof(induct xs rule: rev_induct, clarsimp)
  case (snoc x xs)
  hence "apply_operations xs \<noteq> None"
    by blast
  then obtain log1 tree1 where *: "apply_operations xs = Some (log1, tree1)"
    by auto
  moreover hence "distinct (map log_time log1) \<and> unique_parent tree1"
    using log_tree_invariant snoc.prems by blast
  ultimately show ?case
    using log_time_invariant snoc.prems
    by (cases x; clarsimp simp: interp_msg_def) (clarsimp simp: interp_op'_def)
qed

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>os. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = os" "([], {})"
proof (standard; clarsimp)
  fix xsa i
  assume "xsa prefix of i"
  thus "hb.hb_consistent (node_deliver_messages xsa)"
    by(auto simp add: hb_consistent_prefix)
next
  fix xsa i
  assume "xsa prefix of i"
  thus "distinct (node_deliver_messages xsa)"
    by(auto simp add: node_deliver_messages_distinct)
next
  fix xsa i
  assume "xsa prefix of i"
  thus "hb.concurrent_ops_commute (node_deliver_messages xsa)"
    by(auto simp add: concurrent_operations_commute)
next
  fix xs a b state xsa x
  assume "hb.apply_operations xs ([], {}) = Some state"
         "node_deliver_messages xsa = xs @ [(a, b)]"
         "xsa prefix of x"
  moreover hence "apply_operations xsa \<noteq> None"
    using apply_operations_never_fails by blast
  ultimately show "\<exists>ab bb. interp_msg (a, b) state = Some (ab, bb)"
    by (clarsimp simp: apply_operations_def kleisli_def)
next
  fix xs a b xsa x
  assume "node_deliver_messages xsa = xs @ [(a, b)]"
    and "xsa prefix of x"
  thus "\<exists>xsa. (\<exists>x. xsa prefix of x) \<and> node_deliver_messages xsa = xs"
    using drop_last_message by blast
qed

end

end