theory Move_SEC
  imports Move CRDT.Network
begin

definition interp_op' :: \<open>('t::{linorder}, 'n, 'm) operation \<Rightarrow> ('t, 'n, 'm) state \<rightharpoonup> ('t, 'n, 'm) state\<close> where
  \<open>interp_op' x s \<equiv> case s of (log, tree) \<Rightarrow>
    if unique_parent tree \<and> distinct (map log_time log @ [move_time x]) then
      Some (interp_op x s)
    else None\<close>

fun valid_move_opers :: "('t, 'n, 'm) state \<Rightarrow> 't \<times>('t, 'n, 'm) operation \<Rightarrow> bool" where
  \<open>valid_move_opers S (i, Move t _ _ _) = (t = i)\<close>

locale move = network_with_constrained_ops _ "interp_op'" "([], {})" valid_move_opers
begin


lemma kleisli_interp_op' [iff]:
  shows \<open>interp_op' (x :: ('t :: {linorder}, 'n, 'm) operation) \<rhd> interp_op' y = interp_op' y \<rhd> interp_op' x\<close>
proof (unfold kleisli_def, rule ext, clarify)
  fix log :: \<open>('t, 'n, 'm) log_op list\<close> and tree :: \<open>('n \<times> 'm \<times> 'n) set\<close>
  { assume \<open>unique_parent tree\<close> \<open>distinct (map log_time log @ [move_time x])\<close> \<open>distinct (map log_time log @ [move_time y])\<close>
    have \<open>interp_op' x (log, tree) \<bind> interp_op' y = interp_op' y (log, tree) \<bind> interp_op' x\<close>
      sorry
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
    by (clarsimp simp: interp_op'_def)

qed
(*
  apply(rule ext)
  apply clarify
  apply (case_tac \<open>unique_parent b \<and> distinct (map log_time a)\<close>)
   prefer 2
   apply force
  apply (case_tac \<open>distinct (map log_time a @ [move_time x, move_time y])\<close>)
   apply clarify
   apply (case_tac \<open>interp_op x (a, b)\<close>)
   apply (case_tac \<open>interp_op y (a, b)\<close>)
   apply (subgoal_tac \<open>unique_parent ba \<and> unique_parent bb\<close>)
  prefer 2
  using interp_op_unique_parent apply blast
  apply clarsimp
  apply (subgoal_tac \<open>distinct (map log_time aa) \<and>
                      distinct (map log_time ab)\<close>)
    prefer 2
    apply (rule conjI)
     apply (cases x)
     apply clarsimp
      apply (rule interp_op_timestampI1)
       prefer 2
       apply assumption
     apply force
     apply (cases y)
     apply clarsimp
      apply (rule interp_op_timestampI1)
       prefer 2
       apply assumption
    apply force
   apply clarsimp
   apply (case_tac \<open>move_time x \<notin> log_time ` set ab \<and> move_time y \<notin> log_time ` set aa\<close>)
    apply clarsimp
    apply (cases x, cases y)
  apply clarsimp
    apply (rule interp_op_commute2I)
       apply force
      apply force
     apply force
    apply force
  

*)

(*
lemma timestamps_distinct:
  assumes \<open>xs prefix of i\<close>
  and \<open>ops = node_deliver_messages xs\<close>
shows \<open>distinct (map (move_time \<circ> snd) ops)\<close>
  sorry*)

lemma kleisli_interp_op' [iff]:
  shows \<open>interp_op' x \<rhd> interp_op' y = interp_op' y \<rhd> interp_op' x\<close>  
  apply(unfold interp_op'_def kleisli_def)
  apply(rule ext)
  apply clarify
  apply (case_tac \<open>unique_parent b \<and> distinct (map log_time a)\<close>)
   prefer 2
   apply force
  apply (case_tac \<open>distinct (map log_time a @ [move_time x, move_time y])\<close>)
   apply clarify
   apply (case_tac \<open>interp_op x (a, b)\<close>)
   apply (case_tac \<open>interp_op y (a, b)\<close>)
   apply (subgoal_tac \<open>unique_parent ba \<and> unique_parent bb\<close>)
  prefer 2
  using interp_op_unique_parent apply blast
  apply clarsimp
  apply (subgoal_tac \<open>distinct (map log_time aa) \<and>
                      distinct (map log_time ab)\<close>)
    prefer 2
    apply (rule conjI)
     apply (cases x)
     apply clarsimp
      apply (rule interp_op_timestampI1)
       prefer 2
       apply assumption
     apply force
     apply (cases y)
     apply clarsimp
      apply (rule interp_op_timestampI1)
       prefer 2
       apply assumption
    apply force
   apply clarsimp
   apply (case_tac \<open>move_time x \<notin> log_time ` set ab \<and> move_time y \<notin> log_time ` set aa\<close>)
    apply clarsimp
    apply (cases x, cases y)
  apply clarsimp
    apply (rule interp_op_commute2I)
       apply force
      apply force
     apply force
    apply force
  


  

lemma concurrent_operations_commute:
  assumes \<open>xs prefix of i\<close>
  shows \<open>hb.concurrent_ops_commute (node_deliver_messages xs)\<close>
  using assms
  apply(clarsimp simp add: hb.concurrent_ops_commute_def)
  apply(unfold interp_msg_def; simp)
  prefer 2
  
  done

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>os. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = os" "([], {})"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix drop_last_message node_deliver_messages_distinct concurrent_operations_commute)
  apply(clarsimp simp add: interp_msg_def interp_op'_def)
  using drop_last_message apply blast
  done

end

end