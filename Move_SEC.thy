theory Move_SEC
  imports Move CRDT.Network
begin

definition interp_op' :: \<open>('a::{linorder}, 'b) operation \<Rightarrow> ('a, 'b) state \<rightharpoonup> ('a, 'b) state\<close> where
  \<open>interp_op' x s \<equiv> Some (interp_op x s)\<close>

fun valid_move_opers :: "('b, 'c) state \<Rightarrow> 'b \<times> ('b, 'c) operation \<Rightarrow> bool" where
  \<open>valid_move_opers S (i, Move t p c) = (t = i)\<close>

locale move = network_with_constrained_ops _ "interp_op'" "([], {})" valid_move_opers
begin

lemma timestamps_distinct:
  assumes \<open>xs prefix of i\<close>
  and \<open>ops = node_deliver_messages xs\<close>
shows \<open>distinct (map (move_time \<circ> snd) ops)\<close>
  sorry

lemma kleisli_interp_op' [iff]:
  shows \<open>interp_op' x \<rhd> interp_op' y = interp_op' y \<rhd> interp_op' x\<close>
  apply(clarsimp simp add: interp_op'_def kleisli_def)
  apply(rule ext)
  

lemma concurrent_operations_commute:
  assumes \<open>xs prefix of i\<close>
  shows \<open>hb.concurrent_ops_commute (node_deliver_messages xs)\<close>
  using assms
  apply(clarsimp simp add: hb.concurrent_ops_commute_def)
  apply(unfold interp_msg_def; simp)
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