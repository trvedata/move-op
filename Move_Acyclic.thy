theory Move_Acyclic
  imports Move
begin

inductive steps :: \<open>(('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set) list \<Rightarrow> bool\<close> where
  \<open>steps [do_op (oper, {})]\<close> |
  \<open>\<lbrakk>steps (ss @ [(logop, tree)])\<rbrakk> \<Longrightarrow> steps (ss @ [(logop, tree), do_op (oper, tree)])\<close>

inductive_cases steps_indcases: \<open>steps ss\<close>

lemma apply_op_steps_exist:
  assumes \<open>apply_op oper (log1, tree1) = (log2, tree2)\<close>
    and \<open>steps ss\<close> and \<open>snd (last ss) = tree1\<close>
  shows \<open>\<exists>ss'. steps ss' \<and> snd (last ss') = tree2\<close>
  sorry

lemma steps_exist:
  assumes \<open>apply_ops ops = (log, tree)\<close> and \<open>ops \<noteq> []\<close>
  shows \<open>\<exists>ss. steps ss \<and> snd (last ss) = tree\<close>
using assms proof(induction ops arbitrary: log tree rule: List.rev_induct, simp)
  case (snoc oper ops)
  then show ?case
  proof(cases \<open>ops = []\<close>)
    case True
    hence \<open>apply_ops (ops @ [oper]) =
           (let (op2, tree2) = do_op (oper, {}) in ([op2], tree2))\<close>
      by (metis apply_op.simps(1) apply_ops_Nil apply_ops_step)
    moreover from this have \<open>snd (do_op (oper, {})) = tree\<close>
      by (metis (no_types, lifting) snd_conv snoc.prems(1) split_beta)
    moreover have \<open>steps [do_op (oper, {})]\<close>
      by (simp add: steps.intros(1))
    ultimately show \<open>\<exists>ss. steps ss \<and> snd (last ss) = tree\<close>
      sorry (* why won't this go through? seems obvious *)
  next
    case False
    obtain log1 tree1 where \<open>apply_ops ops = (log1, tree1)\<close>
      by fastforce
    moreover from this obtain ss where \<open>steps ss \<and> snd (last ss) = tree1\<close>
      using snoc.IH False sorry
    ultimately show \<open>\<exists>ss. steps ss \<and> snd (last ss) = tree\<close>
      using apply_op_steps_exist snoc.prems(1) by fastforce
  qed
qed

lemma steps_remove1:
  assumes \<open>steps (ss @ [s])\<close>
  shows \<open>steps ss \<or> ss = []\<close>
using assms steps.cases by fastforce

lemma steps_singleton:
  assumes \<open>steps [s]\<close>
  shows \<open>\<exists>oper. s = do_op (oper, {})\<close>
using assms steps.cases by fastforce

lemma steps_oper:
  assumes \<open>steps (ss @ [(logop, tree), s])\<close>
  shows \<open>\<exists>oper. s = do_op (oper, tree)\<close>
using assms steps.cases by fastforce

lemma steps_acyclic:
  assumes \<open>steps ss\<close>
  shows \<open>acyclic (snd (last ss))\<close>
using assms proof(induction ss rule: List.rev_induct)
  case Nil
  then show ?case using steps.cases by auto
next
  case (snoc s ss)
  then show ?case
  proof(cases \<open>ss = []\<close>)
    case True
    then obtain oper where do_op: \<open>s = do_op (oper, {})\<close>
      by (metis append_Nil snoc.prems steps_singleton)
    hence \<open>acyclic (snd s)\<close>
      by (metis Move.acyclic_def ancestor_empty_False do_op_acyclic eq_snd_iff operation.exhaust_sel)
    then show \<open>acyclic (snd (last (ss @ [s])))\<close>
      by simp
  next
    case False
    hence \<open>acyclic (snd (last ss))\<close>
      using snoc.IH snoc.prems steps_remove1 by blast
    moreover obtain ss' logop tree where \<open>ss = ss' @ [(logop, tree)]\<close>
      using False snoc.prems steps.cases by fastforce
    moreover from this obtain oper where \<open>s = do_op (oper, tree)\<close>
      by (metis append.assoc append_Cons append_Nil snoc.prems steps_oper)
    ultimately show \<open>acyclic (snd (last (ss @ [s])))\<close>
      by (metis do_op_acyclic last.simps last_appendR not_Cons_self
          operation.exhaust_sel prod.exhaust_sel snd_conv)
  qed
qed

theorem apply_ops_acyclic:
  assumes \<open>apply_ops ops = (log, tree)\<close>
  shows \<open>acyclic tree\<close>
proof(cases \<open>ops = []\<close>)
  case True
  then show \<open>acyclic tree\<close>
    using acyclic_def assms by fastforce
next
  case False
  then obtain ss where \<open>steps ss \<and> snd (last ss) = tree\<close>
    using assms steps_exist by blast
  then show \<open>acyclic tree\<close>
    using steps_acyclic by blast
qed

end