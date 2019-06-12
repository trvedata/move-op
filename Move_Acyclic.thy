theory Move_Acyclic
  imports Move
begin

inductive steps :: \<open>(('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set) list \<Rightarrow> bool\<close> where
  \<open>steps [do_op (oper, {})]\<close> |
  \<open>\<lbrakk>steps (ss @ [(logop, tree)])\<rbrakk> \<Longrightarrow> steps (ss @ [(logop, tree), do_op (oper, tree)])\<close>

inductive_cases steps_indcases [elim]: \<open>steps ss\<close>

inductive steps' :: \<open>(('t, 'n, 'm) log_op list \<times> ('n \<times> 'm \<times> 'n) set) list \<Rightarrow> bool\<close> where
  \<open>\<lbrakk>do_op (oper, {}) = (logop, tree)\<rbrakk> \<Longrightarrow> steps' [([logop], tree)]\<close> |
  \<open>\<lbrakk>steps' (ss @ [(log, tree)]); do_op (oper, tree) = (logop, tree2)\<rbrakk> \<Longrightarrow> steps' (ss @ [(log, tree), (logop # log, tree2)])\<close>

inductive_cases steps'_indcases [elim]: \<open>steps' ss\<close>
inductive_cases steps'_snoc_indcases [elim]: \<open>steps' (ss@[s])\<close>

lemma steps'_empty:
  assumes \<open>steps' (ss @ [([], tree)])\<close>
  shows \<open>False\<close>
  using assms apply -
  apply(erule steps'_indcases)
   apply force+
  done

lemma
  assumes \<open>apply_op oper (log1, tree1) = (log2, tree2)\<close>
    and \<open>steps' (ss@[(log1, tree1)])\<close>
  shows \<open>\<exists>ss'. steps' (ss'@[(log2,tree2)])\<close>
using assms proof(induction log1 arbitrary: tree1 log2 tree2 ss)
  case Nil
  thus ?case using steps'_empty by blast
next
  case (Cons logop ops)
  then show ?case
    apply -
    apply(erule steps'_snoc_indcases)
     apply(clarsimp split!: if_split_asm prod.split_asm)
   
  proof(cases \<open>move_time oper < log_time logop\<close>)
    case True
    hence \<open>apply_op oper (logop # ops, tree1) =
           redo_op logop (apply_op oper (ops, undo_op (logop, tree1)))\<close>
      by simp
    then show ?thesis sorry
  next
    case False
    hence \<open>apply_op oper (logop # ops, tree1) =
           (let (op2, tree2) = do_op (oper, tree1) in (op2 # logop # ops, tree2))\<close>
      by simp
    then obtain logop2 where \<open>do_op (oper, tree1) = (logop2, tree2)\<close>
      by (metis (mono_tags, lifting) Cons.prems(1) case_prod_beta' prod.collapse snd_conv)
    hence \<open>steps' (ss @ [(logop # ops, tree1), (logop2 # logop # ops, tree2)])\<close>
      using Cons.prems(2) steps'.intros(2) by blast
    then show ?thesis
    proof -
      have "logop2 # logop # ops = log2"
        using Cons.prems(1) \<open>apply_op oper (logop # ops, tree1) = (let (op2, tree2) = do_op (oper, tree1) in (op2 # logop # ops, tree2))\<close> \<open>do_op (oper, tree1) = (logop2, tree2)\<close> by force
      then show ?thesis
        by (metis \<open>steps' (ss @ [(logop # ops, tree1), (logop2 # logop # ops, tree2)])\<close> append.assoc append_Cons append_Nil)
    qed
  qed
qed

(*
lemma apply_op_steps_exist:
  fixes log1 log2 :: \<open>('t::{linorder}, 'n, 'm) log_op list\<close> and ss :: \<open>(('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set) list\<close>
  assumes \<open>apply_op oper (log1, tree1) = (log2, tree2)\<close>
    and \<open>steps ss\<close> and \<open>snd (last ss) = tree1\<close>
    and \<open>log1 = [] \<longrightarrow> tree1 = {}\<close>
  shows \<open>\<exists>ss' :: (('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set) list. steps ss' \<and> snd (last ss') = tree2\<close>
using assms proof(induction log1 arbitrary: tree1 log2 tree2 ss)
  case Nil
  obtain t p m c where oper: \<open>oper = Move t p m c\<close>
    using operation.exhaust_sel by blast
  hence \<open>apply_op oper ([], tree1) =
         (let (op2, tree2) = do_op (oper, {}) in ([op2], tree2))\<close>
    using Nil by simp
  from this have \<open>do_op (oper, {}) = (LogMove t (get_parent tree1 c) p m c, tree2)\<close>
    using Nil oper by auto
  hence \<open>steps [do_op (oper, {})] \<and> snd (last [do_op (oper, {})]) = tree2\<close>
    using steps.intros(1) by (metis last.simps snd_conv)
  thus ?case
    by blast
next
  case (Cons logop ops)
  then show ?case
  proof(cases \<open>move_time oper < log_time logop\<close>)
    case True
    hence \<open>apply_op oper (logop # ops, tree1) =
           redo_op logop (apply_op oper (ops, undo_op (logop, tree1)))\<close>
      by simp
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed
*)

lemma steps_exist:
  fixes log :: \<open>('t::{linorder}, 'n, 'm) log_op list\<close>
  assumes \<open>apply_ops ops = (log, tree)\<close> and \<open>ops \<noteq> []\<close>
  shows \<open>\<exists>ss :: (('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set) list. steps ss \<and> snd (last ss) = tree\<close>
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
    ultimately show ?thesis
      by force
  next
    case False
    obtain log1 tree1 where \<open>apply_ops ops = (log1, tree1)\<close>
      by fastforce
    moreover from this obtain ss :: \<open>(('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set) list\<close>
        where \<open>steps ss \<and> snd (last ss) = tree1\<close>
      using snoc.IH False by blast
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
  fixes ops :: \<open>('t::{linorder}, 'n, 'm) operation list\<close>
  assumes \<open>apply_ops ops = (log, tree)\<close>
  shows \<open>acyclic tree\<close>
proof(cases \<open>ops = []\<close>)
  case True
  then show \<open>acyclic tree\<close>
    using acyclic_def assms by fastforce
next
  case False
  then obtain ss :: \<open>(('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set) list\<close>
      where \<open>steps ss \<and> snd (last ss) = tree\<close>
    using assms steps_exist by blast
  then show \<open>acyclic tree\<close>
    using steps_acyclic by blast
qed

end