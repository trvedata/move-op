theory Move_Acyclic
  imports Move
begin

inductive steps :: \<open>(('t, 'n, 'm) log_op list \<times> ('n \<times> 'm \<times> 'n) set) list \<Rightarrow> bool\<close> where
  \<open>\<lbrakk>do_op (oper, {}) = (logop, tree)\<rbrakk> \<Longrightarrow> steps [([logop], tree)]\<close> |
  \<open>\<lbrakk>steps (ss @ [(log, tree)]); do_op (oper, tree) = (logop, tree2)\<rbrakk> \<Longrightarrow> steps (ss @ [(log, tree), (logop # log, tree2)])\<close>

inductive_cases steps_indcases [elim]: \<open>steps ss\<close>
inductive_cases steps_singleton_indcases [elim]: \<open>steps [s]\<close>
inductive_cases steps_snoc_indcases [elim]: \<open>steps (ss@[s])\<close>

lemma steps_empty [elim]:
  assumes \<open>steps (ss @ [([], tree)])\<close>
  shows \<open>False\<close>
  using assms by force

lemma steps_snocI:
  assumes \<open>steps (ss @ [(log, tree)])\<close>
      and \<open>do_op (oper, tree) = (logop, tree2)\<close>
      and \<open>suf = [(log, tree), (logop # log, tree2)]\<close>
    shows \<open>steps (ss @ suf)\<close>
  using assms steps.intros(2) by blast

lemma steps'_unique_parent:
  assumes \<open>steps ss\<close>
  and \<open>ss = ss'@[(log, tree)]\<close>
  shows \<open>unique_parent tree\<close>
  using assms by(induction arbitrary: ss' log tree rule: steps.induct)
    (clarsimp, metis do_op_unique_parent emptyE operation.exhaust_sel unique_parentI)+

lemma apply_op_steps_exist:
  assumes \<open>apply_op oper (log1, tree1) = (log2, tree2)\<close>
    and \<open>steps (ss@[(log1, tree1)])\<close>
  shows \<open>\<exists>ss'. steps (ss'@[(log2,tree2)])\<close>
using assms proof(induction log1 arbitrary: tree1 log2 tree2 ss)
  case Nil
  thus ?case using steps_empty by blast
next
  case (Cons logop ops)
  then show ?case
  proof(cases \<open>move_time oper < log_time logop\<close>)
    case True
    hence \<open>apply_op oper (logop # ops, tree1) =
           redo_op logop (apply_op oper (ops, undo_op (logop, tree1)))\<close>
      by simp
    from this and Cons show ?thesis
      apply -
      apply(erule steps_snoc_indcases)
       apply(subgoal_tac \<open>logop = logopa \<and> ops = [] \<and> tree1 = tree\<close>)
        prefer 2 apply force
       apply(elim conjE, clarify)
       apply(subgoal_tac \<open>undo_op (logop, tree1) = {}\<close>)
      prefer 2 
        apply (metis apply_ops_Nil apply_ops_unique_parent do_op.cases do_undo_op_inv old.prod.inject)
      using True apply(clarsimp split!: prod.split_asm)
       apply(subgoal_tac \<open>steps ([([x1], x2)] @ [(log2, tree2)])\<close>)
        apply blast
       apply clarsimp
        apply(cases logop, clarsimp simp del: do_op.simps)
        apply(case_tac \<open>do_op (Move x1a x3 x4 x5, x2)\<close>)
      apply(subgoal_tac \<open>steps ([] @ [([x1], x2), (log2, tree2)])\<close>)
        apply force
       apply(rule steps_snocI)
      apply(clarsimp simp del: do_op.simps)
         apply(rule steps.intros(1))
         apply assumption back
        apply assumption
       apply force
      apply(rename_tac ss' log tree opera logopa tree2)
      apply(subgoal_tac "logop = logopa \<and> ops = log \<and> tree1 = tree2")
       apply(elim conjE, clarify)
       prefer 2 apply force
      apply(subgoal_tac \<open>undo_op (logop, tree1) = tree\<close>)
       prefer 2 using do_undo_op_inv steps'_unique_parent apply (metis operation.exhaust_sel)
      using True apply clarsimp
      apply(case_tac \<open>apply_op oper (ops, undo_op (logop, tree1))\<close>)
      apply clarsimp
      apply(erule_tac x=\<open>undo_op (logop, tree1)\<close> in meta_allE)
      apply(erule_tac x=a in meta_allE)
      apply(erule_tac x=b in meta_allE)
      apply(erule_tac x=ss' in meta_allE)
      apply clarsimp
      apply(rule_tac x=\<open>ss'a @ [(a, b)]\<close> in exI)
      apply clarsimp
        apply(cases logop, clarsimp simp del: do_op.simps split!: prod.split_asm)
      apply(rule steps_snocI, assumption, assumption, force)
      done
  next
    case False
    hence \<open>apply_op oper (logop # ops, tree1) =
           (let (op2, tree2) = do_op (oper, tree1) in (op2 # logop # ops, tree2))\<close>
      by simp
    then obtain logop2 where \<open>do_op (oper, tree1) = (logop2, tree2)\<close>
      by (metis (mono_tags, lifting) Cons.prems(1) case_prod_beta' prod.collapse snd_conv)
    hence \<open>steps (ss @ [(logop # ops, tree1), (logop2 # logop # ops, tree2)])\<close>
      using Cons.prems(2) steps_snocI by blast
    then show ?thesis
    proof -
      have "logop2 # logop # ops = log2"
        using Cons.prems(1) \<open>apply_op oper (logop # ops, tree1) = (let (op2, tree2) = do_op (oper, tree1) in (op2 # logop # ops, tree2))\<close> \<open>do_op (oper, tree1) = (logop2, tree2)\<close> by force
      then show ?thesis
        by (metis \<open>steps (ss @ [(logop # ops, tree1), (logop2 # logop # ops, tree2)])\<close> append.assoc append_Cons append_Nil)
    qed
  qed
qed

lemma steps_exist:
  fixes log :: \<open>('t::{linorder}, 'n, 'm) log_op list\<close>
  assumes \<open>apply_ops ops = (log, tree)\<close> and \<open>ops \<noteq> []\<close>
  shows \<open>\<exists>ss. steps ss \<and> last ss = (log, tree)\<close>
using assms proof(induction ops arbitrary: log tree rule: List.rev_induct, simp)
  case (snoc oper ops)
  then show ?case
  proof (cases ops)
    case Nil
    moreover obtain op2 tree2 where \<open>do_op (oper, {}) = (op2, tree2)\<close>
      by fastforce
    moreover have \<open>apply_ops (ops @ [oper]) = (let (op2, tree2) = do_op (oper, {}) in ([op2], tree2))\<close>
      by (metis apply_op.simps(1) apply_ops_Nil apply_ops_step calculation)
    moreover have \<open>log = [op2]\<close> \<open>tree = tree2\<close>
      using calculation(2) calculation(3) snoc.prems(1) by auto
    ultimately have \<open>steps [(log, tree)]\<close>
      using steps.simps  by auto
    then show ?thesis
      by force
  next
    case (Cons a list)
    obtain log1 tree1 where \<open>apply_ops ops = (log1, tree1)\<close>
      by fastforce
    moreover from this obtain ss :: \<open>(('t, 'n, 'm) log_op list \<times> ('n \<times> 'm \<times> 'n) set) list\<close>
        where \<open>steps ss \<and> (last ss) = (log1, tree1)\<close>
      using snoc.IH Cons by blast
    moreover have \<open>apply_op oper (log1, tree1) = (log, tree)\<close>
      using calculation(1) snoc.prems(1) by auto
    ultimately show ?thesis
      using apply_op_steps_exist snoc.prems(1)
      by (smt Nil_is_append_conv append_butlast_last_id last_snoc list.discI steps.simps)
  qed
qed

lemma steps_remove1:
  assumes \<open>steps (ss @ [s])\<close>
  shows \<open>steps ss \<or> ss = []\<close>
using assms steps.cases by fastforce

lemma steps_singleton:
  assumes \<open>steps [s]\<close>
  shows \<open>\<exists>oper. let (logop, tree) = do_op (oper, {}) in s = ([logop], tree)\<close>
  using assms apply - apply(erule steps_singleton_indcases)
  apply clarsimp
  apply (rule_tac x=oper in exI)
  apply force
  done

lemma steps_acyclic:
  assumes \<open>steps ss\<close>
  shows \<open>acyclic (snd (last ss))\<close>
  using assms apply (induction rule: steps.induct)
   apply clarsimp
   apply (metis acyclic_empty do_op_acyclic operation.exhaust_sel)
  apply clarsimp
  using do_op_acyclic_var by auto

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
  then obtain ss :: \<open>(('t, 'n, 'm) log_op list \<times> ('n \<times> 'm \<times> 'n) set) list\<close>
      where \<open>steps ss \<and> snd (last ss) = tree\<close>
    using assms steps_exist
    by (metis snd_conv)
  then show \<open>acyclic tree\<close>
    using steps_acyclic by blast
qed

end