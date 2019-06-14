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

lemma steps_unique_parent:
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
  { assume \<open>move_time oper < log_time logop\<close>
    hence *:\<open>apply_op oper (logop # ops, tree1) =
            redo_op logop (apply_op oper (ops, undo_op (logop, tree1)))\<close>
      by simp
    moreover {
      fix oper'
      assume asm: \<open>do_op (oper', {}) = (logop, tree1)\<close> \<open>ss = []\<close> \<open>(logop # ops, tree1) = ([logop], tree1)\<close>
      hence undo: \<open>undo_op (logop, tree1) = {}\<close>
        using asm Cons by (metis apply_ops_Nil apply_ops_unique_parent do_op.cases do_undo_op_inv old.prod.inject)
      obtain t oldp p m c where logmove: \<open>logop = LogMove t oldp p m c\<close>
        using log_op.exhaust by blast
      obtain logop'' tree'' where do: \<open>do_op (oper, {}) = (logop'', tree'')\<close>
        by fastforce
      hence redo: \<open>redo_op logop ([logop''], tree'') = (log2, tree2)\<close>
        using Cons.prems(1) asm undo calculation by auto
      then obtain op2 where op2: \<open>do_op (Move t p m c, tree'') = (op2, tree2)\<close>
        by (simp add: logmove)
      hence log2: \<open>log2 = op2 # [logop'']\<close>
        using logmove redo by auto
      have \<open>steps ([] @ [([logop''], tree''), (op2 #  [logop''], tree2)])\<close>
        using do op2 by (fastforce intro: steps.intros)
      hence \<open>steps ([([logop''], tree'')] @ [(log2, tree2)])\<close>
        by (simp add: log2)
      hence \<open>\<exists>ss'. steps (ss' @ [(log2, tree2)])\<close>
        by fastforce
    } moreover {
      fix pre_ss tree' oper'
      assume asm: \<open>steps (pre_ss @ [(ops, tree')])\<close>
                  \<open>do_op (oper', tree') = (logop, tree1)\<close>
                  \<open>ss = pre_ss @ [(ops, tree')]\<close>
      hence undo: \<open>undo_op (logop, tree1) = tree'\<close>
        using do_undo_op_inv_var steps_unique_parent by metis
      obtain log'' tree'' where apply_op: \<open>apply_op oper (ops, undo_op (logop, tree1)) = (log'', tree'')\<close>
        by (meson surj_pair)
      moreover have \<open>steps (pre_ss @ [(ops, undo_op (logop, tree1))])\<close>
        by (simp add: undo asm)
      ultimately obtain ss' where ss': \<open>steps (ss' @ [(log'', tree'')])\<close>
        using Cons.IH by blast
      obtain t oldp p m c where logmove: \<open>logop = LogMove t oldp p m c\<close>
        using log_op.exhaust by blast
      hence redo: \<open>redo_op logop (log'', tree'') = (log2, tree2)\<close>
        using Cons.prems(1) * apply_op by auto
      then obtain op2 where op2: \<open>do_op (Move t p m c, tree'') = (op2, tree2)\<close>
        using logmove redo by auto
      hence log2: \<open>log2 = op2 # log''\<close>
        using logmove redo by auto
      hence \<open>steps (ss' @ [(log'', tree''), (op2 # log'', tree2)])\<close>
        using ss' op2 by (fastforce intro!: steps.intros)
      hence \<open>steps ((ss' @ [(log'', tree'')]) @ [(log2, tree2)])\<close>
        by (simp add: log2)
      hence \<open>\<exists>ss'. steps (ss' @ [(log2, tree2)])\<close>
        by blast
    } ultimately have \<open>\<exists>ss'. steps (ss' @ [(log2, tree2)])\<close>
      using Cons by auto
  } moreover {
    assume \<open>\<not> (move_time oper < log_time logop)\<close>
    hence \<open>apply_op oper (logop # ops, tree1) =
           (let (op2, tree2) = do_op (oper, tree1) in (op2 # logop # ops, tree2))\<close>
      by simp
    moreover then obtain logop2 where \<open>do_op (oper, tree1) = (logop2, tree2)\<close>
      by (metis (mono_tags, lifting) Cons.prems(1) case_prod_beta' prod.collapse snd_conv)
    moreover hence \<open>steps (ss @ [(logop # ops, tree1), (logop2 # logop # ops, tree2)])\<close>
      using Cons.prems(2) steps_snocI by blast
    ultimately have \<open>\<exists>ss'. steps (ss' @ [(log2, tree2)])\<close>
      using Cons by (metis (mono_tags) Cons_eq_appendI append_eq_appendI append_self_conv2 insert_Nil
          prod.sel(1) prod.sel(2) rotate1.simps(2) split_beta)
  } ultimately show ?case
    by auto
qed


lemma last_helper:
  assumes \<open>last xs = x\<close> \<open>xs \<noteq> []\<close>
  shows   \<open>\<exists>pre. xs = pre @ [x]\<close>
  using assms by (induction xs arbitrary: x rule: rev_induct; simp)

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
    moreover from this obtain ss where \<open>steps ss \<and> (last ss) = (log1, tree1) \<and> ss \<noteq> []\<close>
      using snoc.IH Cons by blast
    moreover then obtain pre_ss where \<open>steps (pre_ss @ [(log1, tree1)]) \<close>
      using last_helper by fastforce
    moreover have \<open>apply_op oper (log1, tree1) = (log, tree)\<close>
      using calculation(1) snoc.prems(1) by auto
    ultimately obtain ss' where \<open>steps (ss' @ [(log, tree)])\<close>
      using apply_op_steps_exist by blast
    then show ?thesis
      by force
  qed
qed

lemma steps_remove1:
  assumes \<open>steps (ss @ [s])\<close>
  shows \<open>steps ss \<or> ss = []\<close>
using assms steps.cases by fastforce

lemma steps_singleton:
  assumes \<open>steps [s]\<close>
  shows \<open>\<exists>oper. let (logop, tree) = do_op (oper, {}) in s = ([logop], tree)\<close>
  using assms steps_singleton_indcases
  by (metis (mono_tags, lifting) case_prodI)

lemma steps_acyclic:
  assumes \<open>steps ss\<close>
  shows \<open>acyclic (snd (last ss))\<close>
  using assms apply (induction rule: steps.induct; clarsimp)
   apply (metis acyclic_empty do_op_acyclic operation.exhaust_sel)
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