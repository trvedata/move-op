theory Move_Acyclic
  imports Move
begin

section \<open>Tree invariant 2: no cycles\<close>

definition acyclic :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> bool\<close> where
  \<open>acyclic tree \<equiv> (\<nexists>n. ancestor tree n n)\<close>

lemma acyclic_empty [simp]: \<open>acyclic {}\<close>
  by (meson acyclic_def ancestor_indcases empty_iff)

lemma acyclicE [elim]:
  assumes \<open>acyclic \<T>\<close>
    and \<open>(\<nexists>n. ancestor \<T> n n) \<Longrightarrow> P\<close>
  shows \<open>P\<close>
  using assms by (auto simp add: acyclic_def)

lemma ancestor_empty_False [simp]:
  shows \<open>ancestor {} p c = False\<close>
  by (meson ancestor_indcases emptyE)

lemma ancestor_superset_closed:
  assumes \<open>ancestor \<T> p c\<close>
    and \<open>\<T> \<subseteq> \<S>\<close>
  shows \<open>ancestor \<S> p c\<close>
  using assms by (induction rule: ancestor.induct) (auto intro: ancestor.intros)

lemma acyclic_subset:
  assumes \<open>acyclic T\<close>
    and \<open>S \<subseteq> T\<close>
  shows \<open>acyclic S\<close>
  using assms ancestor_superset_closed by (metis acyclic_def)

inductive path :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n \<times> 'n) list \<Rightarrow> bool\<close> where
  \<open>\<lbrakk>(b, x, e) \<in> T\<rbrakk> \<Longrightarrow> path T b e [(b, e)]\<close> |
  \<open>\<lbrakk>path T b m xs; (m, e) \<notin> set xs; (m, x, e) \<in> T\<rbrakk> \<Longrightarrow> path T b e (xs @ [(m, e)])\<close>

inductive_cases path_indcases: \<open>path T b e xs\<close>

lemma empty_path:
  shows \<open>\<not> path T x y []\<close>
  using path_indcases by fastforce

lemma singleton_path:
  assumes \<open>path T b m [(p, c)]\<close>
  shows \<open>b = p \<and> m = c\<close>
  using assms by (metis (no_types, lifting) butlast.simps(2) butlast_snoc empty_path
    list.inject path.cases prod.inject)

lemma last_path:
  assumes \<open>path T b e (xs @ [(p, c)])\<close>
  shows \<open>e = c\<close>
  using assms path.cases by force

lemma path_drop1:
  assumes \<open>path T b e (xs @ [(a, e)])\<close>
    and \<open>xs \<noteq> []\<close>
  shows \<open>path T b a xs \<and> (a, e) \<notin> set xs\<close>
  using assms path.cases by force
  
lemma path_drop:
  assumes \<open>path T b e (xs @ ys)\<close>
    and \<open>xs \<noteq> []\<close>
  shows \<open>\<exists>m. path T b m xs\<close>
using assms proof(induction ys arbitrary: xs, force)
  case (Cons x ys)
  from this obtain m where IH: \<open>path T b m (xs @ [x])\<close>
    by fastforce
  moreover obtain a e where \<open>x = (a, e)\<close>
    by fastforce
  moreover from this have \<open>m = e\<close>
    using IH last_path by fastforce
  ultimately show ?case
    using Cons.prems(2) path_drop1 by fastforce
qed

lemma fst_path:
  assumes \<open>path T b e ((p, c) # xs)\<close>
  shows \<open>b = p\<close>
using assms proof(induction xs arbitrary: e rule: List.rev_induct)
  case Nil then show ?case
    by (simp add: singleton_path)
next
  case (snoc x xs)
  then show ?case
    by (metis append_Cons list.distinct(1) path_drop)
qed

lemma path_split:
  assumes \<open>path T m n xs\<close>
    and \<open>(p, c) \<in> set xs\<close>
  shows \<open>\<exists>ys zs. (ys = [] \<or> path T m p ys) \<and> (zs = [] \<or> path T c n zs) \<and>
                 (xs = ys @ [(p, c)] @ zs) \<and> (p, c) \<notin> set ys \<and> (p, c) \<notin> set zs\<close>
using assms proof(induction rule: path.induct, force)
  case step: (2 T b m xs e)
  then show ?case
  proof(cases \<open>(p, c) = (m, e)\<close>)
    case True
    then show ?thesis using step.hyps by force
  next
    case pc_xs: False (* (p, c) \<in> set xs *)
    then obtain ys zs where yszs: \<open>(ys = [] \<or> path T b p ys) \<and> (zs = [] \<or> path T c m zs) \<and>
        xs = ys @ [(p, c)] @ zs \<and> (p, c) \<notin> set ys \<and> (p, c) \<notin> set zs\<close>
      using step.IH step.prems by auto
    have path_zs: \<open>path T c e (zs @ [(m, e)])\<close>
      by (metis (no_types, lifting) Un_iff append_Cons last_path path.simps
          self_append_conv2 set_append step.hyps(1) step.hyps(2) step.hyps(3) yszs)
    then show ?thesis
    proof(cases \<open>ys = []\<close>)
      case True
      hence \<open>\<exists>zsa. ([] = [] \<or> path T b p []) \<and> (zsa = [] \<or> path T c e zsa) \<and>
              (p, c) # zs @ [(m, e)] = [] @ (p, c) # zsa \<and> (p, c) \<notin> set [] \<and> (p, c) \<notin> set zsa\<close>
        using pc_xs path_zs yszs by auto
      then show ?thesis
        using yszs by force
    next
      case False
      hence \<open>\<exists>zsa. (ys = [] \<or> path T b p ys) \<and> (zsa = [] \<or> path T c e zsa) \<and>
              ys @ (p, c) # zs @ [(m, e)] = ys @ (p, c) # zsa \<and> (p, c) \<notin> set ys \<and> (p, c) \<notin> set zsa\<close>
        using path_zs pc_xs yszs by auto
      then show ?thesis
        using yszs by force
    qed
  qed
qed

lemma anc_path:
  assumes \<open>ancestor T p c\<close>
  shows \<open>\<exists>xs. path T p c xs\<close>
using assms proof(induction rule: ancestor.induct)
  case (1 parent meta child tree)
  then show ?case by (meson path.intros(1))
next
  case step: (2 parent meta child tree anc)
  then obtain xs where xs: \<open>path tree anc parent xs\<close>
    by blast
  then show ?case
  proof(cases \<open>(parent, child) \<in> set xs\<close>)
    case True
    then show ?thesis
      by (metis step.hyps(1) xs append_Cons append_Nil fst_path path.intros path_split)
  next
    case False
    then show ?thesis
      by (meson path.intros(2) step.hyps(1) xs)
  qed
qed

lemma path_anc:
  assumes \<open>path T p c xs\<close>
  shows \<open>ancestor T p c\<close>
using assms by (induction rule: path.induct, auto simp add: ancestor.intros)

lemma anc_path_eq:
  shows \<open>ancestor T p c \<longleftrightarrow> (\<exists>xs. path T p c xs)\<close>
  by (meson anc_path path_anc)

lemma acyclic_path_eq:
  shows \<open>acyclic T \<longleftrightarrow> (\<nexists>n xs. path T n n xs)\<close>
  by (meson anc_path acyclic_def path_anc)


lemma rem_edge_path:
  assumes \<open>path T m n xs\<close>
    and \<open>T = insert (p, x, c) S\<close>
    and \<open>(p, c) \<notin> set xs\<close>
  shows \<open>path S m n xs\<close>
using assms by (induction rule: path.induct, auto simp add: path.intros)

lemma ancestor_transitive:
  assumes \<open>ancestor \<S> n p\<close> and \<open>ancestor \<S> m n\<close>
    shows \<open>ancestor \<S> m p\<close>
  using assms by (induction rule: ancestor.induct) (auto intro: ancestor.intros)

lemma cyclic_path_technical:
  assumes \<open>path T m m xs\<close>
    and \<open>T = insert (p, x, c) S\<close>
    and \<open>\<forall>n. \<not> ancestor S n n\<close>
    and \<open>c \<noteq> p\<close>
  shows \<open>ancestor S c p\<close>
proof(cases \<open>(p, c) \<in> set xs\<close>)
  case True
  then obtain ys zs where yszs: \<open>(ys = [] \<or> path T m p ys) \<and> (zs = [] \<or> path T c m zs) \<and>
       xs = ys @ [(p, c)] @ zs \<and> (p, c) \<notin> set ys \<and> (p, c) \<notin> set zs\<close>
    using assms(1) path_split by force
  then show ?thesis
  proof(cases \<open>ys = []\<close>)
    case True
    then show ?thesis using assms by (metis append_Cons append_Nil fst_path path_anc
      rem_edge_path singleton_path yszs)
  next
    case False
    then show ?thesis using assms by (metis ancestor_transitive last_path path_anc
      rem_edge_path self_append_conv yszs)
  qed
next
  case False
  then show ?thesis
    using assms by (metis path_anc rem_edge_path)
qed

lemma cyclic_ancestor:
  assumes \<open>\<not> acyclic (S \<union> {(p, x, c)})\<close>
    and \<open>acyclic S\<close> 
    and \<open>c \<noteq> p\<close>
  shows \<open>ancestor S c p\<close>
using assms anc_path acyclic_def cyclic_path_technical by fastforce

lemma do_op_acyclic:
  assumes \<open>acyclic tree1\<close>
    and \<open>do_op (Move t newp m c, tree1) = (log_oper, tree2)\<close>
  shows \<open>acyclic tree2\<close>
proof(cases \<open>ancestor tree1 c newp \<or> c = newp\<close>)
  case True
  then show \<open>acyclic tree2\<close>
    using assms by auto
next
  case False
  hence A: \<open>tree2 = {(p', m', c') \<in> tree1. c' \<noteq> c} \<union> {(newp, m, c)}\<close>
    using assms(2) by auto
  moreover have \<open>{(p', m', c') \<in> tree1. c' \<noteq> c} \<subseteq> tree1\<close>
    by blast
  moreover have \<open>acyclic tree1\<close>
    using assms and acyclic_def by auto
  moreover have B: \<open>acyclic {(p', m', c') \<in> tree1. c' \<noteq> c}\<close>
    using acyclic_subset calculation(2) calculation(3) by blast
  {
    assume \<open>\<not> acyclic tree2\<close>
    hence \<open>ancestor {(p', m', c') \<in> tree1. c' \<noteq> c} c newp\<close>
      using cyclic_ancestor False A B by force
    from this have \<open>False\<close>
      using False ancestor_superset_closed calculation(2) by fastforce
  }
  from this show \<open>acyclic tree2\<close>
    using acyclic_def by auto
qed

lemma do_op_acyclic_var:
  assumes \<open>acyclic tree1\<close>
    and \<open>do_op (oper, tree1) = (log_oper, tree2)\<close>
  shows \<open>acyclic tree2\<close>
  using assms by (metis do_op_acyclic operation.exhaust_sel)

lemma redo_op_acyclic_var:
  assumes \<open>acyclic tree1\<close>
    and \<open>redo_op (LogMove t oldp p m c) (log1, tree1) = (log2, tree2)\<close>
  shows \<open>acyclic tree2\<close>
  using assms by (subst (asm) redo_op.simps) (rule do_op_acyclic, assumption, fastforce)

corollary redo_op_acyclic:
  assumes \<open>acyclic tree1\<close>
    and \<open>redo_op logop (log1, tree1) = (log2, tree2)\<close>
  shows \<open>acyclic tree2\<close>
  using assms by (cases logop) (metis redo_op_acyclic_var)

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