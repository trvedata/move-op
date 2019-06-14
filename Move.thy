theory Move
  imports Main
begin

section \<open>Definitions\<close>

datatype ('t, 'n, 'm) operation
  = Move (move_time: 't)
         (move_parent: 'n)
         (move_meta: 'm)
         (move_child: 'n)

datatype ('t, 'n, 'm) log_op
  = LogMove (log_time: 't)
            (old_parent: \<open>('n \<times> 'm) option\<close>)
            (new_parent: 'n)
            (log_meta: 'm)
            (log_child: 'n)

type_synonym ('t, 'n, 'm) state = \<open>('t, 'n, 'm) log_op list \<times> ('n \<times> 'm \<times> 'n) set\<close>

definition get_parent :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> ('n \<times> 'm) option\<close> where
  \<open>get_parent tree child \<equiv>
     if \<exists>!parent. \<exists>!meta. (parent, meta, child) \<in> tree then
       Some (THE (parent, meta). (parent, meta, child) \<in> tree)
     else None\<close>

inductive ancestor :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool\<close> where
  \<open>\<lbrakk>(parent, meta, child) \<in> tree\<rbrakk> \<Longrightarrow> ancestor tree parent child\<close> |
  \<open>\<lbrakk>(parent, meta, child) \<in> tree; ancestor tree anc parent\<rbrakk> \<Longrightarrow> ancestor tree anc child\<close>

inductive_cases ancestor_indcases: \<open>ancestor \<T> m p\<close>

fun do_op :: \<open>('t, 'n, 'm) operation \<times> ('n \<times> 'm \<times> 'n) set \<Rightarrow>
              ('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set\<close> where
  \<open>do_op (Move t newp m c, tree) =
     (LogMove t (get_parent tree c) newp m c,
      if ancestor tree c newp \<or> c = newp then tree
      else {(p', m', c') \<in> tree. c' \<noteq> c} \<union> {(newp, m, c)})\<close>

fun undo_op :: \<open>('t, 'n, 'm) log_op \<times> ('n \<times> 'm \<times> 'n) set \<Rightarrow> ('n \<times> 'm \<times> 'n) set\<close> where
  \<open>undo_op (LogMove t None newp m c, tree) = {(p', m', c') \<in> tree. c' \<noteq> c}\<close> |
  \<open>undo_op (LogMove t (Some (oldp, oldm)) newp m c, tree) =
     {(p', m', c') \<in> tree. c' \<noteq> c} \<union> {(oldp, oldm, c)}\<close>

fun redo_op :: \<open>('t, 'n, 'm) log_op \<Rightarrow> ('t, 'n, 'm) state \<Rightarrow> ('t, 'n, 'm) state\<close> where
  \<open>redo_op (LogMove t _ p m c) (ops, tree) =
     (let (op2, tree2) = do_op (Move t p m c, tree)
      in (op2 # ops, tree2))\<close>

fun apply_op :: \<open>('t::{linorder}, 'n, 'm) operation \<Rightarrow>
                  ('t, 'n, 'm) state \<Rightarrow> ('t, 'n, 'm) state\<close> where
  \<open>apply_op op1 ([], tree1) =
     (let (op2, tree2) = do_op (op1, tree1)
      in ([op2], tree2))\<close> |
  \<open>apply_op op1 (logop # ops, tree1) =
     (if move_time op1 < log_time logop
      then redo_op logop (apply_op op1 (ops, undo_op (logop, tree1)))
      else let (op2, tree2) = do_op (op1, tree1) in (op2 # logop # ops, tree2))\<close>

abbreviation apply_ops' :: \<open>('t::{linorder}, 'n, 'm) operation list \<Rightarrow> ('t, 'n, 'm) state \<Rightarrow> ('t, 'n, 'm) state\<close> where
  \<open>apply_ops' ops initial \<equiv> foldl (\<lambda>state oper. apply_op oper state) initial ops\<close>

definition apply_ops :: \<open>('t::{linorder}, 'n, 'm) operation list \<Rightarrow> ('t, 'n, 'm) state\<close>
  where \<open>apply_ops ops \<equiv> apply_ops' ops ([], {})\<close>

definition unique_parent :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> bool\<close> where
  \<open>unique_parent tree \<equiv> (\<forall>p1 p2 m1 m2 c. (p1, m1, c) \<in> tree \<and> (p2, m2, c) \<in> tree \<longrightarrow> p1 = p2 \<and> m1 = m2)\<close>

lemma unique_parent_empty[simp]:
  shows \<open>unique_parent {}\<close>
  by (auto simp: unique_parent_def)

lemma unique_parentD [dest]:
  assumes \<open>unique_parent T\<close>
      and \<open>(p1, m1, c) \<in> T\<close>
      and \<open>(p2, m2, c) \<in> T\<close>
    shows \<open>p1 = p2 \<and> m1 = m2\<close>
using assms by(force simp add: unique_parent_def)

lemma unique_parentI [intro]:
  assumes \<open>\<And>p1 p2 m1 m2 c. (p1, m1, c) \<in> T \<Longrightarrow> (p2, m2, c) \<in> T \<Longrightarrow> p1 = p2 \<and> m1 = m2\<close>
  shows \<open>unique_parent T\<close>
using assms by(force simp add: unique_parent_def)

lemma apply_ops_base [simp]:
  shows \<open>apply_ops [Move t1 p1 m1 c1, Move t2 p2 m2 c2] =
                    apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) ([], {}))\<close>
  by (clarsimp simp add: apply_ops_def)

lemma apply_ops_step [simp]:
  shows \<open>apply_ops (xs @ [x]) = apply_op x (apply_ops xs)\<close>
  by (clarsimp simp add: apply_ops_def)

lemma apply_ops_Nil [simp]:
  shows \<open>apply_ops [] = ([], {})\<close>
  by (clarsimp simp add: apply_ops_def)

section \<open>undo-op is the inverse of do-op\<close>

lemma get_parent_None:
  assumes \<open>\<nexists>p m. (p, m, c) \<in> tree\<close>
  shows \<open>get_parent tree c = None\<close>
  by (meson assms get_parent_def)

lemma get_parent_Some:
  assumes \<open>(p, m, c) \<in> tree\<close>
    and \<open>\<And>p' m'. (p', m', c) \<in> tree \<Longrightarrow> p' = p \<and> m' = m\<close>
  shows \<open>get_parent tree c = Some (p, m)\<close>
proof -
  have \<open>\<exists>!parent. \<exists>!meta. (parent, meta, c) \<in> tree\<close>
    using assms by metis
  hence \<open>(THE (parent, meta). (parent, meta, c) \<in> tree) = (p, m)\<close>
    using assms(2) by auto
  thus \<open>get_parent tree c = Some (p, m)\<close>
    using assms get_parent_def by metis
qed

lemma pred_equals_eq3:
  shows \<open>(\<lambda>x y z. (x, y, z) \<in> R) = (\<lambda>x y z. (x, y, z) \<in> S) \<longleftrightarrow> R = S\<close>
  by (simp add: set_eq_iff fun_eq_iff)

lemma do_undo_op_inv:
  assumes \<open>unique_parent tree\<close>
  shows \<open>undo_op (do_op (Move t p m c, tree)) = tree\<close>
proof(cases \<open>\<exists>par meta. (par, meta, c) \<in> tree\<close>)
  case True
  from this obtain oldp oldm where 1: \<open>(oldp, oldm, c) \<in> tree\<close>
    by blast
  hence 2: \<open>get_parent tree c = Some (oldp, oldm)\<close>
    using assms get_parent_Some unique_parent_def by metis
  {
    fix p' m' c'
    assume 3: \<open>(p', m', c') \<in> tree\<close>
    hence \<open>(p', m', c') \<in> undo_op (do_op (Move t p m c, tree))\<close>
      using 1 2 assms unique_parent_def by (cases \<open>c = c'\<close>; fastforce) 
  }
  hence \<open>tree \<subseteq> undo_op (do_op (Move t p m c, tree))\<close>
    by auto
  moreover have \<open>undo_op (do_op (Move t p m c, tree)) \<subseteq> tree\<close>
    using 1 2 by auto
  ultimately show ?thesis
    by blast
next
  case no_old_parent: False
  hence \<open>get_parent tree c = None\<close>
    using assms get_parent_None by metis
  moreover have \<open>{(p', m', c') \<in> tree. c' \<noteq> c} = tree\<close>
    using no_old_parent by fastforce
  moreover from this have \<open>{(p', m', c') \<in> (tree \<union> {(p, m, c)}). c' \<noteq> c} = tree\<close>
    by blast
  ultimately show ?thesis by simp
qed

lemma do_undo_op_inv_var:
  assumes \<open>unique_parent tree\<close>
  shows \<open>undo_op (do_op (oper, tree)) = tree\<close>
  using assms do_undo_op_inv by (metis operation.exhaust_sel)

section \<open>Preserving the invariant that each tree node has at most one parent\<close>

lemma subset_unique_parent:
  assumes \<open>unique_parent tree\<close>
  shows \<open>unique_parent {(p', m', c') \<in> tree. c' \<noteq> c}\<close>
proof -
  {
    fix p1 p2 m1 m2 c'
    assume 1: \<open>(p1, m1, c') \<in> {(p', m', c') \<in> tree. c' \<noteq> c}\<close>
       and 2: \<open>(p2, m2, c') \<in> {(p', m', c') \<in> tree. c' \<noteq> c}\<close>
    have \<open>p1 = p2 \<and> m1 = m2\<close>
    proof(cases \<open>c = c'\<close>)
      case True
      then show ?thesis using 1 2 by auto
    next
      case False
      hence \<open>(p1, m1, c') \<in> tree \<and> (p2, m2, c') \<in> tree\<close>
        using 1 2 by blast
      then show ?thesis
        using assms by (meson unique_parent_def)
    qed
  }
  thus ?thesis by (meson unique_parent_def)
qed

lemma subset_union_unique_parent:
  assumes \<open>unique_parent tree\<close>
  shows \<open>unique_parent ({(p', m', c') \<in> tree. c' \<noteq> c} \<union> {(p, m, c)})\<close>
proof -
  {
    fix p1 p2 m1 m2 c'
    assume 1: \<open>(p1, m1, c') \<in> {(p', m', c') \<in> tree. c' \<noteq> c} \<union> {(p, m, c)}\<close>
       and 2: \<open>(p2, m2, c') \<in> {(p', m', c') \<in> tree. c' \<noteq> c} \<union> {(p, m, c)}\<close>
    have \<open>p1 = p2 \<and> m1 = m2\<close>
    proof(cases \<open>c = c'\<close>)
      case True
      then show ?thesis using 1 2 by auto
    next
      case False
      hence \<open>(p1, m1, c') \<in> tree \<and> (p2, m2, c') \<in> tree\<close>
        using 1 2 by blast
      then show ?thesis
        using assms by (meson unique_parent_def)
    qed
  }
  thus ?thesis by (meson unique_parent_def)
qed

lemma do_op_unique_parent:
  assumes \<open>unique_parent tree1\<close>
    and \<open>do_op (Move t newp m c, tree1) = (log_oper, tree2)\<close>
  shows \<open>unique_parent tree2\<close>
proof(cases \<open>ancestor tree1 c newp \<or> c = newp\<close>)
  case True
  hence \<open>tree1 = tree2\<close>
    using assms(2) by auto
  thus \<open>unique_parent tree2\<close>
    by (metis (full_types) assms(1))
next
  case False
  hence \<open>tree2 = {(p', m', c') \<in> tree1. c' \<noteq> c} \<union> {(newp, m, c)}\<close>
    using assms(2) by auto
  then show \<open>unique_parent tree2\<close>
    using subset_union_unique_parent assms(1) by fastforce
qed

lemma undo_op_unique_parent:
  assumes \<open>unique_parent tree1\<close>
    and \<open>undo_op (LogMove t oldp newp m c, tree1) = tree2\<close>
  shows \<open>unique_parent tree2\<close>
proof (cases oldp)
  case None
  hence \<open>tree2 = {(p', m', c') \<in> tree1. c' \<noteq> c}\<close>
    using assms(2) by auto
  then show ?thesis
    by (simp add: assms(1) subset_unique_parent)
next
  case (Some old)
  obtain oldp oldm where \<open>old = (oldp, oldm)\<close>
    by fastforce
  hence \<open>tree2 = {(p', m', c') \<in> tree1. c' \<noteq> c} \<union> {(oldp, oldm, c)}\<close>
    using Some assms(2) by auto
  then show ?thesis
    using subset_union_unique_parent assms(1) by fastforce
qed

corollary undo_op_unique_parent_variant:
  assumes \<open>unique_parent tree1\<close>
    and \<open>undo_op (oper, tree1) = tree2\<close>
  shows \<open>unique_parent tree2\<close>
using assms by(cases oper, auto simp add: undo_op_unique_parent)

lemma redo_op_unique_parent:
  assumes \<open>unique_parent tree1\<close>
    and \<open>redo_op oper (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>unique_parent tree2\<close>
proof -
  obtain t oldp newp m c where \<open>oper = LogMove t oldp newp m c\<close>
    using log_op.exhaust by blast
  from this obtain move2 where \<open>(move2, tree2) = do_op (Move t newp m c, tree1)\<close>
    using assms(2) by auto
  thus \<open>unique_parent tree2\<close>
    by (metis assms(1) do_op_unique_parent)
qed

lemma apply_op_unique_parent:
  assumes \<open>unique_parent tree1\<close>
    and \<open>apply_op oper (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>unique_parent tree2\<close>
using assms proof(induct ops1 arbitrary: tree1 tree2 ops2)
  case Nil
  have \<open>\<And>pair. snd (case pair of (p1, p2) \<Rightarrow> ([p1], p2)) = snd pair\<close>
    by (simp add: prod.case_eq_if)
  hence \<open>\<exists>log_op. do_op (oper, tree1) = (log_op, tree2)\<close>
    by (metis Nil.prems(2) apply_op.simps(1) prod.collapse snd_conv)
  thus \<open>unique_parent tree2\<close>
    by (metis Nil.prems(1) do_op_unique_parent operation.exhaust_sel)
next
  case step: (Cons logop ops)
  then show \<open>unique_parent tree2\<close>
  proof(cases \<open>move_time oper < log_time logop\<close>)
    case True
    moreover obtain tree1a where \<open>tree1a = undo_op (logop, tree1)\<close>
      by simp
    moreover from this have 1: \<open>unique_parent tree1a\<close>
      using undo_op_unique_parent by (metis step.prems(1) log_op.exhaust_sel)
    moreover obtain ops1b tree1b where \<open>(ops1b, tree1b) = apply_op oper (ops, tree1a)\<close>
      by (metis surj_pair)
    moreover from this have \<open>unique_parent tree1b\<close>
      using 1 by (metis step.hyps)
    ultimately show \<open>unique_parent tree2\<close>
      using redo_op_unique_parent by (metis apply_op.simps(2) step.prems(2))
  next
    case False
    hence \<open>snd (do_op (oper, tree1)) = tree2\<close>
      by (metis (mono_tags, lifting) apply_op.simps(2) prod.sel(2) split_beta step.prems(2))
    then show \<open>unique_parent tree2\<close>
      by (metis do_op_unique_parent operation.exhaust_sel prod.exhaust_sel step.prems(1))
  qed
qed

theorem apply_ops_unique_parent:
  assumes \<open>apply_ops ops = (log, tree)\<close>
  shows \<open>unique_parent tree\<close>
using assms proof(induction ops arbitrary: log tree rule: List.rev_induct)
  case Nil
  hence \<open>apply_ops [] = ([], {})\<close>
    by (simp add: apply_ops_def)
  hence \<open>tree = {}\<close>
    by (metis Nil.prems snd_conv)
  then show ?case
    by (simp add: unique_parent_def)
next
  case (snoc x xs)
  obtain log tree where apply_xs: \<open>apply_ops xs = (log, tree)\<close>
    by fastforce
  hence \<open>apply_ops (xs @ [x]) = apply_op x (log, tree)\<close>
    by (simp add: apply_ops_def)
  moreover have \<open>unique_parent tree\<close>
    by (simp add: apply_xs snoc.IH)
  ultimately show ?case
    by (metis apply_op_unique_parent snoc.prems)
qed


section \<open>Preserving the invariant that the tree contains no cycles\<close>

definition acyclic :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> bool\<close> where
  \<open>acyclic tree \<equiv> (\<nexists>n. ancestor tree n n)\<close>

lemma acyclic_empty [simp]: \<open>acyclic {}\<close>
  by (meson Move.acyclic_def ancestor_indcases empty_iff)

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


section \<open>Commutativity of move operation\<close>

lemma distinct_list_pick1:
  assumes \<open>set (xs @ [x]) = set (ys @ [x] @ zs)\<close>
    and \<open>distinct (xs @ [x])\<close> and \<open>distinct (ys @ [x] @ zs)\<close>
  shows \<open>set xs = set (ys @ zs)\<close>
using assms by (induction xs) (fastforce+)

lemma apply_op_commute_base:
  assumes \<open>t1 < t2\<close>
    and \<open>unique_parent tree\<close>
  shows \<open>apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) ([], tree)) =
         apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) ([], tree))\<close>
proof -
  obtain tree1 where tree1: \<open>do_op (Move t1 p1 m1 c1, tree) =
      (LogMove t1 (get_parent tree c1) p1 m1 c1, tree1)\<close>
    by simp
  obtain tree12 where tree12: \<open>do_op (Move t2 p2 m2 c2, tree1) =
      (LogMove t2 (get_parent tree1 c2) p2 m2 c2, tree12)\<close>
    by simp
  obtain tree2 where tree2: \<open>do_op (Move t2 p2 m2 c2, tree) =
      (LogMove t2 (get_parent tree c2) p2 m2 c2, tree2)\<close>
    by simp
  hence undo2: \<open>undo_op (LogMove t2 (get_parent tree c2) p2 m2 c2, tree2) = tree\<close>
    using assms(2) do_undo_op_inv by fastforce
  have \<open>\<not> t2 < t1\<close>
    using not_less_iff_gr_or_eq assms(1) by blast
  hence \<open>apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) ([], tree)) =
        ([LogMove t2 (get_parent tree1 c2) p2 m2 c2, LogMove t1 (get_parent tree c1) p1 m1 c1], tree12)\<close>
    using tree1 tree12 by auto
  moreover have \<open>apply_op (Move t2 p2 m2 c2) ([], tree) =
      ([LogMove t2 (get_parent tree c2) p2 m2 c2], tree2)\<close>
    using tree2 by auto
  hence \<open>apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) ([], tree)) =
         redo_op (LogMove t2 (get_parent tree c2) p2 m2 c2) ([LogMove t1 (get_parent tree c1) p1 m1 c1], tree1)\<close>
    using tree1 undo2 assms(1) by auto
  ultimately show ?thesis
    using tree12 by auto
qed

lemma apply_op_log_cons:
  assumes \<open>apply_op (Move t1 p1 m1 c1) (log, tree) = (log2, tree2)\<close>
  shows \<open>\<exists>logop rest. log2 = logop # rest \<and> t1 \<le> log_time logop\<close>
proof(cases log)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons logop rest)
  obtain t2 oldp2 p2 m2 c2 where logop: \<open>logop = LogMove t2 oldp2 p2 m2 c2\<close>
    using log_op.exhaust by blast
  then show ?thesis
  proof(cases \<open>t1 < t2\<close>)
    case True
    obtain tree1 log1 where tree1: \<open>apply_op (Move t1 p1 m1 c1) (rest, undo_op (logop, tree)) = (log1, tree1)\<close>
      by fastforce
    obtain tree12 where \<open>do_op (Move t2 p2 m2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 m2 c2, tree12)\<close>
      by simp
    hence \<open>apply_op (Move t1 p1 m1 c1) (log, tree) = (LogMove t2 (get_parent tree1 c2) p2 m2 c2 # log1, tree12)\<close>
      using True local.Cons tree1 logop by auto
    then show ?thesis
      using True assms by auto
  next
    case False
    obtain tree1 where tree1: \<open>do_op (Move t1 p1 m1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 m1 c1, tree1)\<close>
      by simp
    hence \<open>apply_op (Move t1 p1 m1 c1) (log, tree) =
           (LogMove t1 (get_parent tree c1) p1 m1 c1 # log, tree1)\<close>
      using False local.Cons logop by auto
    then show ?thesis
      using assms by auto
  qed
qed

lemma apply_op_commute2:
  assumes \<open>t1 < t2\<close>
    and \<open>unique_parent tree\<close>
    and \<open>distinct ((map log_time log) @ [t1, t2])\<close>
  shows \<open>apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) (log, tree)) =
         apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) (log, tree))\<close>
using assms proof(induction log arbitrary: tree)
  case Nil
  then show ?case using apply_op_commute_base by metis
next
  case (Cons logop log)
  have parent0: \<open>unique_parent (undo_op (logop, tree))\<close>
    by (metis Cons.prems(2) log_op.exhaust_sel undo_op_unique_parent)
  obtain t3 oldp3 p3 m3 c3 where logop: \<open>logop = LogMove t3 oldp3 p3 m3 c3\<close>
    using log_op.exhaust by blast
  then consider (c1) \<open>t3 < t1\<close> | (c2) \<open>t1 < t3 \<and> t3 < t2\<close> | (c3) \<open>t2 < t3\<close>
    using Cons.prems(3) by force
  then show ?case
  proof(cases)
    case c1 (* t3 < t1 < t2 *)
    obtain tree1 where tree1: \<open>do_op (Move t1 p1 m1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 m1 c1, tree1)\<close>
      by simp
    obtain tree12 where tree12: \<open>do_op (Move t2 p2 m2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 m2 c2, tree12)\<close>
      by simp
    obtain tree2 where tree2: \<open>do_op (Move t2 p2 m2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 m2 c2, tree2)\<close>
      by simp
    hence undo2: \<open>undo_op (LogMove t2 (get_parent tree c2) p2 m2 c2, tree2) = tree\<close>
      using Cons.prems(2) do_undo_op_inv by metis
    have \<open>\<not> t2 < t1\<close>
      using not_less_iff_gr_or_eq Cons.prems(1) by blast
    hence \<open>apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) (logop # log, tree)) =
           ([LogMove t2 (get_parent tree1 c2) p2 m2 c2, LogMove t1 (get_parent tree c1) p1 m1 c1, logop] @ log, tree12)\<close>
      using tree1 tree12 logop c1 by auto
    moreover have \<open>t3 < t2\<close>
      using c1 Cons.prems(1) by auto
    hence \<open>apply_op (Move t2 p2 m2 c2) (logop # log, tree) = (LogMove t2 (get_parent tree c2) p2 m2 c2 # logop # log, tree2)\<close>
      using tree2 logop by auto
    hence \<open>apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) (logop # log, tree)) =
           redo_op (LogMove t2 (get_parent tree c2) p2 m2 c2) (LogMove t1 (get_parent tree c1) p1 m1 c1 # logop # log, tree1)\<close>
      using Cons.prems(1) c1 logop tree1 undo2 by auto
    ultimately show ?thesis
      using tree12 by auto
  next
    case c2 (* t1 < t3 < t2 *)
    obtain tree1 log1 where tree1: \<open>apply_op (Move t1 p1 m1 c1) (log, undo_op (logop, tree)) = (log1, tree1)\<close>
      by fastforce
    obtain tree13 where tree13: \<open>do_op (Move t3 p3 m3 c3, tree1) = (LogMove t3 (get_parent tree1 c3) p3 m3 c3, tree13)\<close>
      by simp
    obtain tree132 where tree132: \<open>do_op (Move t2 p2 m2 c2, tree13) = (LogMove t2 (get_parent tree13 c2) p2 m2 c2, tree132)\<close>
      by simp
    obtain tree2 where tree2: \<open>do_op (Move t2 p2 m2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 m2 c2, tree2)\<close>
      by simp
    hence undo2: \<open>undo_op (LogMove t2 (get_parent tree c2) p2 m2 c2, tree2) = tree\<close>
      by (metis Cons.prems(2) do_undo_op_inv)
    have \<open>apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) (logop # log, tree)) =
           (LogMove t2 (get_parent tree13 c2) p2 m2 c2 # LogMove t3 (get_parent tree1 c3) p3 m3 c3 # log1, tree132)\<close>
      using c2 logop tree1 tree13 tree132 by auto
    moreover have \<open>apply_op (Move t2 p2 m2 c2) (logop # log, tree) =
                   (LogMove t2 (get_parent tree c2) p2 m2 c2 # logop # log, tree2)\<close>
      using c2 logop tree2 by auto
    hence \<open>apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) (logop # log, tree)) =
           (LogMove t2 (get_parent tree13 c2) p2 m2 c2 # LogMove t3 (get_parent tree1 c3) p3 m3 c3 # log1, tree132)\<close>
      using assms(1) undo2 c2 logop tree1 tree13 tree132 by auto
    ultimately show ?thesis by simp
  next
    case c3 (* t1 < t2 < t3 *)
    obtain tree1 log1 where tree1: \<open>apply_op (Move t1 p1 m1 c1) (log, undo_op (logop, tree)) = (log1, tree1)\<close>
      by fastforce
    obtain tree13 where tree13: \<open>do_op (Move t3 p3 m3 c3, tree1) = (LogMove t3 (get_parent tree1 c3) p3 m3 c3, tree13)\<close>
      by simp
    hence undo13: \<open>undo_op (LogMove t3 (get_parent tree1 c3) p3 m3 c3, tree13) = tree1\<close>
    proof -
      have \<open>unique_parent tree1\<close>
        by (meson apply_op_unique_parent parent0 tree1)
      thus ?thesis
        using do_undo_op_inv tree13 by metis
    qed
    obtain tree12 log12 where tree12: \<open>apply_op (Move t2 p2 m2 c2) (log1, tree1) = (log12, tree12)\<close>
      by fastforce
    obtain tree123 where tree123: \<open>do_op (Move t3 p3 m3 c3, tree12) = (LogMove t3 (get_parent tree12 c3) p3 m3 c3, tree123)\<close>
      by simp
    obtain tree2 log2 where tree2: \<open>apply_op (Move t2 p2 m2 c2) (log, undo_op (logop, tree)) = (log2, tree2)\<close>
      by fastforce
    obtain tree21 log21 where tree21: \<open>apply_op (Move t1 p1 m1 c1) (log2, tree2) = (log21, tree21)\<close>
      by fastforce
    obtain tree213 where tree213: \<open>do_op (Move t3 p3 m3 c3, tree21) = (LogMove t3 (get_parent tree21 c3) p3 m3 c3, tree213)\<close>
      by simp
    obtain tree23 where tree23: \<open>do_op (Move t3 p3 m3 c3, tree2) = (LogMove t3 (get_parent tree2 c3) p3 m3 c3, tree23)\<close>
      by simp
    hence undo23: \<open>undo_op (LogMove t3 (get_parent tree2 c3) p3 m3 c3, tree23) = tree2\<close>
    proof -
      have \<open>unique_parent tree2\<close>
        by (meson apply_op_unique_parent parent0 tree2)
      thus ?thesis
        using do_undo_op_inv tree23 by metis
    qed
    have \<open>apply_op (Move t1 p1 m1 c1) (logop # log, tree) =
           (LogMove t3 (get_parent tree1 c3) p3 m3 c3 # log1, tree13)\<close>
      using assms(1) c3 logop tree1 tree13 by auto
    hence \<open>apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) (logop # log, tree)) =
           (LogMove t3 (get_parent tree12 c3) p3 m3 c3 # log12, tree123)\<close>
      using c3 tree12 tree123 undo13 by auto
    moreover have \<open>apply_op (Move t2 p2 m2 c2) (logop # log, tree) =
          (LogMove t3 (get_parent tree2 c3) p3 m3 c3 # log2, tree23)\<close>
      using c3 logop tree2 tree23 by auto
    hence \<open>apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) (logop # log, tree)) =
           (LogMove t3 (get_parent tree21 c3) p3 m3 c3 # log21, tree213)\<close>
      using assms(1) c3 undo23 tree21 tree213 by auto
    moreover have \<open>apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) (log, undo_op (logop, tree))) =
                   apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) (log, undo_op (logop, tree)))\<close>
      using Cons.IH Cons.prems(3) assms(1) parent0 by auto
    ultimately show ?thesis
      using tree1 tree12 tree123 tree2 tree21 tree213 by auto
  qed
qed

corollary apply_op_commute2I:
  assumes \<open>unique_parent tree\<close>
    and \<open>distinct ((map log_time log) @ [t1, t2])\<close>
    and \<open>apply_op (Move t1 p1 m1 c1) (log, tree) = (log1, tree1)\<close>
    and \<open>apply_op (Move t2 p2 m2 c2) (log, tree) = (log2, tree2)\<close>
  shows \<open>apply_op (Move t2 p2 m2 c2) (log1, tree1) = apply_op (Move t1 p1 m1 c1) (log2, tree2)\<close>
proof (case_tac \<open>t1 < t2\<close>, metis assms apply_op_commute2)
  assume \<open>\<not> t1 < t2\<close>
  hence \<open>t2 < t1\<close>
    using assms by force
  moreover have \<open>distinct ((map log_time log) @ [t2, t1])\<close>
    using assms by force
  ultimately show ?thesis
    using assms apply_op_commute2 by metis
qed

lemma apply_op_timestamp:
  assumes \<open>distinct ((map log_time log1) @ [t])\<close>
    and \<open>apply_op (Move t p m c) (log1, tree1) = (log2, tree2)\<close>
  shows \<open>distinct (map log_time log2) \<and> set (map log_time log2) = {t} \<union> set (map log_time log1)\<close>
using assms proof(induction log1 arbitrary: tree1 log2 tree2)
  case Nil
  then show ?case by auto
next
  case (Cons logop log)
  obtain log3 tree3 where log3: \<open>apply_op (Move t p m c) (log, undo_op (logop, tree1)) = (log3, tree3)\<close>
    using prod.exhaust_sel by blast
  have \<open>distinct ((map log_time log) @ [t])\<close>
    using Cons.prems(1) by auto
  hence IH: \<open>distinct (map log_time log3) \<and> set (map log_time log3) = {t} \<union> set (map log_time log)\<close>
    using Cons.IH Cons.prems(1) log3 by auto
  then show ?case
  proof(cases \<open>t < log_time logop\<close>)
    case recursive_case: True
    obtain t2 oldp2 p2 m2 c2 where logop: \<open>logop = LogMove t2 oldp2 p2 m2 c2\<close>
      using log_op.exhaust by blast
    obtain tree4 where \<open>do_op (Move t2 p2 m2 c2, tree3) = (LogMove t2 (get_parent tree3 c2) p2 m2 c2, tree4)\<close>
      by simp
    hence \<open>apply_op (Move t p m c) (logop # log, tree1) =
           (LogMove t2 (get_parent tree3 c2) p2 m2 c2 # log3, tree4)\<close>
      using logop log3 recursive_case by auto
    moreover from this have \<open>set (map log_time log2) = {t} \<union> set (map log_time (logop # log))\<close>
      using Cons.prems(2) IH logop by fastforce
    moreover have \<open>distinct (map log_time (LogMove t2 (get_parent tree3 c2) p2 m2 c2 # log3))\<close>
      using Cons.prems(1) IH logop recursive_case by auto
    ultimately show ?thesis
      using Cons.prems(2) by auto
  next
    case cons_case: False
    obtain tree4 where \<open>do_op (Move t p m c, tree1) = (LogMove t (get_parent tree1 c) p m c, tree4)\<close>
      by simp
    hence \<open>apply_op (Move t p m c) (logop # log, tree1) =
           (LogMove t (get_parent tree1 c) p m c # logop # log, tree4)\<close>
      by (simp add: cons_case)
    moreover from this have \<open>set (map log_time log2) = {t} \<union> set (map log_time (logop # log))\<close>
      using Cons.prems(2) by auto
    moreover have \<open>distinct (t # map log_time (logop # log))\<close>
      using Cons.prems(1) by auto
    ultimately show ?thesis
      using Cons.prems(2) by auto
  qed
qed

corollary apply_op_timestampI1:
  assumes \<open>apply_op (Move t p m c) (log1, tree1) = (log2, tree2)\<close> \<open>distinct ((map log_time log1) @ [t])\<close>
  shows \<open>distinct (map log_time log2)\<close>
  using assms apply_op_timestamp by metis

corollary apply_op_timestampI2:
  assumes \<open>apply_op (Move t p m c) (log1, tree1) = (log2, tree2)\<close> \<open>distinct ((map log_time log1) @ [t])\<close>
  shows \<open>set (map log_time log2) = {t} \<union> set (map log_time log1)\<close>
  using assms apply_op_timestamp by metis

lemma apply_ops_timestamps:
  assumes \<open>distinct (map move_time ops)\<close>
    and \<open>apply_ops ops = (log, tree)\<close>
  shows \<open>distinct (map log_time log) \<and> set (map move_time ops) = set (map log_time log)\<close>
using assms proof(induction ops arbitrary: log tree rule: List.rev_induct, simp)
  case (snoc oper ops)
  obtain log1 tree1 where log1: \<open>apply_ops ops = (log1, tree1)\<close>
    by fastforce
  hence IH: \<open>distinct (map log_time log1) \<and> set (map move_time ops) = set (map log_time log1)\<close>
    using snoc by auto
  hence \<open>set (map move_time (ops @ [oper])) = {move_time oper} \<union> set (map log_time log1)\<close>
    by force
  moreover have \<open>distinct (map log_time log1 @ [move_time oper])\<close>
    using log1 snoc(1) snoc.prems(1) by force
  ultimately show ?case
    by (metis (no_types) apply_op_timestamp apply_ops_step log1 operation.exhaust_sel snoc.prems(2))
qed

lemma apply_op_commute_last:
  assumes \<open>distinct ((map move_time ops) @ [t1, t2])\<close>
  shows \<open>apply_ops (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2]) =
         apply_ops (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1])\<close>
proof -
  obtain log tree where apply_ops: \<open>apply_ops ops = (log, tree)\<close>
    by fastforce
  hence unique_parent: \<open>unique_parent tree\<close>
    by (meson apply_ops_unique_parent)
  have distinct_times: \<open>distinct ((map log_time log) @ [t1, t2])\<close>
    using assms apply_ops apply_ops_timestamps by auto
  have \<open>apply_ops (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2]) =
        apply_op (Move t2 p2 m2 c2) (apply_op (Move t1 p1 m1 c1) (log, tree))\<close>
    using apply_ops by (simp add: apply_ops_def)
  also have \<open>... = apply_op (Move t1 p1 m1 c1) (apply_op (Move t2 p2 m2 c2) (log, tree))\<close>
  proof(cases \<open>t1 < t2\<close>)
    case True
    then show ?thesis
      by (metis unique_parent distinct_times apply_op_commute2)
  next
    case False
    hence \<open>t2 < t1\<close>
      using assms by auto
    moreover have \<open>distinct ((map log_time log) @ [t2, t1])\<close>
      using distinct_times by auto
    ultimately show ?thesis
      by (metis unique_parent apply_op_commute2)
  qed
  also have \<open>... = apply_ops (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1])\<close>
    using apply_ops by (simp add: apply_ops_def)
  ultimately show ?thesis
    by presburger
qed

lemma apply_op_commute_middle:
  assumes \<open>distinct (map move_time (xs @ ys @ [oper]))\<close>
  shows \<open>apply_ops (xs @ ys @ [oper]) = apply_ops (xs @ [oper] @ ys)\<close>
using assms proof(induction ys rule: List.rev_induct, simp)
  case (snoc y ys)
  have \<open>apply_ops (xs @ [oper] @ ys @ [y]) = apply_op y (apply_ops (xs @ [oper] @ ys))\<close>
    by (metis append.assoc apply_ops_step)
  also have \<open>... = apply_op y (apply_ops (xs @ ys @ [oper]))\<close>
  proof -
    have \<open>distinct (map move_time (xs @ ys @ [oper]))\<close>
      using snoc.prems by auto
    then show ?thesis
      using snoc.IH by auto
  qed
  also have \<open>... = apply_ops ((xs @ ys) @ [oper, y])\<close>
    by (metis append.assoc append_Cons append_Nil apply_ops_step)
  also have \<open>... = apply_ops ((xs @ ys) @ [y, oper])\<close>
  proof -
    have \<open>distinct ((map move_time (xs @ ys)) @ [move_time y, move_time oper])\<close>
      using snoc.prems by auto
    thus ?thesis
      using apply_op_commute_last by (metis operation.exhaust_sel)
  qed
  ultimately show ?case
    by simp
qed

theorem apply_ops_commutes:
  assumes \<open>set ops1 = set ops2\<close>
    and \<open>distinct (map move_time ops1)\<close>
    and \<open>distinct (map move_time ops2)\<close>
  shows \<open>apply_ops ops1 = apply_ops ops2\<close>
using assms proof(induction ops1 arbitrary: ops2 rule: List.rev_induct, simp)
  case (snoc oper ops)
  then obtain pre suf where pre_suf: \<open>ops2 = pre @ [oper] @ suf\<close>
    by (metis append_Cons append_Nil in_set_conv_decomp)
  hence \<open>set ops = set (pre @ suf)\<close>
    using snoc.prems distinct_map distinct_list_pick1 by metis
  hence IH: \<open>apply_ops ops = apply_ops (pre @ suf)\<close>
    using pre_suf snoc.IH snoc.prems by auto
  moreover have \<open>distinct (map move_time (pre @ suf @ [oper]))\<close>
    using pre_suf snoc.prems(3) by auto
  moreover from this have \<open>apply_ops (pre @ suf @ [oper]) = apply_ops (pre @ [oper] @ suf)\<close>
    using apply_op_commute_middle by blast
  ultimately show \<open>apply_ops (ops @ [oper]) = apply_ops ops2\<close>
    by (metis append_assoc apply_ops_step pre_suf)
qed


end
