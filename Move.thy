theory Move
  imports Main "HOL-Library.Code_Target_Numeral" "Collections.Collections" "Collections.ICF_Userguide"
    "HOL-Library.Product_Lexorder"
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
    have \<open>(p', m', c') \<in> undo_op (do_op (Move t p m c, tree))\<close>
    proof(cases \<open>c = c'\<close>)
      case True
      then show ?thesis using 1 2 3 assms unique_parent_def by fastforce
    next
      case False
      then show ?thesis using 2 3 by auto
    qed
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

inductive_cases ancestor_indcases: \<open>ancestor \<T> m p\<close>

definition acyclic :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> bool\<close> where
  \<open>acyclic tree \<equiv> (\<nexists>n. ancestor tree n n)\<close>

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

lemma undo_op_acyclic_helper2:
\<open>path tree2 n n xs \<Longrightarrow> acyclic tree1 \<Longrightarrow>
           tree2 = insert (oldp, oldm, c) {(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> c} \<Longrightarrow>
           \<exists>xs. path tree2 c c xs\<close>
  apply (erule path_indcases)
   apply clarsimp
   apply (erule disjE1)
    apply clarsimp
    apply (rule_tac x="[(c, c)]" in exI)
    apply (rule path.intros)
    apply force
   apply clarsimp
   apply (meson acyclic_path_eq path.intros(1))
  apply clarsimp
  apply (erule disjE1)
   apply clarsimp
   apply (subgoal_tac "\<exists>ysa. path (insert (oldp, oldm, c) {(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> c}) oldp c ysa")
    apply clarsimp
    apply (meson anc_path ancestor_transitive path_anc)
   apply (rule_tac x="[(oldp, c)]" in exI)
   apply (rule path.intros)
   apply force
  apply clarsimp
  oops

lemma undo_op_acyclic_helper2:
\<open>path tree2 n m xs \<Longrightarrow> n = m \<Longrightarrow> acyclic tree1 \<Longrightarrow>
           tree2 = insert (oldp, oldm, c) {(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> c} \<Longrightarrow>
           \<exists>xs. path tree2 c c xs\<close>
  apply (induction rule: path.induct)
   apply clarsimp
   apply (erule disjE1)
    apply clarsimp
    apply (rule_tac x="[(c, c)]" in exI)
    apply (rule path.intros)
    apply force
   apply clarsimp
   apply (meson acyclic_path_eq path.intros(1))
  apply clarsimp
  apply (erule disjE1)
   apply clarsimp
   apply (subgoal_tac "\<exists>ysa. path (insert (oldp, oldm, c) {(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> c}) oldp c ysa")
    apply clarsimp
    apply (meson anc_path ancestor_transitive path_anc)
   apply (rule_tac x="[(oldp, c)]" in exI)
   apply (rule path.intros)
   apply force
  apply clarsimp
  oops


(*
  apply (induction xs rule: rev_induct)
  using empty_path apply force
  apply clarsimp
  apply (erule path_indcases)
   apply clarsimp
   apply (erule disjE1)
    apply clarsimp
    apply (rule_tac x="[(c, c)]" in exI)
    apply (rule path.intros)
    apply force
   apply clarsimp
   apply (meson acyclic_path_eq path.intros(1))
  apply clarsimp
  apply (erule disjE1)
   apply clarsimp
   apply (subgoal_tac "\<exists>ysa. path (insert (oldp, oldm, c) {(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> c}) oldp c ysa")
    apply clarsimp
    apply (meson anc_path ancestor_transitive path_anc)
   apply (rule_tac x="[(oldp, c)]" in exI)
   apply (rule path.intros)
   apply force
  apply clarsimp
  *)

lemma undo_op_acyclic_helper:
  assumes \<open>acyclic tree1\<close>
  and \<open>undo_op (LogMove t (Some (oldp, oldm)) p m c, tree1) = tree2\<close>
  and \<open>\<not> acyclic tree2\<close>
shows \<open>\<exists>xs. path tree2 oldp oldp xs\<close>
  using assms apply clarsimp
  apply (subst (asm) acyclic_path_eq) back
  apply clarsimp
  oops

lemma undo_op_acyclic:
  assumes \<open>acyclic tree1\<close>
  and \<open>undo_op (LogMove t (Some (oldp, oldm)) p m c, tree1) = tree2\<close>
  shows \<open>acyclic tree2 \<or> (\<exists>xs. path tree2 oldp oldp xs \<and> (\<forall>(n, _) \<in> set xs. \<not> (\<exists>ys. path tree2 n n ys)))\<close>
  using assms apply clarsimp
  apply (subst (asm) acyclic_path_eq)
  oops

lemma
  assumes \<open>acyclic tree1\<close>
    and \<open>\<forall>log1 tree1 log2 tree2. apply_op x (log1, tree1) = (log2, tree2) \<and> acyclic tree1 \<longrightarrow> acyclic tree2\<close>
    and \<open>redo_op a (apply_op x (log1, undo_op (a, tree1))) = (log2, tree2)\<close>
  shows \<open>acyclic tree2\<close>
  using assms
  apply (induction log1 arbitrary: a tree1 log2 tree2)
   apply clarsimp
   apply (case_tac "do_op (x, undo_op (a, tree1))")
   apply clarsimp
   apply (subgoal_tac "acyclic b")
  using redo_op_acyclic apply blast
   apply (case_tac a)
   apply clarsimp
   apply (case_tac x2)
    apply clarsimp
    apply (subgoal_tac "acyclic {(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> x5}")
     apply (smt do_op_acyclic operation.exhaust snd_conv)
    apply (rule acyclic_subset)
     apply assumption
    apply force
  apply clarsimp
   apply (case_tac x)
  apply clarsimp


  oops






(*
lemma \<open>\<exists>log2. redo_op a (apply_op x (log1, undo_op (a, tree1))) = (log2, tree1)\<close>
  *)

lemma apply_op_acyclic:
  assumes \<open>acyclic tree1\<close>
    and \<open>apply_op x (log1, tree1) = (log2, tree2)\<close>
  shows \<open>acyclic tree2\<close>
  using assms
  apply (induction log1 arbitrary: log2 tree1 tree2)
   apply clarsimp
   apply (case_tac "do_op (x, tree1)")
   apply clarsimp
   apply (metis do_op_acyclic operation.exhaust)
  apply clarsimp
  apply (case_tac "move_time x < log_time a")
   defer
   apply clarsimp
   apply (case_tac "do_op (x, tree1)")
   apply clarsimp
   apply (metis do_op_acyclic operation.exhaust)
  apply clarsimp
  apply (case_tac a)
  apply clarsimp
  apply (case_tac x2)
   apply clarsimp
   apply (case_tac "apply_op x (log1, {(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> x5})")
   apply (erule_tac x=a in meta_allE)
   apply (erule_tac x="{(p', m', c'). (p', m', c') \<in> tree1 \<and> c' \<noteq> x5}" in meta_allE)
   apply (erule_tac x=b in meta_allE)
   apply (erule meta_impE)
    apply (rule acyclic_subset)
     apply assumption
  apply force
    apply (erule meta_impE, force)
   apply (simp add: redo_op_acyclic_var)
  apply clarsimp
  apply (case_tac x)
  apply clarsimp
  oops



theorem apply_ops_acyclic:
  assumes \<open>apply_ops ops = (log, tree)\<close>
  shows \<open>acyclic tree\<close>
  using assms
  apply (induction ops arbitrary: log tree rule: List.rev_induct)
  using acyclic_def apply fastforce
  apply simp
  apply (case_tac "apply_ops xs")
  apply (erule_tac x=a in meta_allE)
  apply (erule_tac x=b in meta_allE)
  apply clarsimp
  apply (case_tac a)
   apply clarsimp
   apply (case_tac "do_op (x, b)")
   apply clarsimp
   apply (metis do_op_acyclic operation.exhaust)
  apply clarsimp
  apply (case_tac "move_time x < log_time aa")
   apply clarsimp
  sorry
(*
using assms proof(induction ops arbitrary: log tree rule: List.rev_induct)
  case Nil
  then show ?case by (simp add: acyclic_def apply_ops_def)
next
  case (snoc x xs)
  then obtain log1 tree1 where \<open>apply_ops xs = (log1, tree1)\<close>
    by fastforce
  moreover from this have \<open>apply_ops (xs @ [x]) = apply_op x (log1, tree1)\<close>
    by (metis (no_types) foldl_Cons foldl_Nil foldl_append apply_ops_def)
  ultimately show ?case
    sorry (* TODO: need to generalise do_op_acyclic to hold for apply_op *)
qed
*)

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

section\<open>Code generation: an efficient implementation\<close>

inductive ancestor_alt :: \<open>('n \<times> 'm \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool\<close>
  where \<open>get_parent T c = Some (p, m) \<Longrightarrow> ancestor_alt T p c\<close>
      | \<open>get_parent T c = Some (p, m) \<Longrightarrow> ancestor_alt T a p \<Longrightarrow> ancestor_alt T a c\<close>

lemma get_parent_SomeI [intro]:
  assumes \<open>unique_parent T\<close>
    and \<open>(p, m, c) \<in> T\<close>
  shows \<open>get_parent T c = Some (p, m)\<close>
using assms by(auto simp add: get_parent_def)

lemma get_parent_SomeD:
  assumes 1: \<open>get_parent T c = Some (p, m)\<close>
    and 2: \<open>unique_parent T\<close>
  shows \<open>(p, m, c) \<in> T\<close>
proof -
  {
    assume 3: \<open>\<exists>!parent. \<exists>!meta. (parent, meta, c) \<in> T\<close>
    from this have \<open>get_parent T c = Some (THE (parent, meta). (parent, meta, c) \<in> T)\<close>
      by(auto simp add: get_parent_def)
    from this and 1 have \<open>(THE (parent, meta). (parent, meta, c) \<in> T) = (p, m)\<close>
      by force
    from this and 1 and 2 and 3 have \<open>(p, m, c) \<in> T\<close>
      using get_parent_SomeI by fastforce
  }
  note L = this
  {
    assume \<open>\<not> (\<exists>!parent. \<exists>!meta. (parent, meta, c) \<in> T)\<close>
    from this have \<open>get_parent T c = None\<close>
      by(auto simp add: get_parent_def)
    from this and 1 have \<open>(p, m, c) \<in> T\<close>
      by simp
  }
  from this and L show ?thesis
    by blast
qed

lemma get_parent_NoneD:
  assumes \<open>get_parent T c = None\<close>
    and \<open>unique_parent T\<close>
    and \<open>(p, m, c) \<in> T\<close>
  shows \<open>False\<close>
using assms
  apply(clarsimp simp add: get_parent_def unique_parent_def split: if_split_asm)
  using assms(1) assms(2) get_parent_SomeI apply fastforce
  done

lemma get_parent_NoneI:
  assumes \<open>unique_parent T\<close>
    and \<open>\<And>p m. (p, m, c) \<notin> T\<close>
  shows \<open>get_parent T c = None\<close>
using assms
  by(clarsimp simp add: unique_parent_def get_parent_def)

lemma ancestor_ancestor_alt:
  assumes \<open>ancestor T p c\<close> and \<open>unique_parent T\<close>
    shows \<open>ancestor_alt T p c\<close>
using assms
  apply(induction rule: ancestor.induct)
  apply(rule ancestor_alt.intros)
  apply(rule get_parent_SomeI)
  apply force+
  apply(clarsimp)
  apply(rule ancestor_alt.intros(2))
  apply(rule get_parent_SomeI)
  apply force+
  done

lemma ancestor_alt_ancestor:
  assumes \<open>ancestor_alt T p c\<close> and \<open>unique_parent T\<close>
    shows \<open>ancestor T p c\<close>
using assms
  apply(induction rule: ancestor_alt.induct)
  apply(drule get_parent_SomeD, assumption)
  apply(rule ancestor.intros(1))
  apply force
  apply clarsimp
  apply(rule ancestor.intros(2))
  apply(drule get_parent_SomeD)
  apply force+
  done

theorem ancestor_ancestor_alt_iff [simp]:
  assumes \<open>unique_parent T\<close>
  shows \<open>ancestor T p c \<longleftrightarrow> ancestor_alt T p c\<close>
using assms ancestor_ancestor_alt ancestor_alt_ancestor by metis

lemma unique_parent_emptyI [intro!]:
  shows \<open>unique_parent {}\<close>
  by(auto simp add: unique_parent_def)

lemma unique_parent_singletonI [intro!]:
  shows \<open>unique_parent {x}\<close>
  by(auto simp add: unique_parent_def)

definition refines :: \<open>('n::{hashable}, 'm \<times> 'n) hm \<Rightarrow> ('n \<times> 'm \<times> 'n) set \<Rightarrow> bool\<close> (infix "\<preceq>" 50)
  where \<open>refines Rs Ss \<longleftrightarrow>
           (\<forall>p m c. hm.lookup c Rs = Some (m, p) \<longleftrightarrow> (p, m, c) \<in> Ss)\<close>

lemma refinesI [intro!]:
  assumes \<open>\<And>p m c. hm.lookup c Rs = Some (m, p) \<Longrightarrow> (p, m, c) \<in> Ss\<close>
    and \<open>\<And>p m c. (p, m, c) \<in> Ss \<Longrightarrow> hm.lookup c Rs = Some (m, p)\<close>
  shows \<open>Rs \<preceq> Ss\<close>
using assms unfolding refines_def by meson

lemma weak_refinesE:
  assumes \<open>Rs \<preceq> Ss\<close>
    and \<open>(\<And>p m c. hm.lookup c Rs = Some (m, p) \<Longrightarrow> (p, m, c) \<in> Ss) \<Longrightarrow> (\<And>p m c. (p, m, c) \<in> Ss \<Longrightarrow> hm.lookup c Rs = Some (m, p)) \<Longrightarrow> P\<close>
  shows P
using assms by(auto simp add: refines_def)

lemma refinesE [elim]:
  assumes \<open>Rs \<preceq> Ss\<close>
    and \<open>(\<And>p m c. (hm.lookup c Rs = Some (m, p)) \<longleftrightarrow> (p, m, c) \<in> Ss) \<Longrightarrow> P\<close>
  shows P
using assms by(auto simp add: refines_def)

lemma empty_refinesI [intro!]:
  shows \<open>hm.empty () \<preceq> {}\<close>
  by(auto simp add: hm.correct)

lemma get_parent_refinement_Some1:
  assumes \<open>get_parent T c = Some (p, m)\<close>
    and \<open>unique_parent T\<close>
    and \<open>t \<preceq> T\<close>
    shows \<open>hm.lookup c t = Some (m, p)\<close>
using assms
  apply -
  apply(erule refinesE)
  apply(drule get_parent_SomeD)
  apply force             
  apply meson
  done

lemma get_parent_refinement_Some2:
  assumes \<open>hm.lookup c t = Some (m, p)\<close>
    and \<open>unique_parent T\<close>
    and \<open>t \<preceq> T\<close>
    shows \<open>get_parent T c = Some (p, m)\<close>
using assms
  apply -
  apply(erule refinesE)
  apply(drule get_parent_SomeI)
  apply force             
  apply meson
  done

lemma get_parent_refinement_None1:
  assumes \<open>get_parent T c = None\<close>
    and \<open>unique_parent T\<close>
    and \<open>t \<preceq> T\<close>
    shows \<open>hm.lookup c t = None\<close>
using assms
  apply -
  apply(erule refinesE)
  apply(subgoal_tac \<open>\<forall>p m. (p, m, c) \<notin> T\<close>)
  apply(force dest: get_parent_NoneD)
  apply(intro allI notI)
  apply(drule get_parent_NoneD)
  apply force+
  done

lemma get_parent_refinement_None2:
  assumes \<open>hm.lookup c t = None\<close>
    and \<open>unique_parent T\<close>
    and \<open>t \<preceq> T\<close>
    shows \<open>get_parent T c = None\<close>
using assms
  apply -
  apply(erule refinesE)
  apply(rule get_parent_NoneI)
  apply force+
  done

corollary get_parent_refinement:
  fixes T :: \<open>('a::{hashable} \<times> 'b \<times> 'a) set\<close>
  assumes \<open>unique_parent T\<close> and \<open>t \<preceq> T\<close>
  shows \<open>get_parent T c = map_option (\<lambda>x. (snd x, fst x)) (hm.lookup c t)\<close>
using assms
  apply -
  apply(case_tac \<open>get_parent T c\<close>; case_tac \<open>hm.lookup c t\<close>)
  apply force
  apply(frule get_parent_refinement_None1, force, force, force)
  apply(case_tac a, clarify, frule get_parent_refinement_Some1, force, force, force)
  apply(case_tac a, case_tac aa, clarify)
  apply(frule get_parent_refinement_Some2, force, force, force)
done

lemma set_member_refine:
  assumes \<open>(p, m, c) \<in> T\<close>
    and \<open>t \<preceq> T\<close>
  shows \<open>hm.lookup c t = Some (m, p)\<close>
using assms by blast

lemma ancestor_alt_simp1:
  fixes t :: \<open>('n::{hashable}, 'm \<times> 'n) hm\<close>
  assumes \<open>ancestor_alt T p c\<close> and \<open>t \<preceq> T\<close> and \<open>unique_parent T\<close>
    shows \<open>(case hm.lookup c t of
              None \<Rightarrow> False
            | Some (m, a) \<Rightarrow>
                a = p \<or> ancestor_alt T p a)\<close>
using assms
  apply(induction rule: ancestor_alt.induct)
  apply(drule get_parent_refinement_Some1)
  apply force
  apply force
  apply simp
  apply clarsimp
  apply(drule get_parent_SomeD)
  apply force
  apply(erule weak_refinesE)
  apply(erule_tac x=p in meta_allE, erule_tac x=m in meta_allE, erule_tac x=c in meta_allE, erule meta_impE, assumption) back
  apply clarsimp
  done

lemma ancestor_alt_simp2:
  assumes \<open>(case hm.lookup c t of
              None \<Rightarrow> False
            | Some (m, a) \<Rightarrow>
                a = p \<or> ancestor_alt T p a)\<close>
    and \<open>t \<preceq> T\<close> and \<open>unique_parent T\<close>
  shows \<open>ancestor_alt T p c\<close>
using assms
  apply(clarsimp split: option.split_asm)
  apply(erule weak_refinesE)
  apply(erule_tac x=b in meta_allE, erule_tac x=a in meta_allE, erule_tac x=c in meta_allE, erule_tac meta_impE, assumption)
  apply(erule disjE)
  apply clarsimp
  apply(rule ancestor_alt.intros(1))
  apply(rule get_parent_SomeI, force, force)
  apply(rule ancestor_alt.intros(2))
  apply(rule get_parent_SomeI, force, force, force)
  done

theorem ancestor_alt_simp [simp]:
  fixes t :: \<open>('n::{hashable}, 'm \<times> 'n) hm\<close>
  assumes \<open>t \<preceq> T\<close> and \<open>unique_parent T\<close>
  shows \<open>ancestor_alt T p c \<longleftrightarrow>
           (case hm.lookup c t of
              None \<Rightarrow> False
            | Some (m, a) \<Rightarrow>
                a = p \<or> ancestor_alt T p a)\<close>
using assms ancestor_alt_simp1 ancestor_alt_simp2 by blast

definition flip_triples :: \<open>('a \<times> 'b \<times> 'a) list \<Rightarrow> ('a \<times> 'b \<times> 'a) list\<close>
  where \<open>flip_triples xs \<equiv> map (\<lambda>(x, y, z). (z, y, x)) xs\<close>

definition efficient_ancestor :: \<open>('n::{hashable}, 'm \<times> 'n) hm \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool\<close>
  where \<open>efficient_ancestor t p c \<longleftrightarrow> ancestor_alt (set (flip_triples (hm.to_list t))) p c\<close>

lemma to_list_refines:
  shows \<open>t \<preceq> set (flip_triples (hm.to_list t))\<close>
proof
  fix p m c
  assume *: \<open>hm.lookup c t = Some (m, p)\<close>
  have \<open>hm_invar t\<close>
    by auto
  from this have \<open>map_of (hm.to_list t) = hm.\<alpha> t\<close>
    by(auto simp add: hm.to_list_correct)
  moreover from this have \<open>map_of (hm.to_list t) c = Some (m, p)\<close>
    using * by(clarsimp simp add: hm.lookup_correct)
  from this have \<open>(c, m, p) \<in> set (hm.to_list t)\<close>
    using map_of_SomeD by metis
  from this show \<open>(p, m, c) \<in> set (flip_triples (hm.to_list t))\<close>
    by(force simp add: flip_triples_def intro: rev_image_eqI)
next
  fix p m c
  assume \<open>(p, m, c) \<in> set (flip_triples (hm.to_list t))\<close>
  from this have \<open>(c, m, p) \<in> set (hm.to_list t)\<close>
    by(force simp add: flip_triples_def)
  from this have \<open>map_of (hm.to_list t) c = Some (m, p)\<close>
    by (force intro:  map_of_is_SomeI hm.to_list_correct)+
  from this show \<open>hm.lookup c t = Some (m, p)\<close>
    by(auto simp add: hm.to_list_correct hm.lookup_correct)
qed

lemma unique_parent_to_list:
  shows \<open>unique_parent (set (flip_triples (hm.to_list t)))\<close>
apply(unfold unique_parent_def, intro allI impI conjI, elim conjE)
apply(clarsimp simp add: flip_triples_def)
apply(drule map_of_is_SomeI[rotated])+
apply(force simp add: hm.to_list_correct)+
apply(drule map_of_is_SomeI[rotated])+
apply(force simp add: hm.to_list_correct)+
apply(clarsimp simp add: flip_triples_def)
apply(drule map_of_is_SomeI[rotated])+
apply(force simp add: hm.to_list_correct)+
apply(drule map_of_is_SomeI[rotated])+
apply(force simp add: hm.to_list_correct)+
done

theorem efficient_ancestor_simp [code]:
  shows \<open>efficient_ancestor t p c \<longleftrightarrow>
          (case hm.lookup c t of
              None \<Rightarrow> False
            | Some (m, a) \<Rightarrow>
                a = p \<or> efficient_ancestor t p a)\<close>
  apply(unfold efficient_ancestor_def)
  apply(subst ancestor_alt_simp)
  apply(rule to_list_refines)
  apply(rule unique_parent_to_list)
  apply force
  done

fun efficient_do_op :: \<open>('t, 'n, 'm) operation \<times> ('n::{hashable}, 'm \<times> 'n) hm \<Rightarrow>
        ('t, 'n, 'm) log_op \<times> ('n::{hashable}, 'm \<times> 'n) hm\<close>
  where \<open>efficient_do_op (Move t newp m c, tree) =
           (LogMove t (map_option (\<lambda>x. (snd x, fst x)) (hm.lookup c tree)) newp m c,
              if efficient_ancestor tree c newp \<or> c = newp then tree
                else hm.update c (m, newp) (hm.restrict (\<lambda>(c', m', p'). c \<noteq> c') tree))\<close>

fun efficient_undo_op :: \<open>('t, 'n, 'm) log_op \<times> ('n::{hashable}, 'm \<times> 'n) hm \<Rightarrow> ('n, 'm \<times> 'n) hm\<close>
  where \<open>efficient_undo_op (LogMove t None newp m c, tree) =
          hm.restrict (\<lambda>(c', m', p'). c' \<noteq> c) tree\<close>
      | \<open>efficient_undo_op (LogMove t (Some (oldp, oldm)) newp m c, tree) =
          hm.update c (oldm, oldp) (hm.restrict (\<lambda>(c', m', p'). c' \<noteq> c) tree)\<close>

fun efficient_redo_op :: \<open>('t, 'n, 'm) log_op \<Rightarrow>
            ('t, 'n, 'm) log_op list \<times> ('n::{hashable}, 'm \<times> 'n) hm \<Rightarrow>
            ('t, 'n, 'm) log_op list \<times> ('n, 'm \<times> 'n) hm\<close>
  where \<open>efficient_redo_op (LogMove t _ p m c) (ops, tree) =
          (let (op2, tree2) = efficient_do_op (Move t p m c, tree) in
             (op2#ops, tree2))\<close>

fun efficient_apply_op :: \<open>('t::{linorder}, 'n, 'm) operation \<Rightarrow>
              ('t, 'n, 'm) log_op list \<times> ('n::{hashable}, 'm \<times> 'n) hm \<Rightarrow>
            ('t, 'n, 'm) log_op list \<times> ('n, 'm \<times> 'n) hm\<close>
  where \<open>efficient_apply_op op1 ([], tree1) =
          (let (op2, tree2) = efficient_do_op (op1, tree1)
            in ([op2], tree2))\<close>
      | \<open>efficient_apply_op op1 (logop#ops, tree1) =
          (if move_time op1 < log_time logop
            then efficient_redo_op logop (efficient_apply_op op1 (ops, efficient_undo_op (logop, tree1)))
              else let (op2, tree2) = efficient_do_op (op1, tree1) in (op2 # logop # ops, tree2))\<close>

definition efficient_apply_ops :: \<open>('t::{linorder}, 'n::{hashable}, 'm) operation list \<Rightarrow>
        ('t, 'n, 'm) log_op list \<times> ('n::{hashable}, 'm \<times> 'n) hm\<close>
  where \<open>efficient_apply_ops ops \<equiv>
      foldl (\<lambda>state oper. efficient_apply_op oper state) ([], (hm.empty ())) ops\<close>

text\<open>Any abstract set that is simulated by a hash-map must necessarily have the
     @{term unique_parent} property:\<close>
lemma refines_unique_parent:
  assumes \<open>t \<preceq> T\<close> shows \<open>unique_parent T\<close>
using assms unfolding unique_parent_def
proof(intro allI impI, elim conjE)
  fix p1 p2 m1 m2 c
  assume \<open>(p1, m1, c) \<in> T\<close> and \<open>(p2, m2, c) \<in> T\<close>
  from this have \<open>hm.lookup c t = Some (m1, p1)\<close> and \<open>hm.lookup c t = Some (m2, p2)\<close>
    using assms by(auto simp add: refines_def)
  from this show \<open>p1 = p2 \<and> m1 = m2\<close>
    by force
qed

lemma hm_restrict_refine:
  assumes \<open>t \<preceq> T\<close> and \<open>S = { x\<in>T. (P \<circ> (\<lambda>(x, y, z). (z, y, x))) x }\<close>
  shows \<open>hm.restrict P t \<preceq> S\<close>
using assms
  apply -
  apply(subgoal_tac \<open>unique_parent T\<close>)
prefer 2
  apply(force intro: refines_unique_parent)
  apply(erule refinesE)
  apply(intro refinesI)
  apply(clarsimp simp add: hm.lookup_correct hm.restrict_correct restrict_map_def split!: if_split_asm)
  apply(force simp add: unique_parent_def)
  apply(force simp add: hm.lookup_correct hm.restrict_correct restrict_map_def split!: if_split)
  done

lemma hm_update_refine:
  assumes \<open>t \<preceq> T\<close> and \<open>S = { (p, m, c) \<in> T. c\<noteq>x } \<union> {(z, y, x)}\<close>
  shows \<open>hm.update x (y, z) t \<preceq> S\<close>
using assms
  apply -
  apply(subgoal_tac \<open>unique_parent T\<close>)
prefer 2
  apply(force intro: refines_unique_parent)
  apply(erule refinesE)
  apply(rule refinesI)
  apply(clarsimp simp add: hm.update_correct hm.lookup_correct split: if_split_asm)
  apply clarsimp
  apply(erule disjE)
  apply(clarsimp simp add: hm.lookup_correct hm.update_correct)+
  done

lemma if_refine:
  assumes \<open>x \<Longrightarrow> t \<preceq> T\<close> and \<open>\<not> x \<Longrightarrow> u \<preceq> U\<close> and \<open>x \<longleftrightarrow> y\<close>
  shows \<open>(if x then t else u) \<preceq> (if y then T else U)\<close>
using assms by(case_tac x; clarsimp)

text\<open>The @{term ancestor} relation can be extended ``one step downwards'' using @{term get_parent}:\<close>
lemma ancestor_get_parent_extend:
  assumes \<open>ancestor T a p\<close> and \<open>unique_parent T\<close>
    and \<open>get_parent T c = Some (p, m)\<close>
  shows \<open>ancestor T a c\<close>
using assms proof(induction arbitrary: c m rule: ancestor.induct)
  case (1 parent meta child tree)
  assume 1: \<open>(parent, meta, child) \<in> tree\<close> and \<open>unique_parent tree\<close>
    and \<open>get_parent tree c = Some (child, m)\<close>
  from this have \<open>(child, m, c) \<in> tree\<close>
    by(force simp add: unique_parent_def dest: get_parent_SomeD)
  from this and 1 show ?case
    by(blast intro: ancestor.intros)
next
  case (2 parent meta child tree anc)
  assume 1: \<open>(parent, meta, child) \<in> tree\<close> and 2: \<open>unique_parent tree\<close>
    and \<open>get_parent tree c = Some (child, m)\<close>
    and IH: \<open>\<And>c m. unique_parent tree \<Longrightarrow> get_parent tree c = Some (parent, m) \<Longrightarrow> ancestor tree anc c\<close>
  from this have \<open>(child, m, c) \<in> tree\<close>
    by(force dest: get_parent_SomeD)
  from this and 1 and 2 and IH show ?case
    by(blast intro: ancestor.intros(2) IH get_parent_SomeI)
qed

text\<open>The efficient and abstract @{term ancestor} relations agree for all ancestry queries between a
     prospective ancestor and child node when applied to related states:\<close>
lemma efficient_ancestor_refines:
  assumes \<open>t \<preceq> T\<close>
  shows \<open>efficient_ancestor t p c = ancestor T p c\<close>
using assms proof(intro iffI)
  assume 1: \<open>efficient_ancestor t p c\<close>
    and 2: \<open>t \<preceq> T\<close>
  obtain u where 3: \<open>u = set (flip_triples (hm.to_list t))\<close>
    by force
  from this and 1 have \<open>ancestor_alt u p c\<close>
    by(force simp add: efficient_ancestor_def)
  from this and 2 and 3 show \<open>ancestor T p c\<close>
  proof(induction rule: ancestor_alt.induct)
    case (1 T' c p m)
    assume \<open>get_parent T' c = Some (p, m)\<close> and \<open>T' = set (flip_triples (hm.to_list t))\<close>
    from this have \<open>(p, m, c) \<in> set (flip_triples (hm.to_list t))\<close>
      by(force dest: get_parent_SomeD intro: unique_parent_to_list)
    from this have \<open>(p, m, c) \<in> T\<close>
      using \<open>t \<preceq> T\<close> by(force simp add: hm.correct hm.to_list_correct refines_def
                flip_triples_def dest: map_of_is_SomeI[rotated])
    then show ?case
      by(force intro: ancestor.intros)
  next
    case (2 T' c p m a)
    assume 1: \<open>get_parent T' c = Some (p, m)\<close>
      and IH: \<open>t \<preceq> T \<Longrightarrow> T' = set (flip_triples (hm.to_list t)) \<Longrightarrow> ancestor T a p\<close>
      and 2: \<open>t \<preceq> T\<close> and 3: \<open>T' = set (flip_triples (hm.to_list t))\<close>
    from this have 4: \<open>ancestor T a p\<close>
      by auto
    from this have \<open>(p, m, c) \<in> set (flip_triples (hm.to_list t))\<close>
      using 1 and 3 by(auto dest!: get_parent_SomeD simp add: unique_parent_to_list)
    from this have \<open>(c, m, p) \<in> set (hm.to_list t)\<close>
      by(auto simp add: flip_triples_def)
    from this and 2 have \<open>get_parent T c = Some (p, m)\<close>
      by(auto intro!: get_parent_SomeI refines_unique_parent[OF 2]
          simp add: hm.correct hm.to_list_correct dest!: map_of_is_SomeI[rotated])
    from this and 2 and 4 show ?case
      by(auto intro!: ancestor_get_parent_extend[OF 4] refines_unique_parent)
  qed
next
  assume \<open>ancestor T p c\<close> and \<open>t \<preceq> T\<close> 
  from this show \<open>efficient_ancestor t p c\<close>
    by(induction rule: ancestor.induct) (force simp add: efficient_ancestor_simp)+
qed

lemma efficient_do_op_get_parent_technical:
  assumes \<open>t \<preceq> T\<close>
  shows \<open>map_option (\<lambda>x. (snd x, fst x)) (hm.lookup c t) = get_parent T c\<close>
using assms
  apply(subgoal_tac \<open>unique_parent T\<close>)
prefer 2
  apply(force intro: refines_unique_parent)
  apply(case_tac \<open>get_parent T c\<close>; case_tac \<open>hm.lookup c t\<close>; clarsimp) 
  apply(clarsimp simp add: refines_def)
  apply(drule get_parent_NoneD, force, force, force)
  apply(clarsimp simp add: refines_def)
  apply(drule get_parent_SomeD, force, force)
  apply(drule get_parent_SomeD, force, force simp add: unique_parent_def refines_def)
  done

text\<open>The @{term unique_parent} predicate is ``downward-closed'' in the sense that all subsets of a
     set with the @{term unique_parent} property also possess this property:\<close>
lemma unique_parent_downward_closure:
  assumes \<open>unique_parent T\<close>
    and \<open>S \<subseteq> T\<close>
  shows \<open>unique_parent S\<close>
using assms by(force simp add: unique_parent_def)

lemma efficient_do_op_refines:
  assumes \<open>t \<preceq> T\<close>
    and \<open>efficient_do_op (oper, t) = (log1, u)\<close>
    and \<open>do_op (oper, T) = (log2, U)\<close>
  shows \<open>log1 = log2 \<and> u \<preceq> U\<close>
using assms
  apply -
  apply(subgoal_tac \<open>unique_parent T\<close>)
prefer 2
  apply(force intro: refines_unique_parent)
  apply(case_tac oper; clarify)
  apply(unfold efficient_do_op.simps, unfold do_op.simps)
  apply(simp only: prod.simps, elim conjE, clarify)
  apply(intro conjI)
  apply(simp only: log_op.simps)
  apply(intro conjI, force)
  apply(rule efficient_do_op_get_parent_technical, force, force)
  apply force
  apply force
  apply(rule if_refine)
  apply force
  apply(rule_tac T=\<open>{(p', m', c'). (p', m', c') \<in> T \<and> c' \<noteq> x4}\<close> in hm_update_refine)
  apply(rule hm_restrict_refine, assumption, force)
  apply force
  apply(subst efficient_ancestor_refines, force, force)
  done

text\<open>The efficient and abstract @{term redo_op} functins take related concrete and abstract states
     and produce identical logics and related concrete and abstract states:\<close>
lemma efficient_redo_op_refines:
  assumes 1: \<open>t \<preceq> T\<close>
    and 2: \<open>efficient_redo_op oper (opers, t) = (log1, u)\<close>
    and 3: \<open>redo_op oper (opers, T) = (log2, U)\<close>
  shows \<open>log1 = log2 \<and> u \<preceq> U\<close>
proof(cases oper)
  case (LogMove time opt_old_parent new_parent meta child)
    assume 4: \<open>oper = LogMove time opt_old_parent new_parent meta child\<close>
    obtain entry1 and v where \<open>efficient_do_op (Move time new_parent meta child, t) = (entry1, v)\<close>
      by auto
    moreover obtain entry2 and V where \<open>do_op (Move time new_parent meta child, T) = (entry2, V)\<close>
      by auto
    moreover have 5: \<open>entry1 = entry2\<close> and 6: \<open>v \<preceq> V\<close>
      using calculation efficient_do_op_refines[OF 1] by blast+
    from 4 have \<open>efficient_redo_op oper (opers, t) = (entry1#opers, v)\<close>
      using calculation by clarsimp
    moreover have \<open>log1 = entry1#opers\<close> and \<open>u = v\<close>
      using 2 calculation by auto
    moreover from 4 have \<open>redo_op oper (opers, T) = (entry2#opers, V)\<close>
      using calculation by simp
    moreover have \<open>log2 = entry2#opers\<close> and \<open>U = V\<close>
      using 3 calculation by auto
    ultimately show \<open>?thesis\<close>
      using 5 6 by metis
qed

text\<open>The efficient and abstract versions of @{term undo_op} map related concrete and abstract states
     to related concrete and abstract states when applied to the same operation:\<close>
lemma efficient_undo_op_refines:
  assumes 1: \<open>t \<preceq> T\<close>
  shows \<open>efficient_undo_op (oper, t) \<preceq> undo_op (oper, T)\<close>
using assms proof(cases \<open>oper\<close>)           
  case (LogMove time opt_old_parent new_parent meta child)
    assume 2: \<open>oper = LogMove time opt_old_parent new_parent meta child\<close>
    {
      assume \<open>opt_old_parent = None\<close>
      from this and 2 have 3: \<open>oper = LogMove time None new_parent meta child\<close>
        by simp
      moreover from this have \<open>efficient_undo_op (oper, t) = hm.restrict (\<lambda>(c, m, p). c \<noteq> child) t\<close>
        by force
      moreover have \<open>... \<preceq> {(p', m', c') \<in> T. c' \<noteq> child}\<close>
        by(rule hm_restrict_refine[OF 1]) auto
      moreover have \<open>... = undo_op (oper, T)\<close>
        using 3 by force
      ultimately have ?thesis
        by metis
    }
    note L = this
    {
      fix old_meta old_parent
      assume \<open>opt_old_parent = Some (old_parent, old_meta)\<close>
      from this and 2 have 3: \<open>oper = LogMove time (Some (old_parent, old_meta)) new_parent meta child\<close>
        by simp
      moreover from this have \<open>efficient_undo_op (oper, t) =
          hm.update child (old_meta, old_parent) (hm.restrict (\<lambda>(c, m, p). c \<noteq> child) t)\<close>
        by auto
      moreover have \<open>... \<preceq> {(p, m, c) \<in> T. c \<noteq> child} \<union> {(old_parent, old_meta, child)}\<close>
        by(rule hm_update_refine, rule hm_restrict_refine[OF 1], force, force)
      moreover have \<open>... = undo_op (oper, T)\<close>
        using 3 by auto
      ultimately have ?thesis
        by metis
    }
    from this and L show \<open>?thesis\<close>
      by(cases opt_old_parent) force+
qed

text\<open>The efficient and abstract @{term apply_op} algorithms map related concrete and abstract
     states to related concrete and abstract states when applied to the same operation and input
     log, and also produce identical output logs:\<close>
lemma efficient_apply_op_refines:
  assumes \<open>t \<preceq> T\<close>
    and \<open>efficient_apply_op oper (log, t) = (log1, u)\<close>
    and \<open>apply_op oper (log, T) = (log2, U)\<close>
  shows \<open>log1 = log2 \<and> u \<preceq> U\<close>
using assms proof(induction log arbitrary: T t log1 log2 u U)
  case Nil
  assume 1: \<open>t \<preceq> T\<close> and 2: \<open>efficient_apply_op oper ([], t) = (log1, u)\<close>
    and 3: \<open>apply_op oper ([], T) = (log2, U)\<close>
  obtain action1 action2 t' T' where 4: \<open>efficient_do_op (oper, t) = (action1, t')\<close>
      and 5: \<open>do_op (oper, T) = (action2, T')\<close>
    by fastforce
  moreover from 4 and 5 have \<open>action1 = action2\<close> and \<open>t' \<preceq> T'\<close>
    using efficient_do_op_refines[OF 1] by blast+
  moreover from 2 and 4 have \<open>log1 = [action1]\<close> and \<open>u = t'\<close>
    by auto
  moreover from 3 and 5 have \<open>log2 = [action2]\<close> and \<open>U = T'\<close>
    by auto
  ultimately show ?case
    by auto
next
  case (Cons logop logops)
  assume 1: \<open>t \<preceq> T\<close> and 2: \<open>efficient_apply_op oper (logop # logops, t) = (log1, u)\<close>
    and 3: \<open>apply_op oper (logop # logops, T) = (log2, U)\<close>
    and IH: \<open>(\<And>T t log1 log2 u U. t \<preceq> T \<Longrightarrow> efficient_apply_op oper (logops, t) = (log1, u) \<Longrightarrow>
                apply_op oper (logops, T) = (log2, U) \<Longrightarrow> log1 = log2 \<and> u \<preceq> U)\<close>
  {
    assume 4: \<open>move_time oper < log_time logop\<close>
    obtain action1 and action1' and u' and u'' and u''' where 5: \<open>efficient_undo_op (logop, t) = u'\<close> and
        6: \<open>efficient_apply_op oper (logops, u') = (action1, u'')\<close> and
          7: \<open>efficient_redo_op logop (action1, u'') = (action1', u''')\<close>
      by force
    obtain action2 and action2' and U' and U'' and U''' where 8: \<open>undo_op (logop, T) = U'\<close> and
        9: \<open>apply_op oper (logops, U') = (action2, U'')\<close> and
          10: \<open>redo_op logop (action2, U'') = (action2', U''')\<close>
      by force
    from 5 and 8 have \<open>u' \<preceq> U'\<close>
      using efficient_undo_op_refines[OF 1] by blast
    moreover from 6 and 9 have \<open>action1 = action2\<close> and \<open>u'' \<preceq> U''\<close>
      using IH[OF \<open>u' \<preceq> U'\<close>] by blast+
    moreover from this and 7 and 10 have \<open>action1' = action2'\<close> and \<open>u''' \<preceq> U'''\<close>
      using efficient_redo_op_refines by blast+
    moreover from 2 and 4 and 5 and 6 and 7 have \<open>log1 = action1'\<close> and \<open>u = u'''\<close>
      by auto
    moreover from 3 and 4 and 8 and 9 and 10 have \<open>log2 = action2'\<close> and \<open>U = U'''\<close>
      by auto
    ultimately have ?case
      by auto
  }
  note L = this
  {
    assume 4: \<open>\<not> (move_time oper < log_time logop)\<close>
    obtain action1 action2 u' U' where 5: \<open>efficient_do_op (oper, t) = (action1, u')\<close>
        and 6: \<open>do_op (oper, T) = (action2, U')\<close>
      by fastforce
    from this have \<open>action1 = action2\<close> and \<open>u' \<preceq> U'\<close>
      using efficient_do_op_refines[OF 1] by blast+
    moreover from 2 and 4 and 5 have \<open>log1 = action1#logop#logops\<close> and \<open>u' = u\<close>
      by auto
    moreover from 3 and 4 and 6 have \<open>log2 = action2#logop#logops\<close> and \<open>U' = U\<close>
      by auto
    ultimately have ?case
      using 1 by simp
  }
  from this and L show ?case
    by auto
qed

text\<open>The internal workings of abstract and concrete implementations of the @{term apply_ops}
     function map related states to related states, and produce identical logs, when passed
     identical lists of actions to perform.

     Note this lemma is necessary as the @{term apply_ops} function specifies a particular starting
     state (the empty state) to start the iterated application of the @{term apply_op} function
     from, meaning that an inductive proof using this definition directly becomes impossible, as the
     inductive hypothesis will be over constrained in the step case.  By introducing this lemma, we
     show that the required property holds for any starting states (as long as they are related by
     the simulation relation) and then specialise to the empty starting state in the next lemma,
     below.\<close>
lemma efficient_apply_ops_refines_internal:
  assumes \<open>foldl (\<lambda>state oper. efficient_apply_op oper state) (log, t) xs = (log1, u)\<close>
    and \<open>foldl (\<lambda>state oper. apply_op oper state) (log, T) xs = (log2, U)\<close>
    and \<open>t \<preceq> T\<close>
  shows \<open>log1 = log2 \<and> u \<preceq> U\<close>
using assms proof(induction xs arbitrary: log log1 log2 t T u U)
  case Nil
  assume \<open>foldl (\<lambda>state oper. efficient_apply_op oper state) (log, t) [] = (log1, u)\<close>
    and \<open>apply_ops' [] (log, T) = (log2, U)\<close>
    and *: \<open>t \<preceq> T\<close>
  from this have \<open>log = log2\<close> and \<open>T = U\<close> and \<open>log = log1\<close> and \<open>t = u\<close>
    by auto
  from this show \<open>log1 = log2 \<and> u \<preceq> U\<close>
    using * by auto
next
  case (Cons x xs)
  fix xs :: \<open>('a, 'b, 'c) operation list\<close> and x log log1 log2 t T u U
  assume IH: \<open>\<And>log log1 log2 t T u U.
           foldl (\<lambda>state oper. efficient_apply_op oper state) (log, t) xs = (log1, u) \<Longrightarrow>
           apply_ops' xs (log, T) = (log2, U) \<Longrightarrow> t \<preceq> T \<Longrightarrow> log1 = log2 \<and> u \<preceq> U\<close>
    and 1: \<open>foldl (\<lambda>state oper. efficient_apply_op oper state) (log, t) (x#xs) = (log1, u)\<close>
    and 2: \<open>apply_ops' (x#xs) (log, T) = (log2, U)\<close>
    and 3: \<open>t \<preceq> T\<close>
  obtain log1' log2' U' u' where 4: \<open>efficient_apply_op x (log, t) = (log1', u')\<close>
      and 5: \<open>apply_op x (log, T) = (log2', U')\<close>
    by fastforce
  moreover from this have \<open>log1' = log2'\<close> and \<open>u' \<preceq> U'\<close>
    using efficient_apply_op_refines[OF 3] by blast+
  moreover have \<open>foldl (\<lambda>state oper. efficient_apply_op oper state) (log1', u') xs = (log1, u)\<close>
    using 1 and 4 by simp
  moreover have \<open>apply_ops' xs (log2', U') = (log2, U)\<close>
    using 2 and 5 by simp
  ultimately show \<open>log1 = log2 \<and> u \<preceq> U\<close>
    by(auto simp add: IH)
qed

text\<open>The efficient and abstract versions of @{term apply_ops} produce identical operation logs and
     produce related concrete and abstract states:\<close>
lemma efficient_apply_ops_refines:
  assumes 1: \<open>efficient_apply_ops opers = (log1, u)\<close>
    and 2: \<open>apply_ops opers = (log2, U)\<close>
  shows \<open>log1 = log2 \<and> u \<preceq> U\<close>
proof -
  have \<open>hm.empty () \<preceq> {}\<close>
    by auto
  moreover have \<open>foldl (\<lambda>state oper. efficient_apply_op oper state) ([], hm.empty ()) opers = (log1, u)\<close>
    using 1 by(auto simp add: efficient_apply_ops_def)
  moreover have \<open>foldl (\<lambda>state oper. apply_op oper state) ([], {}) opers = (log2, U)\<close>
    using 2 by(auto simp add: apply_ops_def)
  moreover have \<open>log1 = log2\<close> and \<open>u \<preceq> U\<close>
    using calculation efficient_apply_ops_refines_internal by blast+
  ultimately show \<open>?thesis\<close>
    by auto
qed

text\<open>The main correctness theorem for the efficient algorithms.  This follows the
     @{thm apply_ops_commutes} theorem for the abstract algorithms with one significant difference:
     the states obtained from applyreting the two lists of operations, @{term ops1} and
     @{term ops2}, are no longer identical (the hash-maps may have a different representation in
     memory, for instance), but contain the same set of key-value bindings.  If we take equality of
     finite maps (hash-maps included) to be extensional---i.e. two finite maps are equal when they
     contain the same key-value bindings---then this theorem coincides exactly with the
     @{thm apply_ops_commutes}:\<close>
theorem efficient_apply_ops_commutes:
  assumes 1: \<open>set ops1 = set ops2\<close>
    and 2: \<open>distinct (map move_time ops1)\<close>
    and 3: \<open>distinct (map move_time ops2)\<close>
    and 4: \<open>efficient_apply_ops ops1 = (log1, t)\<close>
    and 5: \<open>efficient_apply_ops ops2 = (log2, u)\<close>
  shows \<open>log1 = log2 \<and> hm.lookup c t = hm.lookup c u\<close>
proof -
  from 1 2 3 have \<open>apply_ops ops1 = apply_ops ops2\<close>
    using apply_ops_commutes by auto
  from this obtain log1' log2' T U where 6: \<open>apply_ops ops1 = (log1', T)\<close>
      and 7: \<open>apply_ops ops2 = (log2', U)\<close> and 8: \<open>log1' = log2'\<close> and 9: \<open>T = U\<close>
    by fastforce
  moreover from 4 5 6 7 have \<open>log1 = log1'\<close> and \<open>log2 = log2'\<close> and \<open>t \<preceq> T\<close> and \<open>u \<preceq> U\<close>
    using efficient_apply_ops_refines by force+
  moreover from 8 have \<open>log1 = log2\<close>
    by(simp add: calculation)
  moreover have \<open>hm.lookup c t = hm.lookup c u\<close>
    using calculation by(cases \<open>hm.lookup c t\<close>; cases \<open>hm.lookup c u\<close>) (force simp add: refines_def)+
  ultimately show \<open>?thesis\<close>
    by auto
qed

subsection\<open>Testing code generation\<close>

text\<open>Check that all of the efficient algorithms produce executable code for all of Isabelle/HOL's
     code generation targets (Standard ML, Scala, OCaml, Haskell).  Note that the Isabelle code
     generation mechanism recursively extracts all necessary material from the HOL library required
     to successfully compile our own definitions, here.  As a result, the first section of each
     extraction is material extracted from the Isabelle libraries---our material is towards the
     bottom.  (View it in the Output buffer of the Isabelle/JEdit IDE.)\<close>

export_code efficient_ancestor efficient_do_op efficient_undo_op efficient_redo_op
  efficient_apply_op efficient_apply_ops in SML
export_code efficient_ancestor efficient_do_op efficient_undo_op efficient_redo_op
  efficient_apply_op efficient_apply_ops in Scala
export_code efficient_ancestor efficient_do_op efficient_undo_op efficient_redo_op
  efficient_apply_op efficient_apply_ops in OCaml
export_code efficient_ancestor efficient_do_op efficient_undo_op efficient_redo_op
  efficient_apply_op efficient_apply_ops in Haskell

text\<open>Without resorting to saving the generated code above to a separate file and feeding them into
     an SML/Scala/OCaml/Haskell compiler, as appropriate, we can show that this code compiles and
     executes relatively quickly from within Isabelle itself, by making use of Isabelle's
     quotations/anti-quotations, and its tight coupling with the underlying PolyML process.

     First define a @{term unit_test} definition that makes use of our @{term efficient_apply_ops}
     function on a variety of inputs:\<close>

definition unit_test :: \<open>((nat, nat, nat) log_op list \<times> (nat, nat \<times> nat) HashMap.hashmap) list\<close>
  where \<open>unit_test \<equiv>
          [ efficient_apply_ops []
          , efficient_apply_ops [Move 1 0 0 0]
          , efficient_apply_ops [Move 1 0 0 0, Move 3 2 2 2, Move 2 1 1 1]
          ]\<close>

text\<open>Then, we can use @{command ML_val} to ask Isabelle to:
      \<^enum> Generate executable code for our @{term unit_test} definition above, using the SML code
        generation target,
      \<^enum> Execute this code within the underlying Isabelle/ML process, and display the resulting SML
        values back to us within the Isabelle/JEdit IDE.\<close>

ML_val\<open>@{code unit_test}\<close>

text\<open>Note, there is a slight lag when performing this action as the executable code is first
     extracted to SML, dynamically compiled, and then the result of the computation reflected back
     to us.  Nevertheless, on a Macbook Pro (2017 edition) this procedure takes 2 seconds, at the
     most.\<close>
end
