theory Move
  imports Main
begin

section \<open>Definitions\<close>

datatype ('time, 'node) operation
  = Move (move_time: 'time) (move_parent: 'node) (move_child: 'node)

datatype ('time, 'node) log_op
  = LogMove (log_time: 'time) (old_parent: \<open>'node option\<close>) (new_parent: 'node) (log_child: 'node)

type_synonym ('t, 'n) state = \<open>('t, 'n) log_op list \<times> ('n \<times> 'n) set\<close>

(*
datatype 'node tree   
  = Node 'node \<open>'node tree fset\<close>
*)

definition get_parent :: \<open>('n \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> 'n option\<close> where
  \<open>get_parent tree child \<equiv>
     if \<exists>!parent. (parent, child) \<in> tree then
       Some (THE parent. (parent, child) \<in> tree)
     else None\<close>

inductive ancestor :: "('n \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool" where
  "\<lbrakk>(parent, child) \<in> tree\<rbrakk> \<Longrightarrow> ancestor tree parent child" |
  "\<lbrakk>(parent, child) \<in> tree; ancestor tree anc parent\<rbrakk> \<Longrightarrow> ancestor tree anc child"

fun do_op :: \<open>('t, 'n) operation \<times> ('n \<times> 'n) set \<Rightarrow> ('t, 'n) log_op \<times> ('n \<times> 'n) set\<close> where
  \<open>do_op (Move t newp c, tree) =
     (LogMove t (get_parent tree c) newp c,
      if ancestor tree c newp \<or> c = newp then tree
      else {(p', c') \<in> tree. c' \<noteq> c} \<union> {(newp, c)})\<close>

fun undo_op :: \<open>('t, 'n) log_op \<times> ('n \<times> 'n) set \<Rightarrow> ('n \<times> 'n) set\<close> where
  \<open>undo_op (LogMove t None newp c, tree) = {(p', c') \<in> tree. c' \<noteq> c}\<close> |
  \<open>undo_op (LogMove t (Some oldp) newp c, tree) =
     {(p', c') \<in> tree. c' \<noteq> c} \<union> {(oldp, c)}\<close>

fun redo_op :: \<open>('t, 'n) log_op \<Rightarrow> ('t, 'n) state \<Rightarrow> ('t, 'n) state\<close> where
  \<open>redo_op (LogMove t _ p c) (ops, tree) =
     (let (op2, tree2) = do_op (Move t p c, tree)
      in (op2 # ops, tree2))\<close>

fun interp_op :: \<open>('t::{linorder}, 'n) operation \<Rightarrow> ('t, 'n) state \<Rightarrow> ('t, 'n) state\<close> where
  \<open>interp_op op1 ([], tree1) =
     (let (op2, tree2) = do_op (op1, tree1)
      in ([op2], tree2))\<close> |
  \<open>interp_op op1 (logop # ops, tree1) =
     (if move_time op1 < log_time logop
      then redo_op logop (interp_op op1 (ops, undo_op (logop, tree1)))
      else let (op2, tree2) = do_op (op1, tree1) in (op2 # ops, tree2))\<close>

definition interp_ops :: \<open>('t::{linorder}, 'n) operation list \<Rightarrow> ('t, 'n) log_op list \<times> ('n \<times> 'n) set\<close> where
  \<open>interp_ops ops \<equiv> foldl (\<lambda>state oper. interp_op oper state) ([], {}) ops\<close>


section \<open>undo_op is the inverse of do_op\<close>

lemma get_parent_None:
  assumes \<open>\<nexists>p. (p, c) \<in> tree\<close>
  shows \<open>get_parent tree c = None\<close>
by (meson assms get_parent_def)

lemma get_parent_Some:
  assumes \<open>(p, c) \<in> tree\<close>
    and \<open>\<And>x. (x, c) \<in> tree \<Longrightarrow> x = p\<close>
  shows \<open>get_parent tree c = Some p\<close>
proof -
  have \<open>\<exists>!parent. (parent, c) \<in> tree\<close>
    using assms by metis
  hence \<open>(THE parent. (parent, c) \<in> tree) = p\<close>
    using assms(2) by fastforce
  thus \<open>get_parent tree c = Some p\<close>
    using assms get_parent_def by metis
qed

lemma do_undo_op_inv:
  assumes \<open>\<And>x. (x, c) \<in> tree \<Longrightarrow> x = oldp\<close>
  shows \<open>undo_op (do_op (Move t p c, tree)) = tree\<close>
proof(cases \<open>\<exists>par. (par, c) \<in> tree\<close>)
  case True
  hence 1: \<open>(oldp, c) \<in> tree\<close>
    using assms by blast
  hence 2: \<open>get_parent tree c = Some oldp\<close>
    using assms get_parent_Some by metis
  moreover have \<open>\<And>p' c'. (p', c') \<in> tree \<Longrightarrow> (p', c') \<in> undo_op (do_op (Move t p c, tree))\<close>
    using assms calculation by auto
  moreover have \<open>\<And>p' c'. (p', c') \<in> undo_op (do_op (Move t p c, tree)) \<Longrightarrow> (p', c') \<in> tree\<close>
    using 1 2 by (cases \<open>ancestor tree c p \<or> c = p\<close>, auto)
  ultimately show ?thesis
    by (meson pred_equals_eq2)
next
  case no_old_parent: False
  hence \<open>get_parent tree c = None\<close>
    using assms get_parent_None by metis
  moreover have \<open>{(p', c') \<in> tree. c' \<noteq> c} = tree\<close>
    using no_old_parent by fastforce
  moreover from this have \<open>{(p', c') \<in> (tree \<union> {(p, c)}). c' \<noteq> c} = tree\<close>
    by auto
  ultimately show ?thesis by simp
qed


section \<open>Preserving the invariant that each tree node has at most one parent\<close>

lemma do_op_unique_parent:
  assumes \<open>\<And>p1 p2 c. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2\<close>
    and \<open>do_op (Move t newp c, tree1) = (log_oper, tree2)\<close>
  shows \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
proof(cases \<open>ancestor tree1 c newp \<or> c = newp\<close>)
  case True
  then show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
    using assms by auto
next
  case False
  hence \<open>tree2 = {(p', c') \<in> tree1. c' \<noteq> c} \<union> {(newp, c)}\<close>
    using assms(2) by auto
  then show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
    using assms(1) by auto
qed

lemma undo_op_unique_parent:
  assumes \<open>\<And>p1 p2 c. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2\<close>
    and \<open>undo_op (LogMove t oldp newp c, tree1) = tree2\<close>
  shows \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
using assms by (cases oldp, auto)

lemma redo_op_unique_parent:
  assumes \<open>\<And>p1 p2 c. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2\<close>
    and \<open>redo_op oper (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
proof -
  obtain t oldp newp c where \<open>oper = LogMove t oldp newp c\<close>
    using log_op.exhaust by blast
  from this obtain move2 where \<open>(move2, tree2) = do_op (Move t newp c, tree1)\<close>
    using assms(2) by auto
  thus \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
    by (metis assms(1) do_op_unique_parent)
qed

theorem interp_op_unique_parent:
  assumes \<open>\<And>p1 p2 c. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2\<close>
    and \<open>interp_op oper (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
using assms proof(induct ops1 arbitrary: tree1 tree2 ops2)
  case Nil
  have \<open>\<And>pair. snd (case pair of (p1, p2) \<Rightarrow> ([p1], p2)) = snd pair\<close>
    by (simp add: prod.case_eq_if)
  hence \<open>\<exists>log_op. do_op (oper, tree1) = (log_op, tree2)\<close>
    by (metis Nil.prems(4) interp_op.simps(1) old.prod.exhaust snd_conv)
  thus \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
    by (metis Nil.prems(3) do_op_unique_parent operation.exhaust_sel)
next
  case step: (Cons logop ops)
  then show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
  proof(cases \<open>move_time oper < log_time logop\<close>)
    case True
    moreover obtain tree1a where \<open>tree1a = undo_op (logop, tree1)\<close>
      by simp
    moreover from this have 1: \<open>\<And>p1 p2 c. (p1, c) \<in> tree1a \<Longrightarrow> (p2, c) \<in> tree1a \<Longrightarrow> p1 = p2\<close>
      using undo_op_unique_parent by (metis step.prems(3) log_op.exhaust_sel)
    moreover obtain ops1b tree1b where \<open>(ops1b, tree1b) = interp_op oper (ops, tree1a)\<close>
      by (metis surj_pair)
    moreover from this have \<open>\<And>p1 p2 c. (p1, c) \<in> tree1b \<Longrightarrow> (p2, c) \<in> tree1b \<Longrightarrow> p1 = p2\<close>
      using 1 by (metis step.hyps)
    ultimately show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
      using redo_op_unique_parent by (metis interp_op.simps(2) step.prems(4))
  next
    case False
    hence \<open>snd (do_op (oper, tree1)) = tree2\<close>
      by (metis (mono_tags, lifting) interp_op.simps(2) prod.sel(2) split_beta step.prems(4))
    then show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
      by (metis do_op_unique_parent operation.exhaust_sel prod.exhaust_sel step.prems(3))
  qed
qed


section \<open>Preserving the invariant that the tree contains no cycles\<close>

definition cyclic :: \<open>('n \<times> 'n) set \<Rightarrow> bool\<close>
  where \<open>cyclic \<T> \<longleftrightarrow> (\<exists>n. ancestor \<T> n n)\<close>

lemma cyclicE [elim]:
  assumes \<open>cyclic \<T>\<close>
  and \<open>(\<exists>n. ancestor \<T> n n) \<Longrightarrow> P\<close>
  shows \<open>P\<close>
  using assms by(auto simp add: cyclic_def)

inductive_cases ancestor_indcases: \<open>ancestor \<T> m p\<close>
thm ancestor_indcases

lemma ancestor_superset_closed:
  assumes \<open>ancestor \<T> p c\<close>
    and \<open>\<T> \<subseteq> \<S>\<close>
  shows \<open>ancestor \<S> p c\<close>
  using assms
  by (induction rule: ancestor.induct) (auto intro: ancestor.intros)

lemma acyclic_subset:
  assumes \<open>\<not> cyclic T\<close>
    and \<open>S \<subseteq> T\<close>
  shows \<open>\<not> cyclic S\<close>
  using assms ancestor_superset_closed by (metis cyclic_def)

lemma
  assumes \<open>ancestor T m p\<close>
    and \<open>(m,p) \<notin> T\<close>
  shows \<open>\<exists>n. ancestor T m n \<and> ancestor T n p\<close>
  using ancestor_indcases and assms
  by (meson ancestor.simps)

inductive path :: "('n \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n \<times> 'n) list \<Rightarrow> bool" where
  "\<lbrakk>(b, e) \<in> T\<rbrakk> \<Longrightarrow> path T b e [(b, e)]" |
  "\<lbrakk>path T b m xs; (m, e) \<notin> set xs; (m, e) \<in> T\<rbrakk> \<Longrightarrow> path T b e (xs@[(m, e)])"


inductive_cases path_indcases: \<open>path T b e xs\<close>

lemma empty_path: "\<not> path T x y []"
  apply clarsimp
  apply (erule path_indcases)
   apply force
  apply force
  done

lemma singleton_path: "path T b m [(p, c)] \<Longrightarrow> b = p \<and> m = c"
  by (metis (no_types, lifting) butlast.simps(2) butlast_snoc empty_path list.inject path.cases prod.inject)

lemma path_drop1: "path T b e (xs @ [(a, e)]) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> path T b a xs \<and> (a, e) \<notin> set xs"
  apply (rule conjI)
  using path.cases apply fastforce
  using path.cases by force
  
lemma path_drop: "path T b e (xs @ ys) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> \<exists>m. path T b m xs"
  apply (induct ys arbitrary: xs)
   apply force
  apply (erule_tac x="xs@[a]" in meta_allE)
  apply clarsimp
  using path.cases by force

lemma fst_path: "path T b e ((p, c)#xs) \<Longrightarrow> b = p"
  apply (induct xs arbitrary: e rule: rev_induct)
   apply (simp add: singleton_path)
  apply clarsimp
  apply (subgoal_tac "path T b e (((p, c) # xs) @ [(a, ba)])")
   apply (drule path_drop)
    apply force
   apply force
  apply force
  done

lemma last_path: "path T b e (xs@[(p, c)]) \<Longrightarrow> e = c"
  apply (erule path_indcases)
   apply force
  apply force
  done

lemma path_concat: "path S m n xs \<Longrightarrow> path S n p ys \<Longrightarrow> path S m p (xs@ys)"
  apply (induct ys arbitrary: p rule: rev_induct)
   apply (simp add: empty_path)
  apply (case_tac x)
  apply simp
  apply (subgoal_tac "p = b")
   defer
   apply (simp add: last_path)
  apply (subgoal_tac "path S m p ((xs @ xsa) @ [(a, p)])")
   apply force
  apply (case_tac xsa)
   apply clarsimp
   apply (subgoal_tac "n = aa")
    prefer 2
    apply (simp add: fst_path)
   apply clarsimp
  sorry


lemma path_split: "path T m n xs \<Longrightarrow> (p, c) \<in> set xs \<Longrightarrow> (\<exists>ys zs. (ys = [] \<or> path T m p ys)
                                                      \<and> (zs = [] \<or> path T c n zs)
                                                      \<and> (xs = ys @ [(p, c)] @ zs)
                                                      \<and> (p, c) \<notin> set ys \<and> (p, c) \<notin> set zs)"
  apply (induct rule: path.induct)
   apply force
  apply clarsimp
  apply (elim disjE conjE)
   apply clarsimp
   apply force
  apply clarsimp
  apply (elim disjE conjE)+
     apply clarsimp
     apply (drule singleton_path)
     apply clarsimp
     apply (rule_tac x="[]" in exI)
     apply clarsimp
     apply (rule conjI)
      apply (simp add: path.intros(1))
     apply force
    apply clarsimp
    apply (rule_tac x="[]" in exI)
    apply clarsimp
    apply (rule conjI)
     apply (simp add: path.intros(2))
    apply force
   apply clarsimp
   apply (rule_tac x="ys" in exI)
   apply clarsimp
   apply (metis (no_types, lifting) last_ConsL last_snoc path.cases path.intros(1) prod.sel(2))
  apply (rule_tac x="ys" in exI)
  apply clarsimp
  by (meson path.intros(2))

lemma anc_path: "ancestor T p c \<Longrightarrow> \<exists>xs. path T p c xs"
  apply (induct rule: ancestor.induct)
   apply (rule_tac x="[(parent, child)]" in exI, rule path.intros, assumption)
  apply clarsimp
  apply (case_tac "(parent, child) \<in> set x")
   defer
  apply (rule_tac x="x@[(parent, child)]" in exI)
   apply (rule path.intros(2))
     apply force
    apply force
   apply force
  apply (frule path_split)
   apply force
  apply clarsimp
  apply (elim disjE conjE)+
  using singleton_path apply fastforce
    apply clarsimp
  using fst_path path.intros(1) apply fastforce
   apply clarsimp
   apply (metis (no_types, lifting) last_ConsL path.cases prod.sel(2) snoc_eq_iff_butlast)
  by (meson path.intros(2))


lemma path_anc: "path T p c xs \<Longrightarrow> ancestor T p c"
  apply (induction rule: path.induct)
   apply (rule ancestor.intros(1), simp)
  by (simp add: ancestor.intros(2))

lemma anc_path_eq: "ancestor T p c \<longleftrightarrow> (\<exists>xs. path T p c xs)"
  by (meson anc_path path_anc)

lemma path_subset: "path T m n xs \<Longrightarrow> set xs \<subseteq> T"
  by (induction rule: path.induct) auto

lemma rem_edge_path: "path T m n xs \<Longrightarrow> T = insert (p, c) S \<Longrightarrow> (p, c) \<notin> set xs \<Longrightarrow> path S m n xs"
  apply (induction rule: path.induct)
   apply (rule path.intros(1), force)
  apply clarsimp
  apply (rule path.intros(2))
   apply clarsimp
   apply clarsimp
  by blast

lemma cyclic_ancestor_parent_flip:
  assumes \<open>ancestor T c p\<close>
    and \<open>T = insert (p, c) S\<close>
    and \<open>c \<noteq> p\<close>
  shows \<open>ancestor S c p\<close>
  using assms apply -

  sorry

lemma ancestor_transitive:
  assumes \<open>ancestor \<S> m n\<close>
      and \<open>ancestor \<S> n p\<close>
    shows \<open>ancestor \<S> m p\<close>
  using assms
  apply (simp add: anc_path_eq)
  apply clarsimp
  using path_concat apply force
  done

lemma cyclic_path_technical:
  assumes \<open>path T m n xs\<close>
      and \<open>T = insert (p, c) S\<close>
      and \<open>m = n\<close>
      and \<open>\<forall>n. \<not> ancestor S n n\<close>
      and \<open>c \<noteq> p\<close>
    shows \<open>ancestor S c p\<close>
  using assms apply -
  apply (case_tac "(p, c) \<in> set xs")
  defer
   apply (meson path_anc rem_edge_path)
  apply (frule path_split)
   apply force
  apply clarsimp
  apply (elim disjE conjE)
     prefer 4
     apply (rule ancestor_transitive[where n = n])
      apply (meson path_anc rem_edge_path)
     apply (meson path_anc rem_edge_path)
    apply clarsimp
  using singleton_path apply fastforce
   defer
   apply clarsimp
   apply (metis (no_types, lifting) cyclic_ancestor_parent_flip last_ConsL last_snoc path.cases path_anc prod.sel(2))
  apply clarsimp
  apply (subgoal_tac "n = p")
   apply clarsimp
   apply (meson cyclic_ancestor_parent_flip path_anc)
  by (simp add: fst_path)
  

lemma cyclic_ancestor_technical:
  assumes \<open>ancestor T m n\<close>
      and \<open>T = insert (p, c) S\<close>
      and \<open>m = n\<close>
      and \<open>\<forall>n. \<not> ancestor S n n\<close>
      and \<open>c \<noteq> p\<close>
    shows \<open>ancestor S c p\<close>
  using cyclic_path_technical
  by (metis anc_path_eq assms(1) assms(2) assms(3) assms(4) assms(5))


lemma cyclic_ancestor:
  assumes \<open>cyclic (S \<union> {(p, c)})\<close>
    and \<open>\<not> (cyclic S)\<close> 
    and \<open>c \<noteq> p\<close>
  shows \<open>ancestor S c p\<close>
  using assms apply (clarsimp simp add: cyclic_def)
  by (meson cyclic_ancestor_technical)

lemma do_op_acyclic:
  assumes \<open>\<not> cyclic tree1\<close>
    and \<open>do_op (Move t newp c, tree1) = (log_oper, tree2)\<close>
  shows \<open>\<not> cyclic tree2\<close>
proof(cases \<open>ancestor tree1 c newp \<or> c = newp\<close>)
  case True
  then show \<open>\<not> cyclic tree2\<close>
    using assms by auto
next
  case False
  hence A: \<open>tree2 = {(p', c') \<in> tree1. c' \<noteq> c} \<union> {(newp, c)}\<close>
    using assms(2) by auto
  moreover have \<open>{(p', c') \<in> tree1. c' \<noteq> c} \<subseteq> tree1\<close>
    by blast
  moreover have \<open>\<not> (cyclic tree1)\<close>
    using assms and cyclic_def by auto
  moreover have \<open>\<not> (cyclic {(p', c') \<in> tree1. c' \<noteq> c})\<close>
    using acyclic_subset calculation(2) calculation(3) by blast
  {
    assume \<open>cyclic tree2\<close>
    have \<open>ancestor {(p', c') \<in> tree1. c' \<noteq> c} c newp\<close>
      using cyclic_ancestor using False
      using A \<open>\<not> cyclic {(p', c'). (p', c') \<in> tree1 \<and> c' \<noteq> c}\<close> \<open>cyclic tree2\<close> by force
    from this have \<open>False\<close>
      using False ancestor_superset_closed calculation(2) by fastforce
  }
  from this show \<open>\<not> cyclic tree2\<close>
    using cyclic_def by auto
qed

theorem interp_op_acyclic:
  (* not true as it stands -- nitpick finds a counterexample *)
  assumes \<open>\<And>x. \<not> ancestor tree1 x x\<close>
    and \<open>interp_op oper (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>\<And>x. \<not> ancestor tree2 x x\<close>
  oops


theorem interp_op_commutes:
  (* missing some assumptions; as it stands, nitpick finds a counterexample *)
  shows \<open>interp_op op1 \<circ> interp_op op2 = interp_op op2 \<circ> interp_op op1\<close>
  oops

end