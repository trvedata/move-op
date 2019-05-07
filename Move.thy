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
      else let (op2, tree2) = do_op (op1, tree1) in (op2 # logop # ops, tree2))\<close>

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

corollary interp_ops_unique_parent:
  assumes \<open>interp_ops ops = (log, tree)\<close>
  shows \<open>\<And>p1 p2 c. (p1, c) \<in> tree \<Longrightarrow> (p2, c) \<in> tree \<Longrightarrow> p1 = p2\<close>
using assms proof(induction ops arbitrary: log tree rule: List.rev_induct)
  case Nil
  then show ?case
    by (metis empty_iff foldl_Nil fst_conv interp_ops_def swap_simp)
next
  case (snoc x xs)
  obtain log tree where interp_xs: \<open>interp_ops xs = (log, tree)\<close>
    by fastforce
  hence \<open>interp_ops (xs @ [x]) = interp_op x (log, tree)\<close>
    by (simp add: interp_ops_def)
  moreover have \<open>\<And>p1 p2 c. (p1, c) \<in> tree \<Longrightarrow> (p2, c) \<in> tree \<Longrightarrow> p1 = p2\<close>
    by (simp add: interp_xs snoc.IH)
  ultimately show ?case
    by (metis interp_op_unique_parent snoc.prems)
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

lemma ancestor_transitive:
  assumes \<open>ancestor \<S> n p\<close> and \<open>ancestor \<S> m n\<close>
    shows \<open>ancestor \<S> m p\<close>
  using assms by (induction rule: ancestor.induct) (auto intro: ancestor.intros)

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
  apply (metis anc_path_eq last_path rem_edge_path)
  apply clarsimp
  apply (subgoal_tac "n = p")
   apply clarsimp
  apply (meson anc_path_eq rem_edge_path)
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

corollary get_parent_empty [simp]:
  shows \<open>get_parent {} p = None\<close>
  using get_parent_None by force

corollary ancestor_empty_False [simp]:
  shows \<open>ancestor {} p c = False\<close>
  by (meson ancestor_indcases emptyE)

lemma interp_ops_base [simp]:
  shows \<open>interp_ops [Move t1 p1 c1, Move t2 p2 c2] =
                    interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) ([], {}))\<close>
  by(clarsimp simp add: interp_ops_def)

lemma interp_ops_base_commute:
  assumes \<open>t1 \<noteq> t2\<close>
  shows \<open>interp_ops [Move t1 p1 c1, Move t2 p2 c2] = interp_ops [Move t2 p2 c2, Move t1 p1 c1]\<close>
  using assms by(cases \<open>t2 < t1\<close>; cases \<open>p1 = c1\<close>; cases \<open>p2 = c2\<close>; cases \<open>c1 = c2\<close>; force)

lemma interp_ops_step [simp]:
  shows \<open>interp_ops (xs @ [x]) =
                    interp_op x (interp_ops xs)\<close>
  by(clarsimp simp add: interp_ops_def)

lemma interp_ops_step_commute [simp]:
  shows \<open>interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2]) =
          interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (interp_ops ops))\<close>
  by(clarsimp simp add: interp_ops_def)

fun do_one_op :: \<open>('t, 'n) state \<Rightarrow> ('t, 'n) operation \<Rightarrow> ('t, 'n) state\<close> where
  \<open>do_one_op (log, tree1) op1 =
    (let (op2, tree2) = do_op (op1, tree1) in (op2 # log, tree2))\<close>

lemma interp_ops_Nil [simp]:
  shows \<open>interp_ops [] = ([], {})\<close>
  by(clarsimp simp add: interp_ops_def)

(*
lemma
  assumes \<open>(log2, tree2) = interp_op (Move t p c) (log1, tree1)\<close>
  shows \<open>log_time ` set log2 = {t} \<union> (log_time ` set log1)\<close>
using assms proof(induction log1 arbitrary: tree1 tree2 log2, simp)
  case (Cons a log1)
  then obtain log3 tree3 where \<open>(log3, tree3) = interp_op (Move t p c) (log1, undo_op (a, tree1))\<close>
    by (metis surj_pair)
  hence \<open>log_time ` set log3 = {t} \<union> log_time ` set log1\<close>
    using Cons.IH by auto
  obtain t2 oldp2 newp2 c2 where a: \<open>a = LogMove t2 oldp2 newp2 c2\<close>
    using log_op.exhaust by blast
  then show ?case
  proof(cases \<open>t < t2\<close>)
    case True
    hence \<open>interp_op (Move t p c) (a # log1, tree1) = redo_op a (log3, tree3)\<close>
      by (simp add: \<open>(log3, tree3) = interp_op (Move t p c) (log1, undo_op (a, tree1))\<close> \<open>a = LogMove t2 oldp2 newp2 c2\<close>)
    hence \<open>redo_op a (log3, tree3) = (log2, tree2)\<close>
      by (simp add: Cons.prems)
    moreover have \<open>fst (redo_op a (log3, tree3)) = fst (do_op (Move t2 newp2 c2, tree3)) # log3\<close>
      by (simp add: \<open>a = LogMove t2 oldp2 newp2 c2\<close>)
    ultimately show ?thesis
      using a apply clarsimp
      using \<open>log_time ` set log3 = {t} \<union> log_time ` set log1\<close> by auto
  next
    case False
    then show ?thesis sorry
  qed
qed

lemma interp_ops_preserves_times:
  assumes \<open>interp_ops ops = (log, tree)\<close>
  shows \<open>move_time ` set ops = log_time ` set log\<close>
using assms proof(induction ops arbitrary: log tree rule: rev_induct, simp)
  case (snoc x xs)
  obtain log1 tree1 where \<open>interp_ops xs = (log1, tree1)\<close>
    by fastforce
  hence \<open>move_time ` set xs = log_time ` set log1\<close>
    using snoc.IH by auto
  obtain t p c where \<open>x = Move t p c\<close>
    using operation.exhaust by blast
  hence \<open>interp_ops (xs @ [x]) = interp_op (Move t p c) (log1, tree1)\<close>
    using \<open>interp_ops xs = (log1, tree1)\<close> by auto
  then show \<open>move_time ` set (xs @ [x]) = log_time ` set log\<close>
  proof(cases log1)
    case Nil
    hence \<open>log = (let (op2, tree2) = do_op (Move t p c, tree1) in [op2])\<close>
      using \<open>interp_ops xs = (log1, tree1)\<close> \<open>x = Move t p c\<close> snoc.prems by auto
    hence \<open>log_time ` set log = {t}\<close>
      by auto
    then show ?thesis 
      by (simp add: \<open>move_time ` set xs = log_time ` set log1\<close> \<open>x = Move t p c\<close> local.Nil)
  next
    case (Cons logop list)
    obtain t2 oldp2 newp2 c2 where \<open>logop = LogMove t2 oldp2 newp2 c2\<close>
      using log_op.exhaust by blast
    then show ?thesis
    proof(cases \<open>t < t2\<close>)
      case True
      hence \<open>interp_op (Move t p c) (log1, tree1) =
          redo_op logop (interp_op (Move t p c) (list, undo_op (logop, tree1)))\<close>
        by (simp add: \<open>logop = LogMove t2 oldp2 newp2 c2\<close> local.Cons)
      obtain tree2 where \<open>tree2 = undo_op (logop, tree1)\<close>
        by simp
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed

lemma
  assumes \<open>distinct (map move_time ops)\<close>
    and \<open>sorted (map move_time ops)\<close>
  shows \<open>interp_ops ops = foldl do_one_op ([], {}) ops\<close>
  using assms
  apply(induction ops rule: rev_induct)
   apply(clarsimp)
  apply clarsimp
  apply(subgoal_tac \<open>sorted (map move_time xs)\<close>)
   prefer 2 using sorted_append apply blast
  apply clarsimp
  apply(case_tac \<open>x\<close>; clarsimp)
  apply(subgoal_tac \<open>\<forall>oper\<in>set xs. x1 > move_time oper\<close>)
   prefer 2 apply (metis (no_types, lifting) image_iff le_neq_trans list.set_intros(1) list.set_map sorted_append)
  apply(case_tac \<open>foldl do_one_op ([], {}) xs\<close>)
  apply(case_tac \<open>a\<close>)
   apply clarsimp
  apply(case_tac \<open>aa\<close>)
  apply(subgoal_tac \<open>x1a < x1\<close>)
   prefer 2
  using interp_ops_preserves_times
  apply (metis (no_types, lifting) empty_set foldl_conv_fold image_eqI insert_iff interp_ops_def le_neq_trans list.set(2) list.set_intros(1) list.set_map log_op.sel(1) sorted_append)
  apply(subgoal_tac \<open>interp_op (Move x1 x2 x3) (aa#list, b) = do_one_op (aa#list, b) (Move x1 x2 x3)\<close>)
   apply force
  apply(subgoal_tac \<open>interp_op (Move x1 x2 x3) (aa#list, b) = (let (op2, tree2) = do_op (Move x1 x2 x3, b) in (op2 # aa # list, tree2))\<close>)
   prefer 2 apply force
  apply(subgoal_tac \<open>(let (op2, tree2) = do_op (Move x1 x2 x3, b) in (op2 # aa # list, tree2)) = do_one_op (aa#list,b) (Move x1 x2 x3)\<close>)
   prefer 2 apply force+
  done

lemma
  assumes \<open>distinct (map move_time (ops @ [Move t1 p1 c1, Move t2 p2 c2]))\<close>
  shows \<open>interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2]) =
         interp_ops (ops @ [Move t2 p2 c2, Move t1 p1 c1])\<close>
  using assms
  apply(induction ops arbitrary: t1 t2 p1 p2 c1 c2 rule: List.rev_induct)
  using interp_ops_base_commute
   apply (metis append_Nil distinct_length_2_or_more list.simps(9) operation.sel(1))
  apply clarsimp
  apply(case_tac \<open>x\<close>; clarify)
  apply(subgoal_tac \<open>\<And>t1 t2 p1 p2 c1 c2.
           t1 \<noteq> t2 \<and> t1 \<notin> move_time ` set xs \<and> t2 \<notin> move_time ` set xs \<Longrightarrow> interp_ops (xs @ [Move t1 p1 c1, Move t2 p2 c2]) = interp_ops (xs @ [Move t2 p2 c2, Move t1 p1 c1])\<close>)
  oops
*)


lemma redo_op_cons:
  assumes \<open>redo_op (LogMove t oldp p c) (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>\<exists>p2. ops2 = (LogMove t p2 p c) # ops1\<close>
  using assms by auto

lemma foldr_redo:
  assumes \<open>interp_op (Move t p c) (log1, tree1) = (log2, tree2)\<close>
    and \<open>foldr redo_op log1 st = (log1, tree1)\<close>
  shows \<open>foldr redo_op log2 st = (log2, tree2)\<close>
  using assms
  apply(induction log1 arbitrary: log2 tree1 tree2 st rule: List.rev_induct; clarsimp)
  apply(case_tac "redo_op x (a, b)"; clarsimp)
  apply(case_tac "x"; clarsimp)
  apply(case_tac "ancestor b x4 x3 \<or> x4 = x3"; clarsimp)
  oops

lemma foldr_redo:
  assumes \<open>interp_op (Move t p c) (log1, tree1) = (log2, tree2)\<close>
    and \<open>foldr redo_op log1 ([], {}) = (log1, tree1)\<close>
  shows \<open>foldr redo_op log2 ([], {}) = (log2, tree2)\<close>
using assms proof(induction log1 arbitrary: log2 tree1 tree2, clarsimp)
  case (Cons logop log1)
  then show ?case
  proof(cases \<open>t < log_time logop\<close>)
    case True
    hence \<open>interp_op (Move t p c) (logop # log1, tree1) =
           redo_op logop (interp_op (Move t p c) (log1, undo_op (logop, tree1)))\<close>
      by simp
    then show ?thesis sorry
(*  then show ?thesis 
      using Cons apply -
      apply clarsimp
      apply (case_tac "foldr redo_op log1 ([], {})")
      apply clarsimp
      apply (subgoal_tac "(\<exists>b2. redo_op logop (a, b) = (logop # a, b2)) \<or> (\<exists>logop2 b2. logop2 \<noteq> logop \<and> 
                                                            redo_op logop (a, b) = (logop2 # a, b2))")
       prefer 2
       apply (metis log_op.exhaust_sel redo_op_cons)
      apply (erule disjE)
       prefer 2
       apply force
      apply (erule exE)
      apply (subgoal_tac "a = log1 \<and> b2 = tree1")
       prefer 2
       apply force
      apply clarsimp
      apply(case_tac "logop", clarsimp simp del: redo_op.simps)
      apply(subst (asm) redo_op.simps)
      apply(subst (asm) do_op.simps)*)
  next
    case False
    hence *: \<open>interp_op (Move t p c) (logop # log1, tree1) =
           (let (op2, tree2) = do_op (Move t p c, tree1) in (op2 # logop # log1, tree2))\<close>
      by simp
    obtain logop2 tree2' where \<open>(logop2, tree2') = do_op (Move t p c, tree1)\<close>
      by simp
    hence \<open>log2 = logop2 # logop # log1\<close> and \<open>tree2' = tree2\<close>
      using * Cons.prems(1) by auto
    hence \<open>foldr redo_op log2 ([], {}) = redo_op logop2 (foldr redo_op (logop # log1) ([], {}))\<close>
      by simp
    also have \<open>... = redo_op logop2 (logop # log1, tree1)\<close>
      using Cons.prems(2) by auto
    (* The problem here is that redoing logop2 ignores the old-parent field,
       and recomputes a new old-parent field by do_op. That recomputed field
       value is not necessarily the same! So the returned log is not necessarily
       equal to log2 = logop2 # logop # log1. *)
    then show \<open>foldr redo_op log2 ([], {}) = (log2, tree2)\<close>
      sorry
  qed
qed

(*lemma foldr_redo:
  assumes \<open>interp_ops ops = (log1, tree1)\<close>
    and \<open>interp_op (Move t p c) (log1, tree1) = (log2, tree2)\<close>
    and \<open>distinct ((map move_time ops) @ [t])\<close>
    and \<open>foldr redo_op log1 ([], {}) = (log1, tree1)\<close>
  shows \<open>foldr redo_op log2 ([], {}) = (log2, tree2)\<close>
  sorry*)

(* if \<open>interp_ops ops = (log, tree)\<close> then tree is a function of log. *)
lemma redo_reconstruct_tree:
  assumes \<open>interp_ops ops = (log, tree)\<close>
    and \<open>distinct (map move_time ops)\<close>
  shows \<open>foldr redo_op log ([], {}) = (log, tree)\<close>
using assms proof(induction ops arbitrary: log tree rule: List.rev_induct)
  case Nil
  thus \<open>foldr redo_op log ([], {}) = (log, tree)\<close>
    using foldr_Nil by simp
next
  case (snoc oper ops)
  obtain t p c where \<open>oper = Move t p c\<close>
    using operation.exhaust by blast
  moreover obtain log1 tree1 where \<open>interp_ops ops = (log1, tree1)\<close>
    using prod.exhaust_sel by blast
  moreover from this have \<open>foldr redo_op log1 ([], {}) = (log1, tree1)\<close>
    using snoc.IH snoc.prems(2) by auto
  ultimately show \<open>foldr redo_op log ([], {}) = (log, tree)\<close>
    using foldr_redo snoc.prems(1) snoc.prems(2) by fastforce
qed

corollary unique_tree_given_log:
  assumes \<open>interp_ops ops1 = (log, tree1)\<close> and \<open>interp_ops ops2 = (log, tree2)\<close>
    and \<open>distinct (map move_time ops1)\<close> and \<open>distinct (map move_time ops2)\<close>
  shows \<open>tree1 = tree2\<close>
using assms redo_reconstruct_tree by (metis Pair_inject)

lemma distinct_list_pick1:
  assumes \<open>set (xs @ [x]) = set (ys @ [x] @ zs)\<close>
    and \<open>distinct (xs @ [x])\<close> and \<open>distinct (ys @ [x] @ zs)\<close>
  shows \<open>set xs = set (ys @ zs)\<close>
  sorry

(*lemma log_unique_two_ops:
  assumes \<open>interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2]) = (log1, tree1)\<close>
    and \<open>interp_ops (ops @ [Move t2 p2 c2, Move t1 p1 c1]) = (log2, tree2)\<close>
    and \<open>distinct ((map move_time ops) @ [t1, t2])\<close>
  shows \<open>log1 = log2\<close>
using assms proof(induction ops arbitrary: log1 log2 tree1 tree2 t1 p1 c1 t2 p2 c2 rule: List.rev_induct)
  case Nil
  thus ?case
    using interp_ops_base_commute
    by (metis append_Nil distinct_length_2_or_more fst_conv list.simps(8))
next
  case (snoc x xs)
  hence \<open>fst (interp_ops (xs @ [x, Move t1 p1 c1])) = fst (interp_ops (xs @ [Move t1 p1 c1, x]))\<close> (is ?L)
    and \<open>fst (interp_ops (xs @ [x, Move t2 p2 c2])) = fst (interp_ops (xs @ [Move t2 p2 c2, x]))\<close> (is ?R)
  proof -
    obtain tx px cx where \<open>x = Move tx px cx\<close>
      using operation.exhaust by blast
    moreover from this have \<open>distinct (map move_time xs @ [tx, t1])\<close>
       and \<open>distinct (map move_time xs @ [tx, t2])\<close>
      using snoc.prems(3) by auto
    ultimately show ?L and ?R
      by (metis prod.exhaust_sel snoc.IH)+
  qed

  then show ?case sorry
qed*)

lemma
  assumes \<open>interp_op (Move t p c) (log1, tree1) = (log2, tree2)\<close>
  shows \<open>\<exists>pre1 pre2 suf oldp. log1 = pre1 @ suf \<and> log2 = pre2 @ [LogMove t oldp p c] @ suf \<and>
         (\<exists>tree3. foldr redo_op pre1 ([LogMove t oldp p c] @ suf, tree3) = (pre2, tree2)) \<and>
         (\<forall>ts \<in> log_time ` set pre2. ts > t) \<and> (\<forall>ts \<in> log_time ` set suf. ts < t)\<close>
using assms proof(induction log1 arbitrary: tree1 tree2 log2, clarsimp)
  case (Cons logop log1)
  then show ?case
  proof(cases \<open>t < log_time logop\<close>)
    case True
    obtain log3 tree3 where *: \<open>(log3, tree3) = interp_op (Move t p c) (log1, undo_op (logop, tree1))\<close>
      by (metis prod.exhaust_sel)
    have \<open>interp_op (Move t p c) (logop # log1, tree1) =
        redo_op logop (interp_op (Move t p c) (log1, undo_op (logop, tree1)))\<close>
      using True by simp
    also have \<open>... = redo_op logop (log3, tree3)\<close>
      using * by simp
    also have **: \<open>... = (log2, tree2)\<close>
      using Cons.prems calculation by auto
    from this obtain logop4 tree4 where \<open>redo_op logop (log3, tree3) = (logop4 # log3, tree4)\<close>
      by (metis log_op.exhaust_sel redo_op_cons)
    obtain pre suf oldp where \<open>log1 = pre @ suf\<close> and
              \<open>log3 = pre @ [LogMove t oldp p c] @ suf\<close> and
              \<open>\<And>ts. ts \<in> log_time ` set pre \<Longrightarrow> ts > t\<close> and
              \<open>\<And>ts. ts \<in> log_time ` set suf \<Longrightarrow> ts < t\<close>
      sorry
    then show ?thesis
      apply -
      apply(rule_tac x=\<open>logop4 # pre\<close> in exI)
      apply(rule_tac x=\<open>suf\<close> in exI, rule_tac x=oldp in exI)
      apply clarsimp
      apply(rule conjI)
      using redo_op_cons **
      sorry
  next
    case False
    then show ?thesis sorry
  qed
qed
  

lemma log_unique_two_ops:
  assumes \<open>interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2]) = (log1, tree1)\<close>
    and \<open>interp_ops (ops @ [Move t2 p2 c2, Move t1 p1 c1]) = (log2, tree2)\<close>
    and \<open>distinct ((map move_time ops) @ [t1, t2])\<close>
    and \<open>t1 < t2\<close>
  shows \<open>log1 = log2\<close>
using assms proof(induction ops arbitrary: log1 log2 tree1 tree2 rule: List.rev_induct)
  case Nil
  thus ?case
    using interp_ops_base_commute
    by (metis append_Nil distinct_length_2_or_more fst_conv list.simps(8))
next
  case (snoc x xs)
  obtain tx px cx where \<open>x = Move tx px cx\<close>
    using operation.exhaust by blast
  then consider (c1) \<open>tx < t1\<close> | (c2) \<open>t1 < tx \<and> tx < t2\<close> | (c3) \<open>t2 < tx\<close>
    using not_less_iff_gr_or_eq snoc.prems(3) by auto
  then show ?case
  proof(cases)
    case c1
    then show ?thesis sorry
  next
    case c2
    then show ?thesis sorry
  next
    case c3
    then show ?thesis sorry
  qed
qed


lemma log_unique_swap_last:
  assumes \<open>distinct ((map move_time ops) @ [t1, t2])\<close>
  shows \<open>fst (interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2])) =
         fst (interp_ops (ops @ [Move t2 p2 c2, Move t1 p1 c1]))\<close>
proof(cases \<open>t1 < t2\<close>)
  case True
  then show ?thesis
    by (meson assms log_unique_two_ops prod.exhaust_sel)
next
  case False
  have \<open>distinct ((map move_time ops) @ [t2, t1])\<close>
    using assms by auto
  moreover have \<open>t1 \<noteq> t2\<close>
    using assms by auto
  hence \<open>t2 < t1\<close>
    using False by auto
  ultimately have \<open>fst (interp_ops (ops @ [Move t2 p2 c2, Move t1 p1 c1])) =
         fst (interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2]))\<close>
    by (meson log_unique_two_ops prod.exhaust_sel)
  thus ?thesis
    by simp
qed

lemma log_unique_middle:
  assumes \<open>interp_ops (xs @ ys @ [oper]) = (log1, tree1)\<close>
    and \<open>interp_ops (xs @ [oper] @ ys) = (log2, tree2)\<close>
    and \<open>distinct (map move_time (xs @ ys @ [oper]))\<close>
  shows \<open>log1 = log2\<close>
using assms proof(induction ys arbitrary: log1 log2 tree1 tree2 rule: List.rev_induct, simp)
  case (snoc y ys)
  have \<open>fst (interp_ops (xs @ [oper] @ ys @ [y])) =
        fst (interp_op y (interp_ops (xs @ [oper] @ ys)))\<close>
    by (metis append.assoc interp_ops_step)
  also have \<open>... = fst (interp_op y (interp_ops (xs @ ys @ [oper])))\<close>
  proof -
    have \<open>distinct (map move_time (xs @ [oper] @ ys))\<close>
        and \<open>distinct (map move_time (xs @ ys @ [oper]))\<close>
      using snoc.prems(3) by auto
    moreover from this have \<open>fst (interp_ops (xs @ [oper] @ ys)) =
        fst (interp_ops (xs @ ys @ [oper]))\<close>
      using snoc.IH by (metis prod.exhaust_sel)
    ultimately show ?thesis
      by (metis prod.exhaust_sel unique_tree_given_log)
  qed
  also have \<open>... = fst (interp_ops ((xs @ ys) @ [oper, y]))\<close>
    by (metis append.assoc append_Cons append_Nil interp_ops_step)
  also have \<open>... = fst (interp_ops ((xs @ ys) @ [y, oper]))\<close>
  proof -
    have \<open>distinct ((map move_time (xs @ ys)) @ [move_time oper, move_time y])\<close>
      using snoc.prems(3) by auto
    thus ?thesis
      using log_unique_swap_last by (metis operation.exhaust_sel)
  qed
  then show ?case
    using calculation snoc.prems(1) snoc.prems(2) by auto
qed

lemma interp_op_move_logop1:
  assumes \<open>t1 \<noteq> t2\<close>
    and \<open>\<And>t. t \<in> set (map log_time log) \<Longrightarrow> t < t1\<close>
    and \<open>logop = LogMove t1 (get_parent tree c1) p1 c1\<close>
    and \<open>undo_op (logop, tree1) = tree\<close>
    and \<open>\<And>p1 p2 c. (p1, c) \<in> tree \<Longrightarrow> (p2, c) \<in> tree \<Longrightarrow> p1 = p2\<close>
  shows \<open>interp_op (Move t2 p2 c2) (logop # log, tree1) =
         interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (log, tree))\<close>
  sorry

lemma interp_op_move_logop2:
  assumes \<open>distinct [t1, t2, t3]\<close>
    and \<open>\<And>t. t \<in> set (map log_time log) \<Longrightarrow> t < t1\<close>
    and \<open>logop = LogMove t1 (get_parent tree c1) p1 c1\<close>
    and \<open>undo_op (logop, tree1) = tree\<close>
    and \<open>\<And>p1 p2 c. (p1, c) \<in> tree \<Longrightarrow> (p2, c) \<in> tree \<Longrightarrow> p1 = p2\<close>
  shows \<open>interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (logop # log, tree1)) =
         interp_op (Move t1 p1 c1) (interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (log, tree)))\<close>
proof -
  consider (c123) \<open>t1 < t2 \<and> t2 < t3\<close> | (c132) \<open>t1 < t3 \<and> t3 < t2\<close> | (c213) \<open>t2 < t1 \<and> t1 < t3\<close> |
           (c231) \<open>t2 < t3 \<and> t3 < t1\<close> | (c312) \<open>t3 < t1 \<and> t1 < t2\<close> | (c321) \<open>t3 < t2 \<and> t2 < t1\<close>
    using assms by fastforce
  then show ?thesis
  proof(cases)
    case c123 (* t1 < t2 < t3 *)
    obtain tree12 where tree12: \<open>do_op (Move t2 p2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 c2, tree12)\<close>
      by simp
    obtain tree123 where tree123: \<open>do_op (Move t3 p3 c3, tree12) = (LogMove t3 (get_parent tree12 c3) p3 c3, tree123)\<close>
      by simp
    obtain tree2 where tree2: \<open>do_op (Move t2 p2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 c2, tree2)\<close>
      by simp
    hence undo3: \<open>undo_op (LogMove t2 (get_parent tree c2) p2 c2, tree2) = tree\<close>
      by (metis assms(5) do_undo_op_inv)
    obtain tree23 where tree23: \<open>do_op (Move t3 p3 c3, tree2) = (LogMove t3 (get_parent tree2 c3) p3 c3, tree23)\<close>
      by simp
    hence undo4: \<open>undo_op (LogMove t3 (get_parent tree2 c3) p3 c3, tree23) = tree2\<close>
      by (metis assms(5) do_op_unique_parent do_undo_op_inv tree2)
    have redo1: \<open>do_op (Move t1 p1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 c1, tree1)\<close>
      sorry
    have 1: \<open>interp_op (Move t2 p2 c2) (logop # log, tree1) =
              ((LogMove t2 (get_parent tree1 c2) p2 c2) # logop # log, tree12)\<close>
      using c123 tree12 assms(3) by auto
    hence 4: \<open>interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (logop # log, tree1)) =
           (LogMove t3 (get_parent tree12 c3) p3 c3 # LogMove t2 (get_parent tree1 c2) p2 c2 # logop # log, tree123)\<close>
      by (metis c123 case_prod_conv interp_op.simps(2) log_op.sel(1) not_less_iff_gr_or_eq operation.sel(1) tree123)
    have \<open>interp_op (Move t2 p2 c2) (log, tree) = (LogMove t2 (get_parent tree c2) p2 c2 # log, tree2)\<close>
    proof(cases log)
      case Nil
      then show ?thesis using tree2 by auto
    next
      case (Cons logop log')
      moreover from this have \<open>log_time logop < t2\<close>
        using assms(2) c123 dual_order.strict_trans by auto
      ultimately show ?thesis using tree2 by auto
    qed
    hence \<open>interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (log, tree)) =
           (LogMove t3 (get_parent tree2 c3) p3 c3 # LogMove t2 (get_parent tree c2) p2 c2 # log, tree23)\<close>
      using c123 tree23 by auto
    hence 3: \<open>interp_op (Move t1 p1 c1) (interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (log, tree))) =
           redo_op (LogMove t3 (get_parent tree2 c3) p3 c3) (interp_op (Move t1 p1 c1) (LogMove t2 (get_parent tree c2) p2 c2 # log, tree2))\<close>
      using c123 undo4 by auto
    have 2: \<open>interp_op (Move t1 p1 c1) (LogMove t2 (get_parent tree c2) p2 c2 # log, tree2) =
          redo_op (LogMove t2 (get_parent tree c2) p2 c2) (interp_op (Move t1 p1 c1) (log, tree))\<close>
      using c123 undo3 by auto
    have \<open>interp_op (Move t1 p1 c1) (log, tree) = (LogMove t1 (get_parent tree c1) p1 c1 # log, tree1)\<close>
    proof(cases log)
      case Nil
      then show ?thesis using redo1 by auto
    next
      case (Cons logop log')
      moreover from this have \<open>log_time logop < t1\<close>
        by (simp add: assms(2))
      ultimately show ?thesis using redo1 by auto
    qed
    hence 5: \<open>interp_op (Move t1 p1 c1) (LogMove t2 (get_parent tree c2) p2 c2 # log, tree2) =
        (LogMove t2 (get_parent tree1 c2) p2 c2 # LogMove t1 (get_parent tree c1) p1 c1 # log, tree12)\<close>
      using "2" tree12 by auto
    hence \<open>interp_op (Move t1 p1 c1) (interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (log, tree))) =
           (LogMove t3 (get_parent tree12 c3) p3 c3 # LogMove t2 (get_parent tree1 c2) p2 c2 # LogMove t1 (get_parent tree c1) p1 c1 # log, tree123)\<close>
      using "3" tree123 by auto
    then show ?thesis
      using "4" assms(3) by simp
  next
    case c132 (* t1 < t3 < t2 *)
    then show ?thesis sorry
  next
    case c213 (* t2 < t1 < t3 *)
    obtain log2 tree2 where log2: \<open>interp_op (Move t2 p2 c2) (log, tree) = (log2, tree2)\<close>
      by fastforce
    obtain tree21 where tree21: \<open>do_op (Move t1 p1 c1, tree2) = (LogMove t1 (get_parent tree2 c1) p1 c1, tree21)\<close>
      by simp
    obtain tree213 where \<open>do_op (Move t3 p3 c3, tree21) = (LogMove t3 (get_parent tree21 c3) p3 c3, tree213)\<close>
      by simp
    hence \<open>interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (logop # log, tree1)) =
           (LogMove t3 (get_parent tree21 c3) p3 c3 # LogMove t1 (get_parent tree2 c1) p1 c1 # log2, tree213)\<close>
      using assms(3) assms(4) c213 log2 tree21 by auto
    obtain tree23 where tree23: \<open>do_op (Move t3 p3 c3, tree2) = (LogMove t3 (get_parent tree2 c3) p3 c3, tree23)\<close>
      by simp
    have \<open>interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (log, tree)) =
          (LogMove t3 (get_parent tree2 c3) p3 c3 # log2, tree23)\<close>
    proof -
      have \<open>\<And>t. t \<in> set (map log_time log2) \<Longrightarrow> t \<le> t2\<close>
        sorry
      moreover have \<open>t2 < t3\<close>
        using c213 by auto
      ultimately show ?thesis
        sorry
    qed
    have \<open>interp_op (Move t1 p1 c1) (interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (log, tree))) =
          undefined\<close>
      sorry
    then show ?thesis sorry
  next
    case c231 (* t2 < t3 < t1 *)
    then show ?thesis sorry
  next
    case c312 (* t3 < t1 < t2 *)
    then show ?thesis sorry
  next
    case c321 (* t3 < t2 < t1 *)
    obtain log2 tree2 where log2: \<open>interp_op (Move t2 p2 c2) (log, tree) = (log2, tree2)\<close>
      by fastforce
    obtain tree21 where tree21: \<open>do_op (Move t1 p1 c1, tree2) = (LogMove t1 (get_parent tree2 c1) p1 c1, tree21)\<close>
      by simp
    hence undo21: \<open>undo_op (LogMove t1 (get_parent tree2 c1) p1 c1, tree21) = tree2\<close>
      by (metis assms(5) do_undo_op_inv interp_op_unique_parent log2)
    obtain tree23 where tree23: \<open>do_op (Move t3 p3 c3, tree2) = (LogMove t3 (get_parent tree2 c3) p3 c3, tree23)\<close>
      by simp
    obtain log3 tree3 where log3: \<open>interp_op (Move t3 p3 c3) (log, tree) = (log3, tree3)\<close>
      by fastforce
    obtain tree32 where tree32: \<open>do_op (Move t2 p2 c2, tree3) = (LogMove t2 (get_parent tree3 c2) p2 c2, tree32)\<close>
      by simp
    obtain tree321 where \<open>do_op (Move t1 p1 c1, tree32) = (LogMove t1 (get_parent tree32 c1) p1 c1, tree321)\<close>
      by simp
    have \<open>interp_op (Move t2 p2 c2) (logop # log, tree1) =
          (LogMove t1 (get_parent tree2 c1) p1 c1 # log2, tree21)\<close>
      using assms(3) assms(4) c321 log2 tree21 by auto
    hence \<open>interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (logop # log, tree1)) =
          redo_op (LogMove t1 (get_parent tree2 c1) p1 c1) (interp_op (Move t3 p3 c3) (log2, tree2))\<close>
      using c321 undo21 by auto
    then show ?thesis sorry
  qed
qed
 

lemma interp_op_commute2:
  assumes \<open>t1 < t2\<close>
    and \<open>\<And>p1 p2 c. (p1, c) \<in> tree \<Longrightarrow> (p2, c) \<in> tree \<Longrightarrow> p1 = p2\<close>
    and \<open>distinct ((map log_time log) @ [t1, t2])\<close>
  shows \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (log, tree)) =
         interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (log, tree))\<close>
using assms proof(induction log arbitrary: tree)
  case Nil
  obtain tree1 where \<open>do_op (Move t1 p1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 c1, tree1)\<close>
    by simp
  hence *: \<open>interp_op (Move t1 p1 c1) ([], tree) = ([LogMove t1 (get_parent tree c1) p1 c1], tree1)\<close>
    by auto
  obtain tree2 where tree2: \<open>do_op (Move t2 p2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 c2, tree2)\<close>
    by simp
  have \<open>\<not> t2 < t1\<close>
    using not_less_iff_gr_or_eq Nil.prems(1) by blast
  hence **: \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) ([], tree)) =
        ([LogMove t2 (get_parent tree1 c2) p2 c2, LogMove t1 (get_parent tree c1) p1 c1], tree2)\<close>
    using * tree2 by auto
  obtain tree3 where tree3: \<open>do_op (Move t2 p2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 c2, tree3)\<close>
    by simp
  hence ***: \<open>interp_op (Move t2 p2 c2) ([], tree) = ([LogMove t2 (get_parent tree c2) p2 c2], tree3)\<close>
    by auto
  have \<open>undo_op (LogMove t2 (get_parent tree c2) p2 c2, tree3) = tree\<close>
    by (metis Nil.prems(2) tree3 do_undo_op_inv)
  hence \<open>interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) ([], tree)) =
         redo_op (LogMove t2 (get_parent tree c2) p2 c2) ([LogMove t1 (get_parent tree c1) p1 c1], tree1)\<close>
    using * *** Nil.prems(1) by auto
  then show ?case
    using tree2 ** by auto
next
  case (Cons logop log)
  obtain t3 where t3: \<open>t3 = log_time logop\<close>
    by simp
  then consider (c1) \<open>t3 < t1\<close> | (c2) \<open>t1 < t3 \<and> t3 < t2\<close> | (c3) \<open>t2 < t3\<close>
    using Cons.prems(3) by force
  then show ?case
  proof(cases)
    case c1
    hence \<open>t3 < t2\<close>
      using Cons.prems(1) by auto
    obtain tree1 where \<open>do_op (Move t1 p1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 c1, tree1)\<close>
      by simp
    hence *: \<open>interp_op (Move t1 p1 c1) (logop # log, tree) = (LogMove t1 (get_parent tree c1) p1 c1 # logop # log, tree1)\<close>
      using t3 c1 by auto
    obtain tree2 where tree2: \<open>do_op (Move t2 p2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 c2, tree2)\<close>
      by simp
    have \<open>\<not> t2 < t1\<close>
      using not_less_iff_gr_or_eq Cons.prems(1) by blast
    hence **: \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (logop # log, tree)) =
               ([LogMove t2 (get_parent tree1 c2) p2 c2, LogMove t1 (get_parent tree c1) p1 c1, logop] @ log, tree2)\<close>
      using * tree2 by auto
    obtain tree3 where tree3: \<open>do_op (Move t2 p2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 c2, tree3)\<close>
      by simp
    hence ***: \<open>interp_op (Move t2 p2 c2) (logop # log, tree) = (LogMove t2 (get_parent tree c2) p2 c2 # logop # log, tree3)\<close>
      using \<open>t3 < t2\<close> t3 by auto
    have \<open>undo_op (LogMove t2 (get_parent tree c2) p2 c2, tree3) = tree\<close>
      by (metis Cons.prems(2) do_undo_op_inv tree3)
    hence \<open>interp_op (Move t1 p1 c1) (LogMove t2 (get_parent tree c2) p2 c2 # logop # log, tree3) =
          redo_op (LogMove t2 (get_parent tree c2) p2 c2) (LogMove t1 (get_parent tree c1) p1 c1 # logop # log, tree1)\<close>
      using * Cons.prems(1) by auto
    then show ?thesis
      using ** *** tree2 by auto
  next
    case c2
    hence \<open>interp_op (Move t1 p1 c1) (logop # log, tree) =
           redo_op logop (interp_op (Move t1 p1 c1) (log, undo_op (logop, tree)))\<close>
      by (simp add: t3)
    obtain tree1 where tree1: \<open>tree1 = undo_op (logop, tree)\<close>
      by simp
    have \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (log, undo_op (logop, tree))) =
          interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (log, undo_op (logop, tree)))\<close>
    proof -
      have \<open>(\<And>p1 c p2. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2)\<close>
        sorry
      then show ?thesis
        using Cons.IH Cons.prems(3) assms(1) tree1 by auto
    qed
    obtain tree3 where tree3: \<open>do_op (Move t2 p2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 c2, tree3)\<close>
      by simp
    have *: \<open>interp_op (Move t2 p2 c2) (logop # log, tree) = (LogMove t2 (get_parent tree c2) p2 c2 # logop # log, tree3)\<close>
      using c2 t3 tree3 by auto
    have \<open>undo_op (LogMove t2 (get_parent tree c2) p2 c2, tree3) = tree\<close>
      by (metis Cons.prems(2) do_undo_op_inv tree3)
    hence \<open>interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (logop # log, tree)) =
          redo_op (LogMove t2 (get_parent tree c2) p2 c2) (interp_op (Move t1 p1 c1) (logop # log, tree))\<close>
      using * assms(1) by auto
    (* TODO work in progress *)
    then show ?thesis sorry
  next
    case c3
    obtain t3 oldp3 p3 c3 where logop: \<open>logop = LogMove t3 oldp3 p3 c3\<close>
      using log_op.exhaust by blast
    have \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (logop # log, tree)) =
           interp_op (Move t3 p3 c3) (interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (log, undo_op(logop, tree))))\<close>
    proof -
      have \<open>distinct [t3, t1, t2]\<close>
        using assms(1) c3 t3 logop by auto
      moreover have \<open>\<And>t. t \<in> set (map log_time log) \<Longrightarrow> t < t3\<close>
        sorry
      moreover have \<open>oldp3 = get_parent (undo_op(logop, tree)) c3\<close>
        sorry
      moreover have \<open>\<And>p1 p2 c. (p1, c) \<in> undo_op(logop, tree) \<Longrightarrow> (p2, c) \<in> undo_op(logop, tree) \<Longrightarrow> p1 = p2\<close>
        sorry
      ultimately show ?thesis
        by (metis (no_types, hide_lams) interp_op_move_logop2 logop)
    qed
    also have \<open>... = interp_op (Move t3 p3 c3) (interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (log, undo_op(logop, tree))))\<close>
    proof -
      have \<open>(\<And>p1 c p2. (p1, c) \<in> undo_op(logop, tree) \<Longrightarrow> (p2, c) \<in> undo_op(logop, tree) \<Longrightarrow> p1 = p2)\<close>
        sorry
      then show ?thesis
        using Cons.IH Cons.prems(3) assms(1) by auto
    qed
    also have \<open>... = interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (logop # log, tree))\<close>
    proof -
      have \<open>distinct [t3, t2, t1]\<close>
        using assms(1) c3 t3 logop by auto
      moreover have \<open>\<And>t. t \<in> set (map log_time log) \<Longrightarrow> t < t3\<close>
        sorry
      moreover have \<open>oldp3 = get_parent (undo_op(logop, tree)) c3\<close>
        sorry
      moreover have \<open>\<And>p1 p2 c. (p1, c) \<in> undo_op(logop, tree) \<Longrightarrow> (p2, c) \<in> undo_op(logop, tree) \<Longrightarrow> p1 = p2\<close>
        sorry
      ultimately show ?thesis
        by (metis (no_types, hide_lams) interp_op_move_logop2 logop)
    qed
    ultimately show ?thesis
      by simp
  qed
qed

lemma interp_op_commute_last:
  assumes \<open>t1 \<noteq> t2\<close>
  shows \<open>interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2]) =
         interp_ops (ops @ [Move t2 p2 c2, Move t1 p1 c1])\<close>
proof -
  obtain log tree where interp_ops: \<open>interp_ops ops = (log, tree)\<close>
    by fastforce
  hence unique_parent: \<open>\<And>p1 p2 c. (p1, c) \<in> tree \<Longrightarrow> (p2, c) \<in> tree \<Longrightarrow> p1 = p2\<close>
    by (meson interp_ops_unique_parent)
  have distinct_times: \<open>distinct ((map log_time log) @ [t1, t2])\<close>
    sorry
  have \<open>interp_ops (ops @ [Move t1 p1 c1, Move t2 p2 c2]) =
        interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (log, tree))\<close>
    using interp_ops by simp
  also have \<open>... = interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (log, tree))\<close>
  proof(cases \<open>t1 < t2\<close>)
    case True
    then show ?thesis
      by (metis unique_parent distinct_times interp_op_commute2)
  next
    case False
    hence \<open>t2 < t1\<close>
      using assms by auto
    moreover have \<open>distinct ((map log_time log) @ [t2, t1])\<close>
      using distinct_times by auto
    ultimately show ?thesis
      by (metis unique_parent interp_op_commute2)
  qed
  also have \<open>... = interp_ops (ops @ [Move t2 p2 c2, Move t1 p1 c1])\<close>
    using interp_ops by simp
  ultimately show ?thesis
    by presburger
qed

lemma interp_op_commute_middle:
  assumes \<open>distinct (map move_time (xs @ ys @ [oper]))\<close>
  shows \<open>interp_ops (xs @ ys @ [oper]) = interp_ops (xs @ [oper] @ ys)\<close>
using assms proof(induction ys rule: List.rev_induct, simp)
  case (snoc y ys)
  have \<open>interp_ops (xs @ [oper] @ ys @ [y]) = interp_op y (interp_ops (xs @ [oper] @ ys))\<close>
    by (metis append.assoc interp_ops_step)
  also have \<open>... = interp_op y (interp_ops (xs @ ys @ [oper]))\<close>
  proof -
    have \<open>distinct (map move_time (xs @ ys @ [oper]))\<close>
      using snoc.prems by auto
    then show ?thesis
      using snoc.IH by auto
  qed
  also have \<open>... = interp_ops ((xs @ ys) @ [oper, y])\<close>
    by (metis append.assoc append_Cons append_Nil interp_ops_step)
  also have \<open>... = interp_ops ((xs @ ys) @ [y, oper])\<close>
  proof -
    have \<open>move_time oper \<noteq> move_time y\<close>
      using snoc.prems by auto
    thus ?thesis
      using interp_op_commute_last by (metis operation.exhaust_sel)
  qed
  ultimately show ?case
    by simp
qed

theorem interp_ops_commutes:
  assumes \<open>set ops1 = set ops2\<close>
    and \<open>distinct (map move_time ops1)\<close> and \<open>distinct (map move_time ops2)\<close>
  shows \<open>interp_ops ops1 = interp_ops ops2\<close>
using assms proof(induction ops1 arbitrary: ops2 rule: List.rev_induct, simp)
  case (snoc oper ops)
  then obtain pre suf where pre_suf: \<open>ops2 = pre @ [oper] @ suf\<close>
    by (metis append_Cons append_Nil in_set_conv_decomp)
  hence \<open>set ops = set (pre @ suf)\<close>
    using snoc.prems distinct_map distinct_list_pick1 by metis
  hence IH: \<open>interp_ops ops = interp_ops (pre @ suf)\<close>
    using pre_suf snoc.IH snoc.prems by auto
  moreover have \<open>distinct (map move_time (pre @ suf @ [oper]))\<close>
    using pre_suf snoc.prems(3) by auto
  moreover from this have \<open>interp_ops (pre @ suf @ [oper]) = interp_ops (pre @ [oper] @ suf)\<close>
    using interp_op_commute_middle by blast
  ultimately show \<open>interp_ops (ops @ [oper]) = interp_ops ops2\<close>
    by (metis append_assoc interp_ops_step pre_suf)
qed


theorem interp_op_acyclic:
  (* not true as it stands -- nitpick finds a counterexample *)
  assumes \<open>\<And>x. \<not> ancestor tree1 x x\<close>
    and \<open>interp_op oper (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>\<And>x. \<not> ancestor tree2 x x\<close>
  oops


end