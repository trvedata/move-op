theory Move
  imports Main CRDT.Network
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

lemma interp_ops_Nil [simp]:
  shows \<open>interp_ops [] = ([], {})\<close>
  by(clarsimp simp add: interp_ops_def)

lemma distinct_list_pick1:
  assumes \<open>set (xs @ [x]) = set (ys @ [x] @ zs)\<close>
    and \<open>distinct (xs @ [x])\<close> and \<open>distinct (ys @ [x] @ zs)\<close>
  shows \<open>set xs = set (ys @ zs)\<close>
using assms by (induction xs) (fastforce+)

lemma interp_op_commute_base:
  assumes \<open>t1 < t2\<close>
    and \<open>\<And>p1 p2 c. (p1, c) \<in> tree \<Longrightarrow> (p2, c) \<in> tree \<Longrightarrow> p1 = p2\<close>
  shows \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) ([], tree)) =
         interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) ([], tree))\<close>
proof -
  obtain tree1 where tree1: \<open>do_op (Move t1 p1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 c1, tree1)\<close>
    by simp
  obtain tree12 where tree12: \<open>do_op (Move t2 p2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 c2, tree12)\<close>
    by simp
  obtain tree2 where tree2: \<open>do_op (Move t2 p2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 c2, tree2)\<close>
    by simp
  hence undo2: \<open>undo_op (LogMove t2 (get_parent tree c2) p2 c2, tree2) = tree\<close>
    using assms(2) do_undo_op_inv by metis
  have \<open>\<not> t2 < t1\<close>
    using not_less_iff_gr_or_eq assms(1) by blast
  hence \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) ([], tree)) =
        ([LogMove t2 (get_parent tree1 c2) p2 c2, LogMove t1 (get_parent tree c1) p1 c1], tree12)\<close>
    using tree1 tree12 by auto
  moreover have \<open>interp_op (Move t2 p2 c2) ([], tree) = ([LogMove t2 (get_parent tree c2) p2 c2], tree2)\<close>
    using tree2 by auto
  hence \<open>interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) ([], tree)) =
         redo_op (LogMove t2 (get_parent tree c2) p2 c2) ([LogMove t1 (get_parent tree c1) p1 c1], tree1)\<close>
    using tree1 undo2 assms(1) by auto
  ultimately show ?thesis
    using tree12 by auto
qed

lemma interp_op_log_cons:
  assumes \<open>interp_op (Move t1 p1 c1) (log, tree) = (log2, tree2)\<close>
  shows \<open>\<exists>logop rest. log2 = logop # rest \<and> t1 \<le> log_time logop\<close>
proof(cases log)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons logop rest)
  obtain t2 oldp2 p2 c2 where logop: \<open>logop = LogMove t2 oldp2 p2 c2\<close>
    using log_op.exhaust by blast
  then show ?thesis
  proof(cases \<open>t1 < t2\<close>)
    case True
    obtain tree1 log1 where tree1: \<open>interp_op (Move t1 p1 c1) (rest, undo_op (logop, tree)) = (log1, tree1)\<close>
      by fastforce
    obtain tree12 where \<open>do_op (Move t2 p2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 c2, tree12)\<close>
      by simp
    hence \<open>interp_op (Move t1 p1 c1) (log, tree) =
           (LogMove t2 (get_parent tree1 c2) p2 c2 # log1, tree12)\<close>
      using True local.Cons tree1 logop by auto
    then show ?thesis
      using True assms by auto
  next
    case False
    obtain tree1 where tree1: \<open>do_op (Move t1 p1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 c1, tree1)\<close>
      by simp
    hence \<open>interp_op (Move t1 p1 c1) (log, tree) =
           (LogMove t1 (get_parent tree c1) p1 c1 # log, tree1)\<close>
      using False local.Cons logop by auto
    then show ?thesis
      using assms by auto
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
  then show ?case using interp_op_commute_base by metis
next
  case (Cons logop log)
  have parent0: \<open>\<And>p1 c p2. (p1, c) \<in> undo_op (logop, tree) \<Longrightarrow> (p2, c) \<in> undo_op (logop, tree) \<Longrightarrow> p1 = p2\<close>
    sorry
  obtain t3 oldp3 p3 c3 where logop: \<open>logop = LogMove t3 oldp3 p3 c3\<close>
    using log_op.exhaust by blast
  then consider (c1) \<open>t3 < t1\<close> | (c2) \<open>t1 < t3 \<and> t3 < t2\<close> | (c3) \<open>t2 < t3\<close>
    using Cons.prems(3) by force
  then show ?case
  proof(cases)
    case c1 (* t3 < t1 < t2 *)
    obtain tree1 where tree1: \<open>do_op (Move t1 p1 c1, tree) = (LogMove t1 (get_parent tree c1) p1 c1, tree1)\<close>
      by simp
    obtain tree12 where tree12: \<open>do_op (Move t2 p2 c2, tree1) = (LogMove t2 (get_parent tree1 c2) p2 c2, tree12)\<close>
      by simp
    obtain tree2 where tree2: \<open>do_op (Move t2 p2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 c2, tree2)\<close>
      by simp
    hence undo2: \<open>undo_op (LogMove t2 (get_parent tree c2) p2 c2, tree2) = tree\<close>
      using Cons.prems(2) do_undo_op_inv by metis
    have \<open>\<not> t2 < t1\<close>
      using not_less_iff_gr_or_eq Cons.prems(1) by blast
    hence \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (logop # log, tree)) =
           ([LogMove t2 (get_parent tree1 c2) p2 c2, LogMove t1 (get_parent tree c1) p1 c1, logop] @ log, tree12)\<close>
      using tree1 tree12 logop c1 by auto
    moreover have \<open>t3 < t2\<close>
      using c1 Cons.prems(1) by auto
    hence \<open>interp_op (Move t2 p2 c2) (logop # log, tree) = (LogMove t2 (get_parent tree c2) p2 c2 # logop # log, tree2)\<close>
      using tree2 logop by auto
    hence \<open>interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (logop # log, tree)) =
           redo_op (LogMove t2 (get_parent tree c2) p2 c2) (LogMove t1 (get_parent tree c1) p1 c1 # logop # log, tree1)\<close>
      using Cons.prems(1) c1 logop tree1 undo2 by auto
    ultimately show ?thesis
      using tree12 by auto
  next
    case c2 (* t1 < t3 < t2 *)
    obtain tree1 log1 where tree1: \<open>interp_op (Move t1 p1 c1) (log, undo_op (logop, tree)) = (log1, tree1)\<close>
      by fastforce
    obtain tree13 where tree13: \<open>do_op (Move t3 p3 c3, tree1) = (LogMove t3 (get_parent tree1 c3) p3 c3, tree13)\<close>
      by simp
    obtain tree132 where tree132: \<open>do_op (Move t2 p2 c2, tree13) = (LogMove t2 (get_parent tree13 c2) p2 c2, tree132)\<close>
      by simp
    obtain tree2 where tree2: \<open>do_op (Move t2 p2 c2, tree) = (LogMove t2 (get_parent tree c2) p2 c2, tree2)\<close>
      by simp
    hence undo2: \<open>undo_op (LogMove t2 (get_parent tree c2) p2 c2, tree2) = tree\<close>
      by (metis Cons.prems(2) do_undo_op_inv)
    have \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (logop # log, tree)) =
           (LogMove t2 (get_parent tree13 c2) p2 c2 # LogMove t3 (get_parent tree1 c3) p3 c3 # log1, tree132)\<close>
      using c2 logop tree1 tree13 tree132 by auto
    moreover have \<open>interp_op (Move t2 p2 c2) (logop # log, tree) =
                   (LogMove t2 (get_parent tree c2) p2 c2 # logop # log, tree2)\<close>
      using c2 logop tree2 by auto
    hence \<open>interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (logop # log, tree)) =
           (LogMove t2 (get_parent tree13 c2) p2 c2 # LogMove t3 (get_parent tree1 c3) p3 c3 # log1, tree132)\<close>
      using assms(1) undo2 c2 logop tree1 tree13 tree132 by auto
    ultimately show ?thesis by simp
  next
    case c3 (* t1 < t2 < t3 *)
    obtain tree1 log1 where tree1: \<open>interp_op (Move t1 p1 c1) (log, undo_op (logop, tree)) = (log1, tree1)\<close>
      by fastforce
    obtain tree13 where tree13: \<open>do_op (Move t3 p3 c3, tree1) = (LogMove t3 (get_parent tree1 c3) p3 c3, tree13)\<close>
      by simp
    hence undo13: \<open>undo_op (LogMove t3 (get_parent tree1 c3) p3 c3, tree13) = tree1\<close>
    proof -
      have \<open>\<And>p1 p2 c. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2\<close>
        by (meson interp_op_unique_parent parent0 tree1)
      thus ?thesis
        using do_undo_op_inv tree13 by metis
    qed
    obtain tree12 log12 where tree12: \<open>interp_op (Move t2 p2 c2) (log1, tree1) = (log12, tree12)\<close>
      by fastforce
    obtain tree123 where tree123: \<open>do_op (Move t3 p3 c3, tree12) = (LogMove t3 (get_parent tree12 c3) p3 c3, tree123)\<close>
      by simp
    obtain tree2 log2 where tree2: \<open>interp_op (Move t2 p2 c2) (log, undo_op (logop, tree)) = (log2, tree2)\<close>
      by fastforce
    obtain tree21 log21 where tree21: \<open>interp_op (Move t1 p1 c1) (log2, tree2) = (log21, tree21)\<close>
      by fastforce
    obtain tree213 where tree213: \<open>do_op (Move t3 p3 c3, tree21) = (LogMove t3 (get_parent tree21 c3) p3 c3, tree213)\<close>
      by simp
    obtain tree23 where tree23: \<open>do_op (Move t3 p3 c3, tree2) = (LogMove t3 (get_parent tree2 c3) p3 c3, tree23)\<close>
      by simp
    hence undo23: \<open>undo_op (LogMove t3 (get_parent tree2 c3) p3 c3, tree23) = tree2\<close>
    proof -
      have \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
        by (meson interp_op_unique_parent parent0 tree2)
      thus ?thesis
        using do_undo_op_inv tree23 by metis
    qed
    have \<open>interp_op (Move t1 p1 c1) (logop # log, tree) =
           (LogMove t3 (get_parent tree1 c3) p3 c3 # log1, tree13)\<close>
      using assms(1) c3 logop tree1 tree13 by auto
    hence \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (logop # log, tree)) =
           (LogMove t3 (get_parent tree12 c3) p3 c3 # log12, tree123)\<close>
      using c3 tree12 tree123 undo13 by auto
    moreover have \<open>interp_op (Move t2 p2 c2) (logop # log, tree) =
          (LogMove t3 (get_parent tree2 c3) p3 c3 # log2, tree23)\<close>
      using c3 logop tree2 tree23 by auto
    hence \<open>interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (logop # log, tree)) =
           (LogMove t3 (get_parent tree21 c3) p3 c3 # log21, tree213)\<close>
      using assms(1) c3 undo23 tree21 tree213 by auto
    moreover have \<open>interp_op (Move t2 p2 c2) (interp_op (Move t1 p1 c1) (log, undo_op (logop, tree))) =
                   interp_op (Move t1 p1 c1) (interp_op (Move t2 p2 c2) (log, undo_op (logop, tree)))\<close>
      using Cons.IH Cons.prems(3) assms(1) parent0 by auto
    ultimately show ?thesis
      using tree1 tree12 tree123 tree2 tree21 tree213 by auto
  qed
qed

lemma interp_op_commute_last:
  assumes \<open>distinct ((map move_time ops) @ [t1, t2])\<close>
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
    have \<open>distinct ((map move_time (xs @ ys)) @ [move_time y, move_time oper])\<close>
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