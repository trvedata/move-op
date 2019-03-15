theory Move
  imports Main
begin

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
      if ancestor tree c newp then tree
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
  \<open>interp_ops ops \<equiv> foldl (\<lambda>state op. interp_op op state) ([], {}) ops\<close>

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
    using 1 2 by (cases \<open>ancestor tree c p\<close>, auto)
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

lemma do_op_unique_parent:
  assumes \<open>\<And>p1 p2 c. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2\<close>
    and \<open>do_op (Move t newp c, tree1) = (log_oper, tree2)\<close>
  shows \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
proof(cases \<open>ancestor tree1 c newp\<close>)
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

lemma interp_op_unique_parent:
  assumes \<open>\<And>p1 p2 c. (p1, c) \<in> tree1 \<Longrightarrow> (p2, c) \<in> tree1 \<Longrightarrow> p1 = p2\<close>
    and \<open>interp_op oper (ops1, tree1) = (ops2, tree2)\<close>
  shows \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
using assms proof(induct ops1)
  case Nil
  have "\<forall>pair. snd (case pair of (p1, p2) \<Rightarrow> ([p1], p2)) = snd pair"
    by simp
  hence \<open>\<exists>log_op. do_op (oper, tree1) = (log_op, tree2)\<close>
    by (metis Nil.prems(4) interp_op.simps(1) old.prod.exhaust snd_conv)
  thus \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
    by (metis assms(1) do_op_unique_parent operation.exhaust)
next
  case (Cons logop ops)
  then show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
  proof(cases \<open>move_time oper < log_time logop\<close>)
    case True
    then show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
      sorry
  next
    case False
    then show \<open>\<And>p1 p2 c. (p1, c) \<in> tree2 \<Longrightarrow> (p2, c) \<in> tree2 \<Longrightarrow> p1 = p2\<close>
      sorry
  qed
qed



theorem interp_op_commutes:
  (* missing some assumptions *)
  shows \<open>interp_op op1 \<circ> interp_op op2 = interp_op op2 \<circ> interp_op op1\<close>
  oops

end