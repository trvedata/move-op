theory Move
  imports Main
begin

datatype ('time, 'node) operation
  = Move (move_time: 'time) (move_parent: 'node) (move_child: 'node)

datatype ('time, 'node) log_op
  = LogMove (log_time: 'time) (old_parent: \<open>'node option\<close>) (new_parent: 'node) (log_child: 'node)

(*
datatype 'node tree   
  = Node 'node \<open>'node tree fset\<close>
*)

definition get_parent :: \<open>'n \<Rightarrow> ('n \<times> 'n) set \<Rightarrow> 'n option\<close> where
  \<open>get_parent ch tree \<equiv>
     if \<exists>!parent. (parent, ch) \<in> tree then
       Some (THE parent. (parent, ch) \<in> tree)
     else None\<close>

inductive ancestor :: "('n \<times> 'n) set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool" where
  "\<lbrakk>(parent, child) \<in> tree\<rbrakk> \<Longrightarrow> ancestor tree parent child" |
  "\<lbrakk>(parent, child) \<in> tree; ancestor tree anc parent\<rbrakk> \<Longrightarrow> ancestor tree anc child"

fun apply_op :: \<open>('t, 'n) operation \<times> ('n \<times> 'n) set \<Rightarrow> ('t, 'n) log_op \<times> ('n \<times> 'n) set\<close> where
  \<open>apply_op (Move t newp c, tree) =
     (LogMove t (get_parent c tree) newp c,
      if ancestor tree c newp then tree
      else {(p', c') \<in> tree. c' \<noteq> c} \<union> {(newp, c)})\<close>

fun undo_op :: \<open>('t, 'n) log_op \<times> ('n \<times> 'n) set \<Rightarrow> ('n \<times> 'n) set\<close> where
  \<open>undo_op (LogMove t None newp c, tree) = {(p', c') \<in> tree. c' \<noteq> c}\<close> |
  \<open>undo_op (LogMove t (Some oldp) newp c, tree) =
     {(p', c') \<in> tree. c' \<noteq> c} \<union> {(oldp, c)}\<close>

fun reapply_op :: \<open>('t, 'n) log_op \<Rightarrow> ('t, 'n) log_op list \<times> ('n \<times> 'n) set \<Rightarrow> ('t, 'n) log_op list \<times> ('n \<times> 'n) set\<close> where
  \<open>reapply_op (LogMove t _ p c) (ops, tree) =
     (let (op2, tree2) = apply_op (Move t p c, tree)
      in (op2 # ops, tree2))\<close>

fun add_op :: \<open>('t::{linorder}, 'n) operation \<Rightarrow> ('n \<times> 'n) set \<Rightarrow> ('t, 'n) log_op list \<Rightarrow> ('t, 'n) log_op list \<times> ('n \<times> 'n) set\<close> where
  \<open>add_op op1 tree1 [] =
     (let (op2, tree2) = apply_op (op1, tree1)
      in ([op2], tree2))\<close> |
  \<open>add_op op1 tree1 (logop # ops) =
     (if move_time op1 < log_time logop
      then reapply_op logop (add_op op1 (undo_op (logop, tree1)) ops)
      else let (op2, tree2) = apply_op (op1, tree1) in (op2 # ops, tree2))\<close>

lemma get_parent_None:
  assumes \<open>\<nexists>p. (p, c) \<in> tree\<close>
  shows \<open>get_parent c tree = None\<close>
by (meson assms get_parent_def)

lemma get_parent_Some:
  assumes \<open>(p, c) \<in> tree\<close>
    and \<open>\<And>x. (x, c) \<in> tree \<Longrightarrow> x = p\<close>
  shows \<open>get_parent c tree = Some p\<close>
proof -
  have \<open>\<exists>!parent. (parent, c) \<in> tree\<close>
    using assms by metis
  hence \<open>(THE parent. (parent, c) \<in> tree) = p\<close>
    using assms(2) by fastforce
  thus \<open>get_parent c tree = Some p\<close>
    using assms get_parent_def by metis
qed

lemma apply_undo_inv:
  assumes \<open>\<And>x. (x, c) \<in> tree \<Longrightarrow> x = oldp\<close>
  shows \<open>undo_op (apply_op (Move t p c, tree)) = tree\<close>
proof(cases \<open>\<exists>par. (par, c) \<in> tree\<close>)
  case True
  hence 1: \<open>(oldp, c) \<in> tree\<close>
    using assms by blast
  hence 2: \<open>get_parent c tree = Some oldp\<close>
    using assms get_parent_Some by metis
  moreover have \<open>\<And>p' c'. (p', c') \<in> tree \<Longrightarrow> (p', c') \<in> undo_op (apply_op (Move t p c, tree))\<close>
    using assms calculation by auto
  moreover have \<open>\<And>p' c'. (p', c') \<in> undo_op (apply_op (Move t p c, tree)) \<Longrightarrow> (p', c') \<in> tree\<close>
    using 1 2 by (cases \<open>ancestor tree c p\<close>, auto)
  ultimately show ?thesis
    by (meson pred_equals_eq2)
next
  case no_old_parent: False
  hence \<open>get_parent c tree = None\<close>
    using assms get_parent_None by metis
  moreover have \<open>{(p', c') \<in> tree. c' \<noteq> c} = tree\<close>
    using no_old_parent by fastforce
  moreover from this have \<open>{(p', c') \<in> (tree \<union> {(p, c)}). c' \<noteq> c} = tree\<close>
    by auto
  ultimately show ?thesis by simp
qed


find_consts name: List

fun find_position :: \<open>('time::{linorder}, 'node) log_op list \<Rightarrow> 'time \<Rightarrow>
                        ('time, 'node) log_op list \<times> ('time, 'node) log_op list\<close> where
  \<open>find_position ls t =
     (List.filter (\<lambda>x. timestamp x < t) ls, List.filter (\<lambda>x. timestamp x > t) ls)\<close>

fun undo_all :: \<open>('time, 'node) log_op list \<Rightarrow> ('node option \<times> 'node) set \<Rightarrow> ('node option \<times> 'node) set\<close> where
  \<open>undo_all [] tree = tree\<close> |
  \<open>undo_all (x#xs) tree = undo_all xs (undoop x tree)\<close>

fun interpret_oplist :: \<open>('node option \<times> 'node) set \<Rightarrow> ('time::{linorder},'node) operation \<Rightarrow> ('time, 'node) log_op list  \<Rightarrow>
                            ('node option \<times> 'node) set \<times> ('time, 'node) log_op list\<close> where
  \<open>interpret_oplist forest (Move t p c) log =
     (let (ls, gs) = find_position log t;
          nt       = undo_all gs forest
      in undefined)\<close>

(*fun find_position :: \<open>('time, 'node) log_op list \<Rightarrow> 'time \<Rightarrow>

fun update_tree :: \<open>'node tree \<Rightarrow> ('time,'node) operation \<Rightarrow> 'node tree\<close> where
  \<open>update_tree tree oper = tree\<close>

fun interpret_oplist :: \<open>'node tree \<Rightarrow> ('time::{linorder},'node) operation \<Rightarrow> ('time, 'node) log_op list  \<Rightarrow>
                            'node tree \<times> ('time, 'node) log_op list\<close> where
  \<open>interpret_oplist tree (Move t p c) [] = (update_tree tree (Move t p c), [UndoMove t None p c])\<close>
| \<open>interpret_oplist tree (Move t p c) ((UndoMove t' p' c') # ops) =
    if t < t' then
      (UndoMove t' p' c') # interp_oplist (undo_op (UndoMove t' p' c') tree) (Move t p c) ops
    else *)

end