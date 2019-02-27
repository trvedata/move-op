theory Move
  imports Main
begin

datatype ('time, 'node) operation
  = Move 'time "'node option" 'node

datatype ('time, 'node) log_op
  = UndoMove (timestamp: 'time) (old_parent: "'node option")
      (new_parent: "'node option") (child: 'node)
(*
datatype 'node tree   
  = Node 'node \<open>'node tree fset\<close>
*)
fun applyop :: \<open>('t, 'n) log_op \<Rightarrow> ('n option \<times> 'n) set \<Rightarrow> ('n option \<times> 'n) set\<close> where
  \<open>applyop (UndoMove t oldp newp c) ns =
     ({ (x, y) | x y. (x, y) \<in> ns \<and> y \<noteq> c } \<union> {(newp, c)})\<close>

definition find_unique :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a option\<close> where
  \<open>find_unique P ss \<equiv>
     if \<exists>!x\<in>ss. P x then
       Some (THE x. x \<in> ss \<and> P x)
     else None\<close>

fun applyoper :: \<open>('t, 'n) operation \<Rightarrow> ('n option \<times> 'n) set \<Rightarrow> ('n option \<times> 'n) set \<times> ('t, 'n) log_op\<close> where
  \<open>applyoper (Move t p c) ns =
     ({ (x, y) | x y. (x, y) \<in> ns \<and> y \<noteq> c } \<union> {(p, c)}, UndoMove t (THE p. undefined) p c)\<close>

fun undoop :: \<open>('t, 'n) log_op \<Rightarrow> ('n option \<times> 'n) set \<Rightarrow> ('n option \<times> 'n) set\<close> where
  \<open>undoop (UndoMove t oldp newp c) ns = applyop (UndoMove t newp oldp c) ns\<close>

lemma undoop_applyop_inv1: 
  assumes \<open>ls = UndoMove t oldp newp c\<close>
    and \<open>(oldp, c) \<in> ns\<close>
    and \<open>\<And>x. (x, c) \<in> ns \<Longrightarrow> x = oldp\<close>
  shows \<open>undoop ls (applyop ls ns) = ns\<close>
  using assms
  apply -
  apply clarify
  apply(subst undoop.simps, (subst applyop.simps)+)
  apply(rule equalityI)
   apply(rule subsetI)
   apply clarify
   apply(erule UnE)
    apply(drule CollectD)
    apply(erule exE)+
    apply clarify
   apply(erule UnE)
    apply(drule CollectD)
    apply(erule exE)+
     apply clarify+
  apply(rule_tac x=a in exI)
  apply(rule_tac x=b in exI)
  apply(rule conjI)
   apply force
  apply(rule conjI)
   apply(subst (asm) de_Morgan_conj)
   apply(erule disjE)
  apply(case_tac \<open>b = c\<close>, force)
    apply(rule UnI1)
    apply(rule CollectI)
  apply(rule_tac x=a in exI)
    apply(rule_tac x=b in exI)
    apply(rule conjI)
     apply force
    apply force
   apply(rule UnI1)
   apply(rule CollectI)
  apply(rule_tac x=a in exI)
   apply(rule_tac x=b in exI)
    apply(rule conjI)
     apply force
   apply force
  apply force
  done

lemma undoop_applyop_inv2: 
  assumes \<open>ls = UndoMove t oldp newp c\<close>
    and \<open>(newp, c) \<in> ns\<close>
    and \<open>\<And>x. (x, c) \<in> ns \<Longrightarrow> x = newp\<close>
  shows \<open>applyop ls (undoop ls ns) = ns\<close>
  using assms
  apply -
  apply clarify
  apply(subst undoop.simps, (subst applyop.simps)+)
  apply(rule equalityI)
   apply(rule subsetI)
   apply clarify
   apply(erule UnE)
    apply(drule CollectD)
    apply(erule exE)+
    apply clarify
   apply(erule UnE)
    apply(drule CollectD)
    apply(erule exE)+
     apply clarify+
  apply(rule_tac x=a in exI)
  apply(rule_tac x=b in exI)
  apply(rule conjI)
   apply force
  apply(rule conjI)
   apply(subst (asm) de_Morgan_conj)
   apply(erule disjE)
    apply(case_tac \<open>b = c\<close>)
  apply blast
    apply(rule UnI1)
    apply(rule CollectI)
  apply(rule_tac x=a in exI)
    apply(rule_tac x=b in exI)
    apply(rule conjI)
      apply force
  apply(rule conjI)
     apply force
  apply assumption
   apply(rule UnI1)
   apply(rule CollectI)
  apply(rule_tac x=a in exI)
   apply(rule_tac x=b in exI)
    apply(rule conjI)
     apply force
   apply force
  apply force
  done

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