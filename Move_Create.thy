theory Move_Create
  imports Move
begin

section \<open>Applying ops in timestamp order\<close>

text \<open>We now show that if a list of operations is in sorted order, applying
those ops with apply_ops is equivalent to a simpler function in which we
only evaluate operations using do_op (never undoing or redoing anything).\<close>

fun apply_do_op :: \<open>('t, 'n, 'm) state \<Rightarrow> ('t, 'n, 'm) operation \<Rightarrow> ('t, 'n, 'm) state\<close> where
  \<open>apply_do_op (log, tree) op =
    (let (logop, tree') = do_op (op, tree) in (logop # log, tree'))\<close>

definition do_ops :: \<open>('t, 'n, 'm) operation list \<Rightarrow> ('t, 'n, 'm) state\<close> where
  \<open>do_ops ops \<equiv> foldl apply_do_op ([], {}) ops\<close>

lemma apply_do_op_snd:
  shows \<open>snd (apply_do_op (log, tree) oper) = snd (do_op (oper, tree))\<close>
  by (simp add: prod.case_eq_if)

lemma do_ops_apply_last:
  assumes \<open>do_ops ops = (log1, tree1)\<close>
    and \<open>do_ops (ops @ [Move t p m c]) = (log2, tree2)\<close>
  shows \<open>tree2 = (if ancestor tree1 c p \<or> c = p then tree1
                  else {(p', m', c') \<in> tree1. c' \<noteq> c} \<union> {(p, m, c)})\<close>
proof -
  have \<open>do_ops (ops @ [Move t p m c]) = apply_do_op (log1, tree1) (Move t p m c)\<close>
    by (metis (no_types, lifting) assms(1) do_ops_def foldl_Cons foldl_Nil foldl_append)
  hence \<open>tree2 = snd (do_op (Move t p m c, tree1))\<close>
    using assms(2) by auto
  thus ?thesis
    by simp
qed

lemma strict_sorted_map_snoc:
  assumes \<open>strict_sorted (map f (xs @ [x]))\<close>
  shows \<open>strict_sorted (map f xs)\<close>
using assms proof (induction xs)
  case Nil
  then show \<open>strict_sorted (map f [])\<close>
    by simp
next
  case (Cons y xs)
  hence \<open>\<forall>z \<in> set (map f (xs @ [x])). f y < z\<close>
    by auto
  thus \<open>strict_sorted (map f (y # xs))\<close>
    by (metis Cons.prems map_append sorted_wrt_append strict_sorted_sorted_wrt)
qed

lemma strict_sorted_map_snoc_less:
  assumes \<open>strict_sorted (map f (xs @ [x]))\<close>
  shows \<open>\<forall>v \<in> set (map f xs). v < f x\<close>
using assms proof (induction xs)
  case Nil
  then show \<open>\<forall>v \<in> set (map f []). v < f x\<close>
    by simp
next
  case (Cons y xs)
  hence \<open>\<forall>v \<in> set (map f xs). v < f x\<close>
    by simp
  moreover have \<open>\<forall>v \<in> set (map f (xs @ [x])). f y < v\<close>
    using Cons.prems by auto
  ultimately show \<open>\<forall>v \<in> set (map f (y # xs)). v < f x\<close>
    by simp
qed

theorem apply_ops_do_ops:
  assumes \<open>strict_sorted (map move_time ops)\<close>
  shows \<open>apply_ops ops = do_ops ops\<close>
using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show \<open>apply_ops [] = do_ops []\<close>
    by (simp add: do_ops_def)
next
  case (snoc oper ops)
  hence \<open>apply_ops ops = do_ops ops\<close>
    by (simp add: strict_sorted_map_snoc)
  obtain log tree where state: \<open>apply_ops ops = (log, tree)\<close>
    by fastforce
  have \<open>apply_op oper (log, tree) = apply_do_op (log, tree) oper\<close>
  proof (cases log)
    case Nil
    then show ?thesis by simp
  next
    case (Cons logop log')
    have \<open>distinct (map move_time ops)\<close>
      by (meson snoc.prems strict_sorted_iff strict_sorted_map_snoc)
    moreover have \<open>\<forall>t \<in> set (map move_time ops). t < move_time oper\<close>
      by (meson snoc.prems strict_sorted_map_snoc_less)
    hence \<open>\<forall>t \<in> set (map log_time log). t < move_time oper\<close>
      using apply_ops_timestamps calculation state by blast
    hence \<open>move_time oper > log_time logop\<close>
      by (simp add: local.Cons)
    hence \<open>apply_op oper (log, tree) = (let (op2, tree2) = do_op (oper, tree) in (op2 # log, tree2))\<close>
      using local.Cons by auto
    thus \<open>apply_op oper (log, tree) = apply_do_op (log, tree) oper\<close>
      by simp
  qed
  then show \<open>apply_ops (ops @ [oper]) = do_ops (ops @ [oper])\<close>
    by (metis (no_types, lifting) \<open>apply_ops ops = do_ops ops\<close> apply_ops_step do_ops_def foldl.simps(1) foldl.simps(2) foldl_append state)
qed

lemma do_ops_tree_parent:
  assumes \<open>do_ops ops = (log, tree)\<close>
    and \<open>(p, m, c) \<in> tree\<close>
  shows \<open>\<exists>oper \<in> set ops. move_parent oper = p\<close>
using assms proof (induction ops arbitrary: log tree rule: List.rev_induct)
  case Nil
  then show \<open>\<exists>oper \<in> set []. move_parent oper = p\<close>
    by (simp add: do_ops_def)
next
  case (snoc oper ops)
  then show \<open>\<exists>oper \<in> set (ops @ [oper]). move_parent oper = p\<close>
  proof (cases \<open>move_parent oper = p\<close>)
    case True
    then show ?thesis by auto
  next
    case False
    obtain log' tree' where \<open>do_ops ops = (log', tree')\<close>
      by fastforce
    hence \<open>do_ops (ops @ [oper]) = (let (logop, tree2) = do_op (oper, tree') in (logop # log', tree2))\<close>
      by (simp add: do_ops_def)
    then obtain logop where logop: \<open>do_op (oper, tree') = (logop, tree)\<close>
      by (metis (mono_tags, lifting) prod.exhaust_sel prod.sel(2) snoc.prems(1) split_beta)
    obtain op_t op_p op_m op_c where oper: \<open>oper = Move op_t op_p op_m op_c\<close>
      using operation.exhaust_sel by blast
    then show ?thesis
    proof (cases \<open>ancestor tree' op_c op_p \<or> op_c = op_p\<close>)
      case True
      hence \<open>tree = tree'\<close>
        using oper logop by auto
      then show \<open>\<exists>oper \<in> set (ops @ [oper]). move_parent oper = p\<close>
        using \<open>do_ops ops = (log', tree')\<close> snoc.IH snoc.prems(2) by auto
    next
      case non_ancestor: False
      have \<open>op_p \<noteq> p\<close>
        using False oper by auto
      have \<open>tree = {(p', m', c') \<in> tree'. c' \<noteq> op_c} \<union> {(op_p, op_m, op_c)}\<close>
        using logop oper non_ancestor by auto
      hence \<open>(p, m, c) \<in> tree'\<close>
        using snoc.prems(2) \<open>op_p \<noteq> p\<close> by blast
      then show \<open>\<exists>oper \<in> set (ops @ [oper]). move_parent oper = p\<close>
        using \<open>do_ops ops = (log', tree')\<close> snoc.IH by auto
    qed
  qed
qed

lemma do_ops_tree_child:
  assumes \<open>do_ops ops = (log, tree)\<close>
    and \<open>(p, m, c) \<in> tree\<close>
  shows \<open>\<exists>oper \<in> set ops. move_child oper = c\<close>
using assms proof (induction ops arbitrary: log tree rule: List.rev_induct)
  case Nil
  then show \<open>\<exists>oper \<in> set []. move_child oper = c\<close>
    by (simp add: do_ops_def)
next
  case (snoc oper ops)
  then show \<open>\<exists>oper \<in> set (ops @ [oper]). move_child oper = c\<close>
  proof (cases \<open>move_child oper = c\<close>)
    case True
    then show ?thesis by simp
  next
    case False
    obtain log' tree' where \<open>do_ops ops = (log', tree')\<close>
      by fastforce
    hence \<open>do_ops (ops @ [oper]) = (let (logop, tree2) = do_op (oper, tree') in (logop # log', tree2))\<close>
      by (simp add: do_ops_def)
    then obtain logop where logop: \<open>do_op (oper, tree') = (logop, tree)\<close>
      by (metis (mono_tags, lifting) prod.exhaust_sel prod.sel(2) snoc.prems(1) split_beta)
    obtain op_t op_p op_m op_c where oper: \<open>oper = Move op_t op_p op_m op_c\<close>
      using operation.exhaust_sel by blast
    then show ?thesis
    proof (cases \<open>ancestor tree' op_c op_p \<or> op_c = op_p\<close>)
      case True
      hence \<open>tree = tree'\<close>
        using oper logop by auto
      then show \<open>\<exists>oper \<in> set (ops @ [oper]). move_child oper = c\<close>
        using \<open>do_ops ops = (log', tree')\<close> snoc.IH snoc.prems(2) by auto
    next
      case non_ancestor: False
      have \<open>op_c \<noteq> c\<close>
        using False oper by auto
      have \<open>tree = {(p', m', c') \<in> tree'. c' \<noteq> op_c} \<union> {(op_p, op_m, op_c)}\<close>
        using logop oper non_ancestor by auto
      hence \<open>(p, m, c) \<in> tree'\<close>
        using snoc.prems(2) \<open>op_c \<noteq> c\<close> by blast
      then show \<open>\<exists>oper \<in> set (ops @ [oper]). move_child oper = c\<close>
        using \<open>do_ops ops = (log', tree')\<close> snoc.IH by auto
    qed
  qed
qed

lemma do_ops_child_monotonic:
  assumes \<open>foldl apply_do_op (log1, tree1) ops = (log2, tree2)\<close>
    and \<open>(p, m, c) \<in> tree1\<close>
  shows \<open>\<exists>p m. (p, m, c) \<in> tree2\<close>
using assms proof (induction ops arbitrary: log2 tree2 rule: List.rev_induct)
  case Nil
  then show \<open>\<exists>p m. (p, m, c) \<in> tree2\<close>
    by auto
next
  case (snoc oper ops)
  obtain op_t op_p op_m op_c where oper: \<open>oper = Move op_t op_p op_m op_c\<close>
    using operation.exhaust_sel by blast
  obtain log3 tree3 where tree3: \<open>foldl apply_do_op (log1, tree1) ops = (log3, tree3)\<close>
    by fastforce
  then obtain p3 m3 where \<open>(p3, m3, c) \<in> tree3\<close>
    using snoc.IH snoc.prems(2) by blast
  then show ?case
  proof (cases \<open>ancestor tree3 op_c op_p \<or> op_c = op_p\<close>)
    case True
    hence \<open>tree2 = tree3\<close>
      using snoc.prems(1) tree3 oper by auto
    then show \<open>\<exists>p m. (p, m, c) \<in> tree2\<close>
      using \<open>(p3, m3, c) \<in> tree3\<close> by blast
  next
    case False
    hence \<open>tree2 = {(p', m', c') \<in> tree3. c' \<noteq> op_c} \<union> {(op_p, op_m, op_c)}\<close>
      using oper snoc.prems(1) tree3 by auto
    then show \<open>\<exists>p m. (p, m, c) \<in> tree2\<close>
      using \<open>(p3, m3, c) \<in> tree3\<close> by (cases \<open>op_c = c\<close>; auto)
  qed
qed


section \<open>Create operations\<close>

text \<open>A move operation whose child does not yet exist in the tree implicitly
creates that child node. Thus, the first (lowest-timestamped) move operation
that references a particular child node can be regarded as the ``create''
operation for that node.

We now show that it is possible to order all create operations ahead of all
non-create move operations in the log. This has the performance advantage that
create operations don't need to be undone and redone when applying a move
operation; in workloads that consist mostly of create operations, and only few
non-create move operations, this can bring a substantial cost saving.

This optimisation requires additional assumptions: firstly, the parent node in
any move/create operation must exist in the tree; secondly, the creation
operation for a given node must be unique (i.e. there cannot be two operations
that both create the same node). These assumptions are easily satisfied in
practice.

The parent_exists predicate allows the first assumption to be captured. It
requires the parent of every operation to either be one of a fixed set of
root nodes (which may be e.g. the actual tree root and the trash node), or to
be the child of a prior move/create operation.\<close>

inductive parent_exists :: \<open>'n set \<Rightarrow> ('t, 'n, 'm) operation list \<Rightarrow> bool\<close> where
  \<open>parent_exists roots []\<close> |
  \<open>\<lbrakk>parent_exists roots ops; p \<in> roots\<rbrakk> \<Longrightarrow> parent_exists roots (ops @ [Move t p m c])\<close> |
  \<open>\<lbrakk>parent_exists roots ops;
    do_ops ops = (log, tree);
    \<exists>a m. (a, m, p) \<in> tree\<rbrakk> \<Longrightarrow> parent_exists roots (ops @ [Move t p m c])\<close>

inductive_cases parent_exists_indcases: \<open>parent_exists roots ops\<close>

lemma parent_exists_snoc:
  assumes \<open>parent_exists roots (ops @ [oper])\<close>
  shows \<open>parent_exists roots ops\<close>
  using assms apply(rule parent_exists.cases)
  by blast+

lemma parent_exists_tree:
  assumes \<open>parent_exists roots (ops @ [Move t p m c])\<close>
    and \<open>do_ops ops = (log, tree)\<close>
  shows \<open>p \<in> roots \<or> (\<exists>a m. (a, m, p) \<in> tree)\<close>
  using assms(1) apply(rule parent_exists.cases)
  using assms(2) by auto

lemma parent_exists_interpolate:
  assumes \<open>parent_exists roots (ops1 @ ops2 @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2])\<close>
    and \<open>parent_exists roots (ops1 @ [Move t2 p2 m2 c2])\<close>
  shows \<open>parent_exists roots (ops1 @ ops2 @ [Move t2 p2 m2 c2])\<close>
proof -
  have \<open>parent_exists roots (ops1 @ ops2 @ [Move t1 p1 m1 c1])\<close>
    using assms(1) parent_exists_snoc by force
  hence ops12: \<open>parent_exists roots (ops1 @ ops2)\<close>
    using parent_exists_snoc by force
  then show ?thesis
  proof (cases \<open>p2 \<in> roots\<close>)
    case True
    then show \<open>parent_exists roots (ops1 @ ops2 @ [Move t2 p2 m2 c2])\<close>
      using ops12 parent_exists.intros(2) by fastforce
  next
    case False
    obtain log1 tree1 where tree1: \<open>do_ops ops1 = (log1, tree1)\<close>
      by fastforce
    hence \<open>\<exists>a m. (a, m, p2) \<in> tree1\<close>
      by (meson False assms(2) parent_exists_tree)
    obtain log2 tree2 where tree2: \<open>do_ops (ops1 @ ops2) = (log2, tree2)\<close>
      by fastforce
    hence \<open>(log2, tree2) = foldl apply_do_op (log1, tree1) ops2\<close>
      by (metis tree1 do_ops_def foldl_append)
    hence \<open>\<exists>a m. (a, m, p2) \<in> tree2\<close>
      by (metis do_ops_child_monotonic \<open>\<exists>a m. (a, m, p2) \<in> tree1\<close>)
    then show \<open>parent_exists roots (ops1 @ ops2 @ [Move t2 p2 m2 c2])\<close>
      using tree2 ops12 parent_exists.intros(3) by fastforce
  qed
qed

lemma parent_exists_commute:
  assumes \<open>parent_exists roots (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2])\<close>
    and \<open>parent_exists roots (ops @ [Move t2 p2 m2 c2])\<close>
  shows \<open>parent_exists roots (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1])\<close>
proof (cases \<open>p1 \<in> roots\<close>)
  case True
  then show \<open>parent_exists roots (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1])\<close>
    using assms(2) parent_exists.intros(2) by fastforce
next
  case False
  obtain log1 tree1 where tree1: \<open>do_ops ops = (log1, tree1)\<close>
    by fastforce
  obtain log2 tree2 where tree2: \<open>do_ops (ops @ [Move t1 p1 m1 c1]) = (log2, tree2)\<close>
    by fastforce
  have \<open>parent_exists roots (ops @ [Move t1 p1 m1 c1])\<close>
    using assms(1) parent_exists_snoc by force
  hence \<open>\<exists>a m. (a, m, p1) \<in> tree1\<close>
    using parent_exists_tree False tree1 by metis
  hence \<open>\<exists>a m. (a, m, p1) \<in> tree2\<close>
    by (metis (full_types) do_ops_child_monotonic do_ops_def foldl_append tree1 tree2)
  hence \<open>parent_exists roots ((ops @ [Move t2 p2 m2 c2]) @ [Move t1 p1 m1 c1])\<close>
    using assms(2) parent_exists.intros(3) tree2 sorry (* should be easy?! *)
  then show \<open>parent_exists roots (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1])\<close>
    by simp
qed

lemma parent_exists_child:
  assumes \<open>parent_exists roots ops\<close>
    and \<open>do_ops ops = (log, tree)\<close>
    and \<open>(p, m, c) \<in> tree\<close>
  shows \<open>p \<in> roots \<or> (\<exists>(p', m', c') \<in> tree. c' = p)\<close>
using assms proof (induction ops arbitrary: log tree p m c rule: List.rev_induct)
  case Nil
  hence \<open>tree = {}\<close>
    by (simp add: do_ops_def)
  then show ?case
    using Nil.prems(3) by blast
next
  case (snoc oper ops)
  obtain log2 tree2 where tree2: \<open>do_ops ops = (log2, tree2)\<close>
    by fastforce
  obtain op_t op_p op_m op_c where oper: \<open>oper = Move op_t op_p op_m op_c\<close>
    using operation.exhaust_sel by blast
  have IH: \<open>\<And>p m c. (p, m, c) \<in> tree2 \<Longrightarrow> p \<in> roots \<or> (\<exists>(p', m', c') \<in> tree2. c' = p)\<close>
    by (metis (mono_tags, lifting) parent_exists_snoc snoc.IH snoc.prems(1) tree2)
  show \<open>p \<in> roots \<or> (\<exists>(p', m', c') \<in> tree. c' = p)\<close>
  proof (cases \<open>ancestor tree2 op_c op_p \<or> op_c = op_p\<close>)
    case True
    hence \<open>tree = tree2\<close>
      by (metis (no_types, lifting) do_ops_apply_last oper snoc.prems(2) tree2)
    then show ?thesis
      using IH snoc.prems(3) by blast
  next
    case False
    hence tree12: \<open>tree = {(p', m', c') \<in> tree2. c' \<noteq> op_c} \<union> {(op_p, op_m, op_c)}\<close>
      by (metis (mono_tags, lifting) do_ops_apply_last oper snoc.prems(2) tree2)
    then show ?thesis
    proof (cases \<open>op_c = c\<close>)
      case True
      hence exists: \<open>p \<in> roots \<or> (\<exists>a m. (a, m, op_p) \<in> tree2)\<close>
        by (metis (mono_tags, lifting) tree12 UnE curryI curry_case_prod mem_Collect_eq oper
            parent_exists_tree prod.sel(1) singletonD snoc.prems(1) snoc.prems(3) tree2)
      then show ?thesis
      proof (cases \<open>p = op_p\<close>)
        case True
        hence \<open>p \<in> roots \<or> (\<exists>(p', m', c') \<in> tree2. c' = p)\<close>
          using exists by blast
        thus \<open>p \<in> roots \<or> (\<exists>(p', m', c') \<in> tree. c' = p)\<close>
          using UnI1 tree12 by blast
      next
        case False
        thus \<open>p \<in> roots \<or> (\<exists>(p', m', c') \<in> tree. c' = p)\<close>
          using True snoc.prems(3) tree12 by auto
      qed
    next
      case False
      hence \<open>(p, m, c) \<in> tree2\<close>
        using tree12 snoc.prems(3) by blast
      then show ?thesis
        using tree12 IH by fastforce
    qed
  qed
qed

lemma parent_exists_child_subset:
  assumes \<open>parent_exists roots ops\<close>
    and \<open>do_ops ops = (log, tree)\<close>
  shows \<open>{p. \<exists>m c. (p, m, c) \<in> tree} \<subseteq> roots \<union> {c. \<exists>p m. (p, m, c) \<in> tree}\<close>
proof
  fix p
  assume \<open>p \<in> {p. \<exists>m c. (p, m, c) \<in> tree}\<close>
  then obtain m c where \<open>(p, m, c) \<in> tree\<close>
    by fastforce
  hence \<open>p \<in> roots \<or> (\<exists>(p', m', c') \<in> tree. c' = p)\<close>
    by (metis (mono_tags, lifting) assms(1) assms(2) parent_exists_child)
  thus \<open>p \<in> roots \<union> {c. \<exists>p m. (p, m, c) \<in> tree}\<close>
    by blast
qed

lemma ancestor_parent_exists:
  assumes \<open>ancestor tree parent child\<close>
  shows \<open>\<exists>(p, m, c) \<in> tree. p = parent\<close>
using assms by (induction rule: ancestor.induct; blast+)

lemma parent_exists_ancestor:
  assumes \<open>parent_exists roots (ops @ [Move t p m c])\<close>
    and \<open>\<forall>oper \<in> set ops. move_child oper \<noteq> c\<close>
    and \<open>do_ops ops = (log, tree)\<close>
    and \<open>c \<notin> roots\<close>
  shows \<open>\<not> ancestor tree c p\<close>
proof -
  have \<open>\<forall>(p', m', c') \<in> tree. c' \<in> set (map move_child ops)\<close>
    using assms(3) do_ops_tree_child by fastforce
  hence \<open>c \<notin> {c. \<exists>p m. (p, m, c) \<in> tree}\<close>
    using assms(2) by auto
  hence \<open>c \<notin> {p. \<exists>m c. (p, m, c) \<in> tree}\<close>
    using assms(1) assms(3) assms(4) parent_exists_child_subset parent_exists_snoc by blast
  thus \<open>\<not> ancestor tree c p\<close>
    using ancestor_parent_exists by fastforce
qed

lemma do_ops_apply1:
  assumes \<open>parent_exists roots (ops @ [Move t p m c])\<close>
    and \<open>\<forall>oper \<in> set ops. move_child oper \<noteq> c\<close>
    and \<open>do_ops ops = (log, tree)\<close>
    and \<open>c \<notin> roots\<close> and \<open>c \<noteq> p\<close>
  shows \<open>snd (do_ops (ops @ [Move t p m c])) = {(p', m', c') \<in> tree. c' \<noteq> c} \<union> {(p, m, c)}\<close>
proof -
  obtain logop tree2 where tree2: \<open>do_op (Move t p m c, tree) = (logop, tree2)\<close>
    by fastforce
  hence \<open>foldl apply_do_op (log, tree) [Move t p m c] = (logop # log, tree2)\<close>
    by auto
  hence \<open>do_ops (ops @ [Move t p m c]) = (logop # log, tree2)\<close>
    by (metis assms(3) do_ops_def foldl_append)
  moreover have \<open>\<not> ancestor tree c p\<close>
    by (meson assms(1) assms(2) assms(3) assms(4) parent_exists_ancestor)
  ultimately show ?thesis
    using assms(5) tree2 by auto
qed

lemma ancestor_monotone:
  assumes \<open>ancestor tree a b\<close>
  shows \<open>ancestor (tree \<union> {(p, m, c)}) a b\<close>
using assms proof (induction rule: ancestor.induct)
  case (1 parent meta child tree)
  then show \<open>ancestor (tree \<union> {(p, m, c)}) parent child\<close>
    using ancestor.simps by fastforce
next
  case (2 parent meta child tree anc)
  then show \<open>ancestor (tree \<union> {(p, m, c)}) anc child\<close>
    using ancestor.simps by fastforce
qed

(* Intuition behind this lemma: we add a new tree edge from p to c.
   If there is no existing edge starting at c, then after adding the
   edge, c must be a leaf node with no children. Thus, if there was
   previously no path from a to b, and after adding the path there
   now is a path from a to b, then that path must end at b. *)
lemma ancestor_no_new_path:
  assumes \<open>\<not> ancestor tree a b\<close>
    and \<open>\<nexists>m' c'. (c, m', c') \<in> tree\<close>
    and \<open>b \<noteq> c\<close>
  shows \<open>\<not> ancestor (tree \<union> {(p, m, c)}) a b\<close>
  sorry

lemma tree_updates_commute:
  assumes \<open>tree2 = {(p, m, c) \<in> tree1. c \<noteq> c1} \<union> {(p1, m1, c1)}\<close>
    and \<open>tree3 = tree2 \<union> {(p2, m2, c2)}\<close>
    and \<open>tree4 = tree1 \<union> {(p2, m2, c2)}\<close>
    and \<open>tree5 = {(p, m, c) \<in> tree4. c \<noteq> c1} \<union> {(p1, m1, c1)}\<close>
    and \<open>c1 \<noteq> c2\<close>
  shows \<open>tree3 = tree5\<close>
proof -
  have \<open>{(p, m, c) \<in> tree1. c = c1} \<inter> {(p2, m2, c2)} = {}\<close>
    using assms(5) by auto
  moreover have \<open>{(p, m, c) \<in> tree4. c = c1} = {(p, m, c) \<in> tree1. c = c1}\<close>
    using assms(3) assms(5) by auto
  moreover have \<open>{(p, m, c) \<in> tree4. c \<noteq> c1} = tree4 - {(p, m, c) \<in> tree4. c = c1}\<close>
    by auto
  ultimately show \<open>tree3 = tree5\<close>
    using assms(1) assms(2) assms(3) assms(4) by auto
qed

lemma do_ops_commute:
  assumes \<open>parent_exists roots (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2])\<close>
      and \<open>parent_exists roots (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1])\<close>
      and \<open>\<forall>oper \<in> set (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2]).
           move_child oper \<notin> roots \<and> move_child oper \<noteq> move_parent oper\<close>
      and \<open>\<forall>oper \<in> set (ops @ [Move t1 p1 m1 c1]). move_child oper \<noteq> c2\<close>
  shows \<open>snd (do_ops (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2])) =
         snd (do_ops (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1]))\<close>
proof -
  have exists2: \<open>parent_exists roots (ops @ [Move t1 p1 m1 c1])\<close>
    using assms(1) parent_exists_snoc by force
  hence exists1: \<open>parent_exists roots ops\<close>
    using parent_exists_snoc by auto
  have \<open>c1 \<noteq> c2\<close>
    using assms(4) by auto
  have \<open>c1 \<noteq> p1\<close>
    using assms(3) by auto
  have \<open>c2 \<noteq> p2\<close>
    using assms(3) by auto
  have \<open>c1 \<notin> roots\<close>
    using assms(3) by auto
  have \<open>c2 \<notin> roots\<close>
    using assms(3) by auto
  have ops1: \<open>\<forall>oper \<in> set (ops @ [Move t1 p1 m1 c1]). move_child oper \<noteq> c2\<close>
    using assms(4) by auto
  hence ops2: \<open>\<forall>oper \<in> set ops. move_child oper \<noteq> c2\<close>
    by auto
  obtain log1 tree1 where tree1: \<open>do_ops ops = (log1, tree1)\<close>
    by fastforce
  obtain log2 tree2 where tree2: \<open>do_ops (ops @ [Move t1 p1 m1 c1]) = (log2, tree2)\<close>
    by fastforce
  hence tree12: \<open>tree2 = (if ancestor tree1 c1 p1 \<or> c1 = p1 then tree1
                 else {(p', m', c') \<in> tree1. c' \<noteq> c1} \<union> {(p1, m1, c1)})\<close>
    using do_ops_apply_last tree1 tree2 by (metis (mono_tags, lifting))
  obtain log3 tree3 where tree3: \<open>do_ops (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2]) = (log3, tree3)\<close>
    by fastforce
  have tree23: \<open>tree3 = {(p', m', c') \<in> tree2. c' \<noteq> c2} \<union> {(p2, m2, c2)}\<close>
  proof -
    have \<open>parent_exists roots ((ops @ [Move t1 p1 m1 c1]) @ [Move t2 p2 m2 c2])\<close>
      using assms(1) by simp
    then show ?thesis
      using do_ops_apply1 tree2 tree3 ops1 \<open>c2 \<notin> roots\<close> \<open>c2 \<noteq> p2\<close> sorry
  qed
  obtain log4 tree4 where tree4: \<open>do_ops (ops @ [Move t2 p2 m2 c2]) = (log4, tree4)\<close>
    by fastforce
  have tree14: \<open>tree4 = {(p', m', c') \<in> tree1. c' \<noteq> c2} \<union> {(p2, m2, c2)}\<close>
  proof -
    have \<open>parent_exists roots (ops @ [Move t2 p2 m2 c2])\<close>
      using assms(2) parent_exists_snoc by force
    moreover have \<open>\<forall>oper\<in>set ops. move_child oper \<noteq> c2\<close>
      using ops1 by auto
    ultimately show ?thesis
      using do_ops_apply1 tree1 tree4 \<open>c2 \<notin> roots\<close> \<open>c2 \<noteq> p2\<close> sorry
  qed
  obtain log5 tree5 where tree5: \<open>do_ops (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1]) = (log5, tree5)\<close>
    by fastforce
  have tree45: \<open>tree5 = (if ancestor tree4 c1 p1 \<or> c1 = p1 then tree4
                else {(p', m', c') \<in> tree4. c' \<noteq> c1} \<union> {(p1, m1, c1)})\<close>
  proof -
    have \<open>do_ops ((ops @ [Move t2 p2 m2 c2]) @ [Move t1 p1 m1 c1]) = (log5, tree5)\<close>
      by (simp add: tree5)
    thus ?thesis
      using do_ops_apply_last tree4 sorry
  qed
  have tree14': \<open>tree4 = tree1 \<union> {(p2, m2, c2)}\<close>
  proof -
    have \<open>c2 \<notin> {c. \<exists>p m. (p, m, c) \<in> tree1}\<close>
      using do_ops_tree_child tree1 ops2 by fastforce
    hence \<open>{(p', m', c') \<in> tree1. c' \<noteq> c2} = tree1\<close>
      by blast
    thus ?thesis
      by (simp add: tree14)
  qed
  have \<open>tree3 = tree5\<close>
  proof (cases \<open>ancestor tree1 c1 p1\<close>)
    case True
    hence \<open>tree2 = tree1\<close>
      by (simp add: tree12)
    moreover have \<open>c2 \<notin> {c. \<exists>p m. (p, m, c) \<in> tree2}\<close>
      using do_ops_tree_child tree2 ops1 by fastforce
    hence \<open>{(p', m', c') \<in> tree2. c' \<noteq> c2} = tree2\<close>
      by blast
    hence \<open>tree3 = tree2 \<union> {(p2, m2, c2)}\<close>
      by (simp add: tree23)
    moreover have \<open>ancestor tree4 c1 p1\<close>
      using True ancestor_monotone tree14' by fastforce
    hence \<open>tree5 = tree4\<close>
      by (simp add: tree45)
    ultimately show ?thesis
      using tree14' by simp
  next
    case False
    hence \<open>tree2 = {(p', m', c') \<in> tree1. c' \<noteq> c1} \<union> {(p1, m1, c1)}\<close>
      using \<open>c1 \<noteq> p1\<close> tree12 by auto
    moreover have \<open>c2 \<notin> {c. \<exists>p m. (p, m, c) \<in> tree2}\<close>
      using do_ops_tree_child tree2 ops1 by fastforce
    hence \<open>{(p', m', c') \<in> tree2. c' \<noteq> c2} = tree2\<close>
      by blast
    hence \<open>tree3 = tree2 \<union> {(p2, m2, c2)}\<close>
      by (simp add: tree23)
    moreover have \<open>\<not> ancestor tree4 c1 p1\<close>
    proof -
      have \<open>\<nexists>p' m'. (p', m', c2) \<in> tree1\<close>
        by (meson do_ops_tree_child tree1 ops2)
      moreover from this have \<open>\<nexists>m' c'. (c2, m', c') \<in> tree1\<close>
        using parent_exists_child_subset tree1 exists1 \<open>c2 \<notin> roots\<close> Un_iff by blast
      ultimately show \<open>\<not> ancestor tree4 c1 p1\<close>
        using ancestor_no_new_path False tree14' \<open>c1 \<noteq> c2\<close>
        by (metis \<open>c2 \<notin> roots\<close> exists2 parent_exists_tree tree1)
    qed
    hence \<open>tree5 = {(p', m', c') \<in> tree4. c' \<noteq> c1} \<union> {(p1, m1, c1)}\<close>
      using tree45 False \<open>c1 \<noteq> p1\<close> by simp
    moreover have \<open>c1 \<noteq> c2\<close>
      using ops1 by auto
    ultimately show \<open>tree3 = tree5\<close>
      using tree14' tree_updates_commute by auto
  qed
  thus \<open>snd (do_ops (ops @ [Move t1 p1 m1 c1, Move t2 p2 m2 c2])) =
        snd (do_ops (ops @ [Move t2 p2 m2 c2, Move t1 p1 m1 c1]))\<close>
    using tree3 tree5 by auto
qed

theorem create_commutes:
  assumes \<open>parent_exists roots (ops1 @ ops2 @ [Move t p m c])\<close>
      and \<open>parent_exists roots (ops1 @ [Move t p m c])\<close>
      and \<open>\<forall>oper \<in> set (ops1 @ ops2 @ [Move t p m c]).
           move_child oper \<notin> roots \<and> move_child oper \<noteq> move_parent oper\<close>
      and \<open>\<forall>oper \<in> set (ops1 @ ops2). move_child oper \<noteq> c\<close>
    shows \<open>snd (do_ops (ops1 @ ops2 @ [Move t p m c])) = snd (do_ops (ops1 @ [Move t p m c] @ ops2))\<close>
using assms proof (induction ops2 rule: List.rev_induct)
  case Nil
  then show \<open>snd (do_ops (ops1 @ [] @ [Move t p m c])) = snd (do_ops (ops1 @ [Move t p m c] @ []))\<close>
    by simp
next
  case (snoc oper ops)
  obtain op_t op_p op_m op_c where oper: \<open>oper = Move op_t op_p op_m op_c\<close>
    using operation.exhaust_sel by blast
  have \<open>snd (do_ops (ops1 @ (ops @ [oper]) @ [Move t p m c])) =
        snd (do_ops ((ops1 @ ops) @ [Move op_t op_p op_m op_c, Move t p m c]))\<close>
    by (simp add: oper)
  moreover have \<open>... = snd (do_ops ((ops1 @ ops) @ [Move t p m c, Move op_t op_p op_m op_c]))\<close>
  proof -
    have \<open>parent_exists roots ((ops1 @ ops) @ [Move op_t op_p op_m op_c, Move t p m c])\<close>
      using snoc.prems(1) oper by auto
    moreover from this have \<open>parent_exists roots ((ops1 @ ops) @ [Move t p m c])\<close>
      using parent_exists_interpolate snoc.prems(2) by force
    hence \<open>parent_exists roots ((ops1 @ ops) @ [Move t p m c, Move op_t op_p op_m op_c])\<close>
      by (meson calculation parent_exists_commute)
    moreover have \<open>\<forall>oper \<in> set ((ops1 @ ops) @ [Move op_t op_p op_m op_c, Move t p m c]).
         move_child oper \<notin> roots \<and> move_child oper \<noteq> move_parent oper\<close>
      by (simp add: oper snoc.prems(3))
    moreover have \<open>\<forall>oper \<in> set ((ops1 @ ops) @ [Move op_t op_p op_m op_c]). move_child oper \<noteq> c\<close>
      by (simp add: oper snoc.prems(4))
    ultimately show ?thesis
      using do_ops_commute by metis
  qed
  moreover have \<open>... = snd (do_ops (ops1 @ [Move t p m c] @ ops @ [oper]))\<close>
  proof -
    have \<open>parent_exists roots (ops1 @ ops @ [Move t p m c])\<close>
      using oper parent_exists_interpolate snoc.prems(1) snoc.prems(2) by fastforce
    hence IH: \<open>snd (do_ops (ops1 @ ops @ [Move t p m c])) = snd (do_ops (ops1 @ [Move t p m c] @ ops))\<close>
      using snoc.IH snoc.prems(2) snoc.prems(3) snoc.prems(4) by auto
    obtain tree where tree: \<open>tree = snd (do_ops (ops1 @ ops @ [Move t p m c]))\<close>
      by fastforce
    moreover have \<open>do_ops ((ops1 @ ops) @ [Move t p m c, oper]) =
                   apply_do_op (do_ops (ops1 @ ops @ [Move t p m c])) oper\<close>
      by (simp add: do_ops_def)
    hence \<open>snd (do_ops ((ops1 @ ops) @ [Move t p m c, oper])) = snd (do_op (oper, tree))\<close>
      by (metis tree apply_do_op_snd prod.exhaust_sel)
    moreover have \<open>do_ops (ops1 @ [Move t p m c] @ ops @ [oper]) =
                   apply_do_op (do_ops (ops1 @ [Move t p m c] @ ops)) oper\<close>
      by (simp add: do_ops_def)
    hence \<open>snd (do_ops (ops1 @ [Move t p m c] @ ops @ [oper])) = snd (do_op (oper, tree))\<close>
      by (metis IH apply_do_op_snd prod.exhaust_sel tree)
    ultimately show ?thesis
      using oper by blast
  qed
  ultimately show \<open>snd (do_ops (ops1 @ (ops @ [oper]) @ [Move t p m c])) =
                   snd (do_ops (ops1 @ [Move t p m c] @ ops @ [oper]))\<close>
    by blast
qed

end
