theory
  Move_Code
imports
  Move "HOL-Library.Code_Target_Numeral" "Collections.Collections" "Collections.ICF_Userguide"
    "HOL-Library.Product_Lexorder"
begin

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
  efficient_apply_op efficient_apply_ops in SML file generated.SML
export_code efficient_ancestor efficient_do_op efficient_undo_op efficient_redo_op
  efficient_apply_op efficient_apply_ops in Scala file generated.scala
export_code efficient_ancestor efficient_do_op efficient_undo_op efficient_redo_op
  efficient_apply_op efficient_apply_ops in OCaml file generated.ml
export_code efficient_ancestor efficient_do_op efficient_undo_op efficient_redo_op
  efficient_apply_op efficient_apply_ops in Haskell

definition example_apply_op ::
    \<open>((int \<times> String.literal), String.literal, String.literal) operation \<Rightarrow>
     ((int \<times> String.literal), String.literal, String.literal) log_op list \<times>
       (String.literal, String.literal \<times> String.literal) HashMap.hashmap \<Rightarrow>
     ((int \<times> String.literal), String.literal, String.literal) log_op list \<times>
       (String.literal, String.literal \<times> String.literal) HashMap.hashmap\<close>
 where \<open>example_apply_op = efficient_apply_op\<close>

export_code example_apply_op in Scala module_name generated file \<open>evaluation/src/main/scala/Move_Code.scala\<close>

text\<open>Without resorting to saving the generated code above to a separate file and feeding them into
     an SML/Scala/OCaml/Haskell compiler, as appropriate, we can show that this code compiles and
     executes relatively quickly from within Isabelle itself, by making use of Isabelle's
     quotations/anti-quotations, and its tight coupling with the underlying PolyML process.

     First define a @{term unit_test} definition that makes use of our @{term efficient_apply_ops}
     function on a variety of inputs:\<close>

definition unit_test :: \<open>((nat, nat, nat) log_op list \<times> (nat, nat \<times> nat) HashMap.hashmap) list\<close>
  where \<open>unit_test \<equiv>
          [ efficient_apply_ops []
          , efficient_apply_ops [Move 1 0 0 1]
          , efficient_apply_ops [Move 1 0 0 0, Move 3 2 2 2, Move 2 1 1 1]
          ]\<close>

text\<open>Then, we can use @{command ML_val} to ask Isabelle to:
      \<^enum> Generate executable code for our @{term unit_test} definition above, using the SML code
        generation target,
      \<^enum> Execute this code within the underlying Isabelle/ML process, and display the resulting SML
        values back to us within the Isabelle/JEdit IDE.\<close>

ML_val\<open>@{code unit_test}\<close>
value unit_test
text\<open>Note, there is a slight lag when performing this action as the executable code is first
     extracted to SML, dynamically compiled, and then the result of the computation reflected back
     to us.  Nevertheless, on a Macbook Pro (2017 edition) this procedure takes 2 seconds, at the
     most.\<close>
end