theory Ancestor_LFP_Executable_Code
  imports Main "HOL-Library.While_Combinator" "HOL-Library.Code_Target_Nat"
begin

inductive ancestor :: \<open>('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>(p, c) \<in> S \<Longrightarrow> ancestor S p c\<close> |
  \<open>(p, c) \<in> S \<Longrightarrow> ancestor S c g \<Longrightarrow> ancestor S p g\<close>

lemma ancestor_trans:
  assumes \<open>ancestor S p c\<close>
    and \<open>ancestor S c g\<close>
  shows \<open>ancestor S p g\<close>
  using assms by(induction rule: ancestor.induct) (force intro: ancestor.intros)+

definition ancestor' :: \<open>('a::{finite} \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>ancestor' S p c \<equiv> (p, c) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>

lemma mono_ancestor_functorI [intro!, code_unfold]:
  shows \<open>mono (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
  by(rule monoI, force)

lemma ancestor_alt_def1:
  assumes \<open>ancestor' S p c\<close>
  shows \<open>ancestor S p c\<close>
proof -
  have \<open>lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T }) \<subseteq> { (p, c). ancestor S p c }\<close>
  proof(rule lfp_induct)
    show \<open>mono (\<lambda>T. S \<union> {(p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T})\<close>
      by force
  next
    show \<open>S \<union> {(p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> lfp (\<lambda>T. S \<union> {(p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T}) \<inter> {(p, c). ancestor S p c}} \<subseteq> {(p, c). ancestor S p c}\<close>
      by(force intro: ancestor.intros)+
  qed
  from this have \<open>{ (p, c). ancestor' S p c } \<subseteq> { (p, c). ancestor S p c }\<close>
    by(auto simp add: ancestor'_def)
  from this and assms show \<open>ancestor S p c\<close>
    by auto
qed

lemma ancestor_functor_refl [intro!]:
  assumes \<open>(p, c) \<in> S\<close>
  shows \<open>(p, c) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
  using assms by(subst lfp_unfold, auto)

lemma ancestor_functor_trans [intro!]:
  fixes p :: \<open>'a::{finite}\<close>
  assumes \<open>(p, c) \<in> S\<close> and \<open>(c, g) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
  shows \<open>(p, g) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
proof -
  have \<open>S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T }) } =
          lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
    by(rule lfp_unfold[OF mono_ancestor_functorI, symmetric])
  also have \<open>(p, g) \<in> S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T }) }\<close>
    using assms by clarsimp
  ultimately show \<open>?thesis\<close>
    by auto
qed

lemma ancestor_alt_def2:
  assumes \<open>ancestor S p c\<close>
  shows \<open>ancestor' S p c\<close>
  using assms
proof(induction rule: ancestor.induct)
  fix p c and S :: \<open>('a \<times> 'a) set\<close>
  assume \<open>(p, c) \<in> S\<close>
  from this show \<open>ancestor' S p c\<close>
    by(force simp add: ancestor'_def)
next
  fix p c g and S :: \<open>('a \<times> 'a) set\<close>
  assume *: \<open>(p, c) \<in> S\<close> and \<open>ancestor' S c g\<close>
  from this also have **: \<open>(c, g) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
    by(clarsimp simp add: ancestor'_def)
  ultimately show \<open>ancestor' S p g\<close>
    by(clarsimp simp add: ancestor'_def intro!: ancestor_functor_trans[OF * **])
qed

lemma ancestor_alt_def [simp, code]:
  shows \<open>ancestor S p c \<longleftrightarrow> ancestor' S p c\<close>
  using ancestor_alt_def1 ancestor_alt_def2 by force

declare lfp_while_lattice [code_unfold]
declare finite_class.finite [code_unfold]

section\<open>Efficiency improvements\<close>

lemma ancestor_unwind [code]:
  shows \<open>ancestor Ss p c \<longleftrightarrow> ((p, c) \<in> Ss \<or> (\<exists>(x, y)\<in>Ss. p = x \<and> ancestor Ss y c))\<close>
  apply(rule iffI)
  apply(induction rule: ancestor.induct)
  apply force+
  apply(erule disjE)
  apply(force intro!: ancestor.intros)
  apply(clarsimp simp add: ancestor.intros)
  done

export_code ancestor in SML module_name Ancestor file ancestor.ML

record example_node =
  name :: \<open>String.literal\<close>
  age  :: \<open>nat\<close>

value \<open>
  let db = {(\<lparr>name = String.implode ''Alan'', age = 34\<rparr>, \<lparr>name = String.implode ''Bill'', age = 18\<rparr>),
              (\<lparr>name = String.implode ''Bill'', age = 18\<rparr>, \<lparr>name = String.implode ''Charles'', age = 1\<rparr>),
              (\<lparr>name = String.implode ''Alan'', age = 34\<rparr>, \<lparr>name = String.implode ''Diane'', age = 17\<rparr>),
              (\<lparr>name = String.implode ''Diane'', age = 17\<rparr>, \<lparr>name = String.implode ''Elizabeth'', age = 0\<rparr>)};
      pr = \<lparr>name = String.implode ''Alan'', age = 34\<rparr>;
      cd = \<lparr>name = String.implode ''Elizabeth'', age = 0\<rparr>
   in ancestor db pr cd\<close>

definition support :: \<open>('a \<times> 'a) set \<Rightarrow> 'a set\<close>
  where \<open>support Ss \<equiv> \<Union>(x, y) \<in> Ss. {x, y}\<close>

definition has_descendent :: \<open>('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>has_descendent Ss p \<equiv> \<exists>s\<in>support Ss. ancestor Ss p s\<close>

definition has_ancestor :: \<open>('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>has_ancestor Ss c \<equiv> \<exists>a\<in>support Ss. ancestor Ss a c\<close>

definition have_common_ancestor :: \<open>('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>have_common_ancestor Ss c1 c2 \<equiv> \<exists>a\<in>support Ss. ancestor Ss a c1 \<and> ancestor Ss a c2\<close>

value \<open>
  let db = {(\<lparr>name = String.implode ''Alan'', age = 34\<rparr>, \<lparr>name = String.implode ''Bill'', age = 18\<rparr>),
              (\<lparr>name = String.implode ''Bill'', age = 18\<rparr>, \<lparr>name = String.implode ''Charles'', age = 1\<rparr>),
              (\<lparr>name = String.implode ''Alan'', age = 34\<rparr>, \<lparr>name = String.implode ''Diane'', age = 17\<rparr>),
              (\<lparr>name = String.implode ''Diane'', age = 17\<rparr>, \<lparr>name = String.implode ''Elizabeth'', age = 0\<rparr>)};
      pr = \<lparr>name = String.implode ''Diane'', age = 17\<rparr>;
      cd = \<lparr>name = String.implode ''Elizabeth'', age = 0\<rparr>
   in have_common_ancestor db \<lparr>name = String.implode ''Bill'', age = 18\<rparr> \<lparr>name = String.implode ''Diane'', age = 17\<rparr>\<close>

export_code has_ancestor has_descendent ancestor in SML

end