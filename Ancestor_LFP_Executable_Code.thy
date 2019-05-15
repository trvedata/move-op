theory Ancestor_LFP_Executable_Code
  imports Main "HOL-Library.While_Combinator" "HOL-Library.FSet"
begin

inductive ancestor :: \<open>('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>(p, c) \<in> S \<Longrightarrow> ancestor S p c\<close> |
  \<open>(p, c) \<in> S \<Longrightarrow> ancestor S c g \<Longrightarrow> ancestor S p g\<close>

definition ancestor' :: \<open>('a::{finite} \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>ancestor' S p c \<equiv> (p, c) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>

lemma mono_ancestor_functorI [intro!, code_unfold]:
  shows \<open>mono (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
  by(rule monoI, force)

lemma ancestor_functor_refl [intro!]:
  assumes \<open>(p, c) \<in> S\<close>
  shows \<open>(p, c) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
  using assms by(subst lfp_unfold, auto)

lemma ancestor_functor_trans [intro!]:
  assumes \<open>(p, c) \<in> S\<close> and \<open>(c, g) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
  shows \<open>(p, g) \<in> lfp (\<lambda>T. S \<union> { (p, g). \<exists>c. (p, c) \<in> S \<and> (c, g) \<in> T })\<close>
  sorry

lemma ancestor_alt_def [simp, code]:
  shows \<open>ancestor S p c \<longleftrightarrow> ancestor' S p c\<close>
proof
  assume *: \<open>ancestor' S p c\<close>
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
  from this and * show \<open>ancestor S p c\<close>
    by auto
next
  assume \<open>ancestor S p c\<close>
  from this show \<open>ancestor' S p c\<close>
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
qed

declare lfp_while_lattice [code_unfold]
declare finite_class.finite [code_unfold]

export_code ancestor' in SML module_name Ancestor

value [code] \<open>ancestor' {(CHR ''a'', CHR ''b''), (CHR ''b'', CHR ''c''), (CHR ''c'', CHR ''d'')} (CHR ''a'') (CHR ''a'')\<close>
value [code] \<open>ancestor' {(CHR ''a'', CHR ''b''), (CHR ''b'', CHR ''c''), (CHR ''c'', CHR ''d'')} (CHR ''a'') (CHR ''d'')\<close>

end