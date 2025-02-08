# section \<open>The ZF Axioms, Ordinals and Transfinite Recursion\<close>

# theory ZFC_in_HOL
#   imports ZFC_Library

# begin

# subsection\<open>Syntax and axioms\<close>

# hide_const (open) list.set Sum subset

# unbundle lattice_syntax
# %%

from kdrag.all import *

# typedecl V

V = smt.DeclareSort("V")

import kdrag.theories.set as set_

x, y, z = smt.Consts("x y z", V)
X, Y, Z = smt.Consts("X Y Z", set_.Set(V))
# text\<open>Presentation refined by Dmitriy Traytel\<close>
# axiomatization elts :: "V \<Rightarrow> V set"
#  where ext [intro?]:    "elts x = elts y \<Longrightarrow> x=y"
#    and down_raw:        "Y \<subseteq> elts x \<Longrightarrow> Y \<in> range elts"
#    and Union_raw:       "X \<in> range elts \<Longrightarrow> Union (elts ` X) \<in> range elts"
#    and Pow_raw:         "X \<in> range elts \<Longrightarrow> inv elts ` Pow X \<in> range elts"
#    and replacement_raw: "X \<in> range elts \<Longrightarrow> f ` X \<in> range elts"
#    and inf_raw:         "range (g :: nat \<Rightarrow> V) \<in> range elts"
#    and foundation:      "wf {(x,y). x \<in> elts y}"

elts = smt.Function("elts", V, set_.Set(V))
ext = kd.axiom(kd.QForAll([x, y], elts(x) == elts(y), x == y))
down_raw = kd.axiom(kd.QForAll([Y, x], Y <= elts(x), set_.member(Y, set_.Range(elts))))
# Union_raw = kd.axiom(kd.QForAll([X], set_.member(X, set_.Range(elts)), set_.member(set_.Union(set_.image(elts, X)), set_.Range(elts)))
# %%

# lemma mem_not_refl [simp]: "i \<notin> elts i"
#   using wf_not_refl [OF foundation] by force

# lemma mem_not_sym: "\<not> (x \<in> elts y \<and> y \<in> elts x)"
#   using wf_not_sym [OF foundation] by force

# text \<open>A set is small if it can be injected into the extension of a V-set.\<close>
# definition small :: "'a set \<Rightarrow> bool"
#   where "small X \<equiv> \<exists>V_of :: 'a \<Rightarrow> V. inj_on V_of X \<and> V_of ` X \<in> range elts"

# lemma small_empty [iff]: "small {}"
#   by (simp add: small_def down_raw)

# lemma small_iff_range: "small X \<longleftrightarrow> X \<in> range elts"
#   apply (simp add: small_def)
#   by (metis inj_on_id2 replacement_raw the_inv_into_onto)

# lemma small_eqpoll: "small A \<longleftrightarrow> (\<exists>x. elts x \<approx> A)"
#   unfolding small_def by (metis UNIV_I bij_betw_def eqpoll_def eqpoll_sym imageE image_eqI)

# text\<open>Small classes can be mapped to sets.\<close>
# definition set :: "V set \<Rightarrow> V"
#   where "set X \<equiv> (if small X then inv elts X else inv elts {})"

# lemma set_of_elts [simp]: "set (elts x) = x"
#   by (force simp add: ext set_def f_inv_into_f small_def)

# lemma elts_of_set [simp]: "elts (set X) = (if small X then X else {})"
#   by (simp add: ZFC_in_HOL.set_def down_raw f_inv_into_f small_iff_range)

# lemma down: "Y \<subseteq> elts x \<Longrightarrow> small Y"
#   by (simp add: down_raw small_iff_range)

# lemma Union [intro]: "small X \<Longrightarrow> small (Union (elts ` X))"
#   by (simp add: Union_raw small_iff_range)

# lemma Pow: "small X \<Longrightarrow> small (set ` Pow X)"
#   unfolding small_iff_range using Pow_raw set_def down by force

# declare replacement_raw [intro,simp]

# lemma replacement [intro,simp]:
#   assumes "small X"
#   shows "small (f ` X)"
# proof -
#   let ?A = "inv_into X f ` (f ` X)"
#   have AX: "?A \<subseteq> X"
#     by (simp add: image_subsetI inv_into_into)
#   have inj: "inj_on f ?A"
#     by (simp add: f_inv_into_f inj_on_def)
#   have injo: "inj_on (inv_into X f) (f ` X)"
#     using inj_on_inv_into by blast
#   have "\<exists>V_of. inj_on V_of (f ` X) \<and> V_of ` f ` X \<in> range elts"
#     if "inj_on V_of X" and "V_of ` X = elts x"
#     for V_of :: "'a \<Rightarrow> V" and x
#   proof (intro exI conjI)
#     show "inj_on (V_of \<circ> inv_into X f) (f ` X)"
#       by (meson \<open>inv_into X f ` f ` X \<subseteq> X\<close> comp_inj_on inj_on_subset injo that)
#     have "(\<lambda>x. V_of (inv_into X f (f x))) ` X = elts (set (V_of ` ?A))"
#       by (metis AX down elts_of_set image_image image_mono that(2))
#     then show "(V_of \<circ> inv_into X f) ` f ` X \<in> range elts"
#       by (metis image_comp image_image rangeI)
#   qed
#   then show ?thesis
#     using assms by (auto simp: small_def)
# qed

# lemma small_image_iff [simp]: "inj_on f A \<Longrightarrow> small (f ` A) \<longleftrightarrow> small A"
#   by (metis replacement the_inv_into_onto)

# text \<open>A little bootstrapping is needed to characterise @{term small} for sets of arbitrary type.\<close>

# lemma inf: "small (range (g :: nat \<Rightarrow> V))"
#   by (simp add: inf_raw small_iff_range)

# lemma small_image_nat_V [simp]: "small (g ` N)" for g :: "nat \<Rightarrow> V"
#   by (metis (mono_tags, opaque_lifting) down elts_of_set image_iff inf rangeI subsetI)

# lemma Finite_V:
#   fixes X :: "V set"
#   assumes "finite X" shows "small X"
#   using ex_bij_betw_nat_finite [OF assms] unfolding bij_betw_def by (metis small_image_nat_V)

# lemma small_insert_V:
#   fixes X :: "V set"
#   assumes "small X"
#   shows "small (insert a X)"
# proof (cases "finite X")
#   case True
#   then show ?thesis
#     by (simp add: Finite_V)
# next
#   case False
#   show ?thesis
#     using infinite_imp_bij_betw2 [OF False]
#     by (metis replacement Un_insert_right assms bij_betw_imp_surj_on sup_bot.right_neutral)
# qed

# lemma small_UN_V [simp,intro]:
#   fixes B :: "'a \<Rightarrow> V set"
#   assumes X: "small X" and B: "\<And>x. x \<in> X \<Longrightarrow> small (B x)"
#   shows "small (\<Union>x\<in>X. B x)"
# proof -
#   have "(\<Union> (elts ` (\<lambda>x. ZFC_in_HOL.set (B x)) ` X)) = (\<Union> (B ` X))"
#     using B by force
#   then show ?thesis
#     using Union [OF replacement [OF X, of "\<lambda>x. ZFC_in_HOL.set (B x)"]] by simp
# qed

# definition vinsert where "vinsert x y \<equiv> set (insert x (elts y))"

# lemma elts_vinsert [simp]: "elts (vinsert x y) = insert x (elts y)"
#   using down small_insert_V vinsert_def by auto

# definition succ where "succ x \<equiv> vinsert x x"

# lemma elts_succ [simp]: "elts (succ x) = insert x (elts x)"
#   by (simp add: succ_def)

# lemma finite_imp_small:
#   assumes "finite X" shows "small X"
#   using assms
# proof induction
#   case empty
#   then show ?case
#     by simp
# next
#   case (insert a X)
#   then obtain V_of u where u: "inj_on V_of X" "V_of ` X = elts u"
#     by (meson small_def image_iff)
#   show ?case
#     unfolding small_def
#   proof (intro exI conjI)
#     show "inj_on (V_of(a:=u)) (insert a X)"
#       using u
#       apply (clarsimp simp add: inj_on_def)
#       by (metis image_eqI mem_not_refl)
#     have "(V_of(a:=u)) ` insert a X = elts (vinsert u u)"
#       using insert.hyps(2) u(2) by auto
#     then show "(V_of(a:=u)) ` insert a X \<in> range elts"
#       by (blast intro:  elim: )
#   qed
# qed

# lemma small_insert:
#   assumes "small X"
#   shows "small (insert a X)"
# proof (cases "finite X")
#   case True
#   then show ?thesis
#     by (simp add: finite_imp_small)
# next
#   case False
#   show ?thesis
#     using infinite_imp_bij_betw2 [OF False]
#     by (metis replacement Un_insert_right assms bij_betw_imp_surj_on sup_bot.right_neutral)
# qed

# lemma smaller_than_small:
#   assumes "small A" "B \<subseteq> A" shows "small B"
#   using assms
#   by (metis down elts_of_set image_mono small_def small_iff_range subset_inj_on)

# lemma small_insert_iff [iff]: "small (insert a X) \<longleftrightarrow> small X"
#   by (meson small_insert smaller_than_small subset_insertI)

# lemma small_iff: "small X \<longleftrightarrow> (\<exists>x. X = elts x)"
#   by (metis down elts_of_set subset_refl)

# lemma small_elts [iff]: "small (elts x)"
#   by (auto simp: small_iff)

# lemma small_diff [iff]: "small (elts a - X)"
#   by (meson Diff_subset down)

# lemma small_set [simp]: "small (list.set xs)"
#   by (simp add: ZFC_in_HOL.finite_imp_small)

# lemma small_upair: "small {x,y}"
#   by simp

# lemma small_Un_elts: "small (elts x \<union> elts y)"
#   using Union [OF small_upair] by auto

# lemma small_eqcong: "\<lbrakk>small X; X \<approx> Y\<rbrakk> \<Longrightarrow> small Y"
#   by (metis bij_betw_imp_surj_on eqpoll_def replacement)

# lemma lepoll_small: "\<lbrakk>small Y; X \<lesssim> Y\<rbrakk> \<Longrightarrow> small X"
#     by (meson lepoll_iff replacement smaller_than_small)

# lemma big_UNIV [simp]: "\<not> small (UNIV::V set)" (is  "\<not> small ?U")
#   proof
#     assume "small ?U"
#     then have "small A" for A :: "V set"
#       by (metis (full_types) UNIV_I down small_iff subsetI)
#     then have "range elts = UNIV"
#       by (meson small_iff surj_def)
#   then show False
#     by (metis Cantors_theorem Pow_UNIV)
# qed

# lemma inj_on_set: "inj_on set (Collect small)"
#   by (metis elts_of_set inj_onI mem_Collect_eq)

# lemma set_injective [simp]: "\<lbrakk>small X; small Y\<rbrakk> \<Longrightarrow> set X = set Y \<longleftrightarrow> X=Y"
#   by (metis elts_of_set)


# subsection\<open>Type classes and other basic setup\<close>

# instantiation V :: zero
# begin
# definition zero_V where "0 \<equiv> set {}"
# instance ..
# end

# lemma elts_0 [simp]: "elts 0 = {}"
#   by (simp add: zero_V_def)

# lemma set_empty [simp]: "set {} = 0"
#   by (simp add: zero_V_def)

# instantiation V :: one
# begin
# definition one_V where "1 \<equiv> succ 0"
# instance ..
# end

# lemma elts_1 [simp]: "elts 1 = {0}"
#   by (simp add: one_V_def)

# lemma insert_neq_0 [simp]: "set (insert a X) = 0 \<longleftrightarrow> \<not> small X"
#   unfolding zero_V_def
#   by (metis elts_of_set empty_not_insert set_of_elts small_insert_iff)

# lemma elts_eq_empty_iff [simp]: "elts x = {} \<longleftrightarrow> x=0"
#   by (auto simp: ZFC_in_HOL.ext)

# instantiation V :: distrib_lattice
# begin

# definition inf_V where "inf_V x y \<equiv> set (elts x \<inter> elts y)"

# definition sup_V where "sup_V x y \<equiv> set (elts x \<union> elts y)"

# definition less_eq_V where "less_eq_V x y \<equiv> elts x \<subseteq> elts y"

# definition less_V where "less_V x y \<equiv> less_eq x y \<and> x \<noteq> (y::V)"

# instance
# proof
#   show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" for x :: V and y :: V
#     using ext less_V_def less_eq_V_def by auto
#   show "x \<le> x" for x :: V
#     by (simp add: less_eq_V_def)
#   show "x \<le> z" if "x \<le> y" "y \<le> z" for x y z :: V
#     using that by (auto simp: less_eq_V_def)
#   show "x = y" if "x \<le> y" "y \<le> x" for x y :: V
#     using that by (simp add: ext less_eq_V_def)
#   show "inf x y \<le> x" for x y :: V
#     by (metis down elts_of_set inf_V_def inf_sup_ord(1) less_eq_V_def)
#   show "inf x y \<le> y" for x y :: V
#     by (metis Int_lower2 down elts_of_set inf_V_def less_eq_V_def)
#   show "x \<le> inf y z" if "x \<le> y" "x \<le> z" for x y z :: V
#   proof -
#     have "small (elts y \<inter> elts z)"
#       by (meson down inf.cobounded1)
#     then show ?thesis
#       using elts_of_set inf_V_def less_eq_V_def that by auto
#   qed
#   show "x \<le> x \<squnion> y" "y \<le> x \<squnion> y" for x y :: V
#     by (simp_all add: less_eq_V_def small_Un_elts sup_V_def)
#   show "sup y z \<le> x" if "y \<le> x" "z \<le> x" for x y z :: V
#     using less_eq_V_def sup_V_def that by auto
#   show "sup x (inf y z) = inf (x \<squnion> y) (sup x z)" for x y z :: V
#   proof -
#     have "small (elts y \<inter> elts z)"
#       by (meson down inf.cobounded2)
#     then show ?thesis
#       by (simp add: Un_Int_distrib inf_V_def small_Un_elts sup_V_def)
#   qed
# qed
# end

# lemma V_equalityI [intro]: "(\<And>x. x \<in> elts a \<longleftrightarrow> x \<in> elts b) \<Longrightarrow> a = b"
#   by (meson dual_order.antisym less_eq_V_def subsetI)

# lemma vsubsetI [intro!]: "(\<And>x. x \<in> elts a \<Longrightarrow> x \<in> elts b) \<Longrightarrow> a \<le> b"
#   by (simp add: less_eq_V_def subsetI)

# lemma vsubsetD [elim, intro?]: "a \<le> b \<Longrightarrow> c \<in> elts a \<Longrightarrow> c \<in> elts b"
#   using less_eq_V_def by auto

# lemma rev_vsubsetD: "c \<in> elts a \<Longrightarrow> a \<le> b \<Longrightarrow> c \<in> elts b"
#   \<comment> \<open>The same, with reversed premises for use with @{method erule} -- cf. @{thm rev_mp}.\<close>
#   by (rule vsubsetD)

# lemma vsubsetCE [elim,no_atp]: "a \<le> b \<Longrightarrow> (c \<notin> elts a \<Longrightarrow> P) \<Longrightarrow> (c \<in> elts b \<Longrightarrow> P) \<Longrightarrow> P"
#   \<comment> \<open>Classical elimination rule.\<close>
#   using vsubsetD by blast

# lemma set_image_le_iff: "small A \<Longrightarrow> set (f ` A) \<le> B \<longleftrightarrow> (\<forall>x\<in>A. f x \<in> elts B)"
#   by auto

# lemma eq0_iff: "x = 0 \<longleftrightarrow> (\<forall>y. y \<notin> elts x)"
#   by auto

# lemma less_eq_V_0_iff [simp]: "x \<le> 0 \<longleftrightarrow> x = 0" for x::V
#   by auto

# lemma subset_iff_less_eq_V:
#   assumes "small B" shows "A \<subseteq> B \<longleftrightarrow> set A \<le> set B \<and> small A"
#   using assms down small_iff by auto

# lemma small_Collect [simp]: "small A \<Longrightarrow> small {x \<in> A. P x}"
#   by (simp add: smaller_than_small)

# lemma small_Union_iff: "small (\<Union>(elts ` X)) \<longleftrightarrow> small X"
#   proof
#   show "small X"
#     if "small (\<Union> (elts ` X))"
#   proof -
#     have "X \<subseteq> set ` Pow (\<Union> (elts ` X))"
#       by fastforce
#     then show ?thesis
#       using Pow subset_iff_less_eq_V that by auto
#   qed
# qed auto

# lemma not_less_0 [iff]:
#   fixes x::V shows "\<not> x < 0"
#   by (simp add: less_eq_V_def less_le_not_le)

# lemma le_0 [iff]:
#   fixes x::V shows "0 \<le> x"
#   by auto

# lemma min_0L [simp]: "min 0 n = 0" for n :: V
#   by (simp add: min_absorb1)

# lemma min_0R [simp]: "min n 0 = 0" for n :: V
#   by (simp add: min_absorb2)

# lemma neq0_conv: "\<And>n::V. n \<noteq> 0 \<longleftrightarrow> 0 < n"
#   by (simp add: less_V_def)


# definition VPow :: "V \<Rightarrow> V"
#   where "VPow x \<equiv> set (set ` Pow (elts x))"

# lemma VPow_iff [iff]: "y \<in> elts (VPow x) \<longleftrightarrow> y \<le> x"
#   using down Pow
#   apply (auto simp: VPow_def less_eq_V_def)
#   using less_eq_V_def apply fastforce
#   done

# lemma VPow_le_VPow_iff [simp]: "VPow a \<le> VPow b \<longleftrightarrow> a \<le> b"
#   by auto

# lemma elts_VPow: "elts (VPow x) = set ` Pow (elts x)"
#   by (auto simp: VPow_def Pow)

# lemma small_sup_iff [simp]: "small (X \<union> Y) \<longleftrightarrow> small X \<and> small Y" for X::"V set"
#   by (metis down elts_of_set small_Un_elts sup_ge1 sup_ge2)

# lemma elts_sup_iff [simp]: "elts (x \<squnion> y) = elts x \<union> elts y"
#   by (simp add: sup_V_def)

# lemma trad_foundation:
#   assumes z: "z \<noteq> 0" shows "\<exists>w. w \<in> elts z \<and> w \<sqinter> z = 0"
#   using foundation assms
#   by (simp add: wf_eq_minimal) (metis Int_emptyI equals0I inf_V_def set_of_elts zero_V_def)


# instantiation "V" :: Sup
# begin
# definition Sup_V where "Sup_V X \<equiv> if small X then set (Union (elts ` X)) else 0"
# instance ..
# end

# instantiation "V" :: Inf
# begin
# definition Inf_V where "Inf_V X \<equiv> if X = {} then 0 else set (Inter (elts ` X))"
# instance ..
# end

# lemma V_disjoint_iff: "x \<sqinter> y = 0 \<longleftrightarrow> elts x \<inter> elts y = {}"
#   by (metis down elts_of_set inf_V_def inf_le1 zero_V_def)

# text\<open>I've no idea why @{term bdd_above} is treated differently from @{term bdd_below}, but anyway\<close>
# lemma bdd_above_iff_small [simp]: "bdd_above X = small X" for X::"V set"
# proof
#   show "small X" if "bdd_above X"
#   proof -
#     obtain a where "\<forall>x\<in>X. x \<le> a"
#       using that \<open>bdd_above X\<close> bdd_above_def by blast
#     then show "small X"
#       by (meson VPow_iff \<open>\<forall>x\<in>X. x \<le> a\<close> down subsetI)
#   qed
#   show "bdd_above X"
#     if "small X"
#   proof -
#     have "\<forall>x\<in>X. x \<le> \<Squnion> X"
#       by (simp add: SUP_upper Sup_V_def Union less_eq_V_def that)
#     then show ?thesis
#       by (meson bdd_above_def)
#   qed
# qed


# instantiation "V" :: conditionally_complete_lattice
# begin

# definition bdd_below_V where "bdd_below_V X \<equiv> X \<noteq> {}"

# instance
#   proof
#   show "\<Sqinter> X \<le> x" if "x \<in> X" "bdd_below X"
#     for x :: V and X :: "V set"
#     using that by (auto simp: bdd_below_V_def Inf_V_def split: if_split_asm)
#   show "z \<le> \<Sqinter> X"
#     if "X \<noteq> {}" "\<And>x. x \<in> X \<Longrightarrow> z \<le> x"
#     for X :: "V set" and z :: V
#     using that
#     apply (clarsimp simp add: bdd_below_V_def Inf_V_def less_eq_V_def split: if_split_asm)
#     by (meson INT_subset_iff down eq_refl equals0I)
#   show "x \<le> \<Squnion> X" if "x \<in> X" and "bdd_above X" for x :: V and X :: "V set"
#     using that Sup_V_def by auto
#   show "\<Squnion> X \<le> (z::V)" if "X \<noteq> {}" "\<And>x. x \<in> X \<Longrightarrow> x \<le> z" for X :: "V set" and z :: V
#     using that  by (simp add: SUP_least Sup_V_def less_eq_V_def)
# qed
# end

# lemma Sup_upper: "\<lbrakk>x \<in> A; small A\<rbrakk> \<Longrightarrow> x \<le> \<Squnion>A" for A::"V set"
#   by (auto simp: Sup_V_def SUP_upper Union less_eq_V_def)

# lemma Sup_least:
#   fixes z::V shows "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>A \<le> z"
#   by (auto simp: Sup_V_def SUP_least less_eq_V_def)

# lemma Sup_empty [simp]: "\<Squnion>{} = (0::V)"
#   using Sup_V_def by auto

# lemma elts_Sup [simp]: "small X \<Longrightarrow> elts (\<Squnion> X) = \<Union>(elts ` X)"
#   by (auto simp: Sup_V_def)

# lemma sup_V_0_left [simp]: "0 \<squnion> a = a" and sup_V_0_right [simp]: "a \<squnion> 0 = a" for a::V
#   by auto

# lemma Sup_V_insert:
#   fixes x::V assumes "small A" shows "\<Squnion>(insert x A) = x \<squnion> \<Squnion>A"
#   by (simp add: assms cSup_insert_If)

# lemma Sup_Un_distrib: "\<lbrakk>small A; small B\<rbrakk> \<Longrightarrow> \<Squnion>(A \<union> B) = \<Squnion>A \<squnion> \<Squnion>B" for A::"V set"
#   by auto

# lemma SUP_sup_distrib:
#   fixes f :: "V \<Rightarrow> V"
#   shows "small A \<Longrightarrow> (\<Squnion>x\<in>A. f x \<squnion> g x) = \<Squnion> (f ` A) \<squnion> \<Squnion> (g ` A)"
#   by (force simp:)

# lemma SUP_const [simp]: "(\<Squnion>y \<in> A. a) = (if A = {} then (0::V) else a)"
#   by simp

# lemma cSUP_subset_mono:
#   fixes f :: "'a \<Rightarrow> V set" and g :: "'a \<Rightarrow> V set"
#   shows "\<lbrakk>A \<subseteq> B; \<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<rbrakk> \<Longrightarrow> \<Squnion> (f ` A) \<le> \<Squnion> (g ` B)"
#   by (simp add: SUP_subset_mono)

# lemma mem_Sup_iff [iff]: "x \<in> elts (\<Squnion>X) \<longleftrightarrow> x \<in> \<Union> (elts ` X) \<and> small X"
#   using Sup_V_def by auto

# lemma cSUP_UNION:
#   fixes B :: "V \<Rightarrow> V set" and f :: "V \<Rightarrow> V"
#   assumes ne: "small A" and bdd_UN: "small (\<Union>x\<in>A. f ` B x)"
#   shows "\<Squnion>(f ` (\<Union>x\<in>A. B x)) = \<Squnion>((\<lambda>x. \<Squnion>(f ` B x)) ` A)"
# proof -
#   have bdd: "\<And>x. x \<in> A \<Longrightarrow> small (f ` B x)"
#     using bdd_UN subset_iff_less_eq_V
#     by (meson SUP_upper smaller_than_small)
#   then have bdd2: "small ((\<lambda>x. \<Squnion>(f ` B x)) ` A)"
#     using ne(1) by blast
#   have "\<Squnion>(f ` (\<Union>x\<in>A. B x)) \<le> \<Squnion>((\<lambda>x. \<Squnion>(f ` B x)) ` A)"
#     using assms by (fastforce simp add: intro!: cSUP_least intro: cSUP_upper2 simp: bdd2 bdd)
#   moreover have "\<Squnion>((\<lambda>x. \<Squnion>(f ` B x)) ` A) \<le> \<Squnion>(f ` (\<Union>x\<in>A. B x))"
#     using assms by (fastforce simp add: intro!: cSUP_least intro: cSUP_upper simp: image_UN bdd_UN)
#   ultimately show ?thesis
#     by (rule order_antisym)
# qed

# lemma Sup_subset_mono: "small B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A \<le> Sup B" for A::"V set"
#   by auto

# lemma Sup_le_iff: "small A \<Longrightarrow> Sup A \<le> a \<longleftrightarrow> (\<forall>x\<in>A. x \<le> a)" for A::"V set"
#   by auto

# lemma SUP_le_iff: "small (f ` A) \<Longrightarrow> \<Squnion>(f ` A) \<le> u \<longleftrightarrow> (\<forall>x\<in>A. f x \<le> u)" for f :: "V \<Rightarrow> V"
#   by blast

# lemma Sup_eq_0_iff [simp]: "\<Squnion>A = 0 \<longleftrightarrow> A \<subseteq> {0} \<or> \<not> small A" for A :: "V set"
#   using Sup_upper by fastforce

# lemma Sup_Union_commute:
#   fixes f :: "V \<Rightarrow> V set"
#   assumes "small A" "\<And>x. x\<in>A \<Longrightarrow> small (f x)"
#   shows "\<Squnion> (\<Union>x\<in>A. f x) = (\<Squnion>x\<in>A. \<Squnion> (f x))"
#   using assms
#   by (force simp: subset_iff_less_eq_V intro!: antisym)

# lemma Sup_eq_Sup:
#   fixes B :: "V set"
#   assumes "B \<subseteq> A" "small A" and *: "\<And>x. x \<in> A \<Longrightarrow> \<exists>y \<in> B. x \<le> y"
#   shows "Sup A = Sup B"
# proof -
#   have "small B"
#     using assms subset_iff_less_eq_V by auto
#   moreover have "\<exists>y\<in>B. u \<in> elts y"
#     if "x \<in> A" "u \<in> elts x" for u x
#     using that "*" by blast
#   moreover have "\<exists>x\<in>A. v \<in> elts x"
#     if "y \<in> B" "v \<in> elts y" for v y
#     using that \<open>B \<subseteq> A\<close> by blast
#   ultimately show ?thesis
#     using assms by auto
# qed

# subsection\<open>Successor function\<close>

# lemma vinsert_not_empty [simp]: "vinsert a A \<noteq> 0"
#   and empty_not_vinsert [simp]: "0 \<noteq> vinsert a A"
#   by (auto simp: vinsert_def)

# lemma succ_not_0 [simp]: "succ n \<noteq> 0" and zero_not_succ [simp]: "0 \<noteq> succ n"
#   by (auto simp: succ_def)

# instantiation V :: zero_neq_one
# begin
# instance
#   by intro_classes (metis elts_0 elts_succ empty_iff insert_iff one_V_def set_of_elts)
# end

# instantiation V :: zero_less_one
# begin
# instance
#   by intro_classes (simp add: less_V_def)
# end

# lemma succ_ne_self [simp]: "i \<noteq> succ i"
#   by (metis elts_succ insertI1 mem_not_refl)

# lemma succ_notin_self: "succ i \<notin> elts i"
#   using elts_succ mem_not_refl by blast

# lemma le_succE: "succ i \<le> succ j \<Longrightarrow> i \<le> j"
#   using less_eq_V_def mem_not_sym by auto

# lemma succ_inject_iff [iff]: "succ i = succ j \<longleftrightarrow> i = j"
#   by (simp add: dual_order.antisym le_succE)

# lemma inj_succ: "inj succ"
#   by (simp add: inj_def)

# lemma succ_neq_zero: "succ x \<noteq> 0"
#   by (metis elts_0 elts_succ insert_not_empty)

# definition pred where "pred i \<equiv> THE j. i = succ j"

# lemma pred_succ [simp]: "pred (succ i) = i"
#   by (simp add: pred_def)


# subsection \<open>Ordinals\<close>

# definition Transset where "Transset x \<equiv> \<forall>y \<in> elts x. y \<le> x"

# definition Ord where "Ord x \<equiv> Transset x \<and> (\<forall>y \<in> elts x. Transset y)"

# abbreviation ON where "ON \<equiv> Collect Ord"

# subsubsection \<open>Transitive sets\<close>

# lemma Transset_0 [iff]: "Transset 0"
#   by (auto simp: Transset_def)

# lemma Transset_succ [intro]:
#   assumes "Transset x" shows "Transset (succ x)"
#   using assms
#   by (auto simp: Transset_def succ_def less_eq_V_def)

# lemma Transset_Sup:
#   assumes "\<And>x. x \<in> X \<Longrightarrow> Transset x" shows "Transset (\<Squnion>X)"
# proof (cases "small X")
#   case True
#   with assms show ?thesis
#     by (simp add: Transset_def) (meson Sup_upper assms dual_order.trans)
# qed (simp add: Sup_V_def)

# lemma Transset_sup:
#   assumes "Transset x" "Transset y" shows "Transset (x \<squnion> y)"
#   using Transset_def assms by fastforce

# lemma Transset_inf: "\<lbrakk>Transset i; Transset j\<rbrakk> \<Longrightarrow> Transset (i \<sqinter> j)"
#   by (simp add: Transset_def rev_vsubsetD)

# lemma Transset_VPow: "Transset(i) \<Longrightarrow> Transset(VPow(i))"
#   by (auto simp: Transset_def)

# lemma Transset_Inf: "(\<And>i. i \<in> A \<Longrightarrow> Transset i) \<Longrightarrow> Transset (\<Sqinter> A)"
#   by (force simp: Transset_def Inf_V_def)

# lemma Transset_SUP: "(\<And>x. x \<in> A \<Longrightarrow> Transset (B x)) \<Longrightarrow> Transset (\<Squnion> (B ` A))"
#   by (metis Transset_Sup imageE)

# lemma Transset_INT: "(\<And>x. x \<in> A \<Longrightarrow> Transset (B x)) \<Longrightarrow> Transset (\<Sqinter> (B ` A))"
#   by (metis Transset_Inf imageE)


# subsubsection \<open>Zero, successor, sups\<close>

# lemma Ord_0 [iff]: "Ord 0"
#   by (auto simp: Ord_def)

# lemma Ord_succ [intro]:
#   assumes "Ord x" shows "Ord (succ x)"
#   using assms by (auto simp: Ord_def)

# lemma Ord_Sup:
#   assumes "\<And>x. x \<in> X \<Longrightarrow> Ord x" shows "Ord (\<Squnion>X)"
# proof (cases "small X")
#   case True
#   with assms show ?thesis
#     by (auto simp: Ord_def Transset_Sup)
# qed (simp add: Sup_V_def)

# lemma Ord_Union:
#   assumes "\<And>x. x \<in> X \<Longrightarrow> Ord x" "small X" shows "Ord (set (\<Union> (elts ` X)))"
#   by (metis Ord_Sup Sup_V_def assms)

# lemma Ord_sup:
#   assumes "Ord x" "Ord y" shows "Ord (x \<squnion> y)"
#   using assms
#   proof (clarsimp simp: Ord_def)
#   show "Transset (x \<squnion> y) \<and> (\<forall>y\<in>elts x \<union> elts y. Transset y)"
#     if "Transset x" "Transset y" "\<forall>y\<in>elts x. Transset y" "\<forall>y\<in>elts y. Transset y"
#     using Ord_def Transset_sup assms by auto
# qed

# lemma big_ON [simp]: "\<not> small ON"
# proof
#   assume "small ON"
#   then have "set ON \<in> ON"
#     by (metis Ord_Union Ord_succ Sup_upper elts_Sup elts_succ insertI1 mem_Collect_eq mem_not_refl set_of_elts vsubsetD)
#   then show False
#     by (metis \<open>small ON\<close> elts_of_set mem_not_refl)
# qed

# lemma Ord_1 [iff]: "Ord 1"
#   using Ord_succ one_V_def succ_def vinsert_def by fastforce

# lemma OrdmemD: "Ord k \<Longrightarrow> j \<in> elts k \<Longrightarrow> j < k"
#   using Ord_def Transset_def less_V_def by auto

# lemma Ord_trans: "\<lbrakk> i \<in> elts j;  j \<in> elts k;  Ord k \<rbrakk>  \<Longrightarrow> i \<in> elts k"
#   using Ord_def Transset_def by blast

# lemma mem_0_Ord:
#   assumes k: "Ord k" and knz: "k \<noteq> 0" shows "0 \<in> elts k"
#   by (metis Ord_def Transset_def inf.orderE k knz trad_foundation)

# lemma Ord_in_Ord: "\<lbrakk> Ord k;  m \<in> elts k \<rbrakk>  \<Longrightarrow> Ord m"
#   using Ord_def Ord_trans by blast

# lemma OrdI: "\<lbrakk>Transset i; \<And>x. x \<in> elts i \<Longrightarrow> Transset x\<rbrakk> \<Longrightarrow> Ord i"
#   by (simp add: Ord_def)

# lemma Ord_is_Transset: "Ord i \<Longrightarrow> Transset i"
#   by (simp add: Ord_def)

# lemma Ord_contains_Transset: "\<lbrakk>Ord i; j \<in> elts i\<rbrakk> \<Longrightarrow> Transset j"
#   using Ord_def by blast

# lemma ON_imp_Ord:
#   assumes "H \<subseteq> ON" "x \<in> H"
#   shows "Ord x"
#   using assms by blast

# lemma elts_subset_ON: "Ord \<alpha> \<Longrightarrow> elts \<alpha> \<subseteq> ON"
#   using Ord_in_Ord by blast

# lemma Transset_pred [simp]: "Transset x \<Longrightarrow> \<Squnion>(elts (succ x)) = x"
#   by (fastforce simp: Transset_def)

# lemma Ord_pred [simp]: "Ord \<beta> \<Longrightarrow> \<Squnion> (insert \<beta> (elts \<beta>)) = \<beta>"
#   using Ord_def Transset_pred by auto


# subsubsection \<open>Induction, Linearity, etc.\<close>

# lemma Ord_induct [consumes 1, case_names step]:
#   assumes k: "Ord k"
#       and step: "\<And>x.\<lbrakk> Ord x; \<And>y. y \<in> elts x \<Longrightarrow> P y \<rbrakk>  \<Longrightarrow> P x"
#     shows "P k"
#   using foundation k
# proof (induction k rule: wf_induct_rule)
#   case (less x)
#   then show ?case
#     using Ord_in_Ord local.step by auto
# qed

# text \<open>Comparability of ordinals\<close>
# lemma Ord_linear: "Ord k \<Longrightarrow> Ord l \<Longrightarrow> k \<in> elts l \<or> k=l \<or> l \<in> elts k"
# proof (induct k arbitrary: l rule: Ord_induct)
#   case (step k)
#   note step_k = step
#   show ?case using \<open>Ord l\<close>
#     proof (induct l rule: Ord_induct)
#       case (step l)
#       thus ?case using step_k
#         by (metis Ord_trans V_equalityI)
#     qed
# qed

# text \<open>The trichotomy law for ordinals\<close>
# lemma Ord_linear_lt:
#   assumes "Ord k" "Ord l"
#   obtains (lt) "k < l" | (eq) "k=l" | (gt) "l < k"
#   using Ord_linear OrdmemD assms by blast

# lemma Ord_linear2:
#   assumes "Ord k" "Ord l"
#   obtains (lt) "k < l" | (ge) "l \<le> k"
#   by (metis Ord_linear_lt eq_refl assms order.strict_implies_order)

# lemma Ord_linear_le:
#   assumes "Ord k" "Ord l"
#   obtains (le) "k \<le> l" | (ge) "l \<le> k"
#   by (meson Ord_linear2 le_less assms)

# lemma union_less_iff [simp]: "\<lbrakk>Ord i; Ord j\<rbrakk> \<Longrightarrow> i \<squnion> j < k \<longleftrightarrow> i<k \<and> j<k"
#   by (metis Ord_linear_le le_iff_sup sup.order_iff sup.strict_boundedE)

# lemma Ord_mem_iff_lt: "Ord k \<Longrightarrow> Ord l \<Longrightarrow> k \<in> elts l \<longleftrightarrow> k < l"
#   by (metis Ord_linear OrdmemD less_le_not_le)

# lemma Ord_Collect_lt: "Ord \<alpha> \<Longrightarrow> {\<xi>. Ord \<xi> \<and> \<xi> < \<alpha>} = elts \<alpha>"
#   by (auto simp flip: Ord_mem_iff_lt elim: Ord_in_Ord OrdmemD)

# lemma Ord_not_less: "\<lbrakk>Ord x; Ord y\<rbrakk> \<Longrightarrow> \<not> x < y \<longleftrightarrow> y \<le> x"
#   by (metis (no_types) Ord_linear2 leD)

# lemma Ord_not_le: "\<lbrakk>Ord x; Ord y\<rbrakk> \<Longrightarrow> \<not> x \<le> y \<longleftrightarrow> y < x"
#   by (metis (no_types) Ord_linear2 leD)

# lemma le_succ_iff: "Ord i \<Longrightarrow> Ord j \<Longrightarrow> succ i \<le> succ j \<longleftrightarrow> i \<le> j"
#   by (metis Ord_linear_le Ord_succ le_succE order_antisym)

# lemma succ_le_iff: "Ord i \<Longrightarrow> Ord j \<Longrightarrow> succ i \<le> j \<longleftrightarrow> i < j"
#   using Ord_mem_iff_lt dual_order.strict_implies_order less_eq_V_def by fastforce

# lemma succ_in_Sup_Ord:
#   assumes eq: "succ \<beta> = \<Squnion>A" and "small A" "A \<subseteq> ON" "Ord \<beta>"
#   shows "succ \<beta> \<in> A"
# proof -
#   have "\<not> \<Squnion>A \<le> \<beta>"
#     using eq \<open>Ord \<beta>\<close> succ_le_iff by fastforce
#   then show ?thesis
#     using assms by (metis Ord_linear2 Sup_least Sup_upper eq_iff mem_Collect_eq subsetD succ_le_iff)
# qed

# lemma in_succ_iff: "Ord i \<Longrightarrow> j \<in> elts (ZFC_in_HOL.succ i) \<longleftrightarrow> Ord j \<and> j \<le> i"
#   by (metis Ord_in_Ord Ord_mem_iff_lt Ord_not_le Ord_succ succ_le_iff)

# lemma zero_in_succ [simp,intro]: "Ord i \<Longrightarrow> 0 \<in> elts (succ i)"
#   using mem_0_Ord by auto

# lemma less_succ_self: "x < succ x"
#   by (simp add: less_eq_V_def order_neq_le_trans subset_insertI)

# lemma Ord_finite_Sup: "\<lbrakk>finite A; A \<subseteq> ON; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Squnion>A \<in> A"
# proof (induction A rule: finite_induct)
#   case (insert x A)
#   then have *: "small A" "A \<subseteq> ON" "Ord x"
#     by (auto simp add: ZFC_in_HOL.finite_imp_small insert.hyps)
#   show ?case
#   proof (cases "A = {}")
#     case False
#     then have "\<Squnion>A \<in> A"
#       using insert by blast
#     then have "\<Squnion>A \<le> x" if "x \<squnion> \<Squnion>A \<notin> A"
#       using * by (metis ON_imp_Ord Ord_linear_le sup.absorb2 that)
#     then show ?thesis
#       by (fastforce simp: \<open>small A\<close> Sup_V_insert)
#   qed auto
# qed auto


# subsubsection \<open>The natural numbers\<close>

# primrec ord_of_nat :: "nat \<Rightarrow> V" where
#   "ord_of_nat 0 = 0"
# | "ord_of_nat (Suc n) = succ (ord_of_nat n)"

# lemma ord_of_nat_eq_initial: "ord_of_nat n = set (ord_of_nat ` {..<n})"
#   by (induction n) (auto simp: lessThan_Suc succ_def)

# lemma mem_ord_of_nat_iff [simp]: "x \<in> elts (ord_of_nat n) \<longleftrightarrow> (\<exists>m<n. x = ord_of_nat m)"
#   by (subst ord_of_nat_eq_initial) auto

# lemma elts_ord_of_nat: "elts (ord_of_nat k) = ord_of_nat ` {..<k}"
#   by auto

# lemma Ord_equality: "Ord i \<Longrightarrow> i = \<Squnion> (succ ` elts i)"
#   by (force intro: Ord_trans)

# lemma Ord_ord_of_nat [simp]: "Ord (ord_of_nat k)"
#   by (induct k, auto)

# lemma ord_of_nat_equality: "ord_of_nat n = \<Squnion> ((succ \<circ> ord_of_nat) ` {..<n})"
#   by (metis Ord_equality Ord_ord_of_nat elts_of_set image_comp small_image_nat_V ord_of_nat_eq_initial)

# definition \<omega> :: V where "\<omega> \<equiv> set (range ord_of_nat)"

# lemma elts_\<omega>: "elts \<omega> = {\<alpha>. \<exists>n. \<alpha> = ord_of_nat n}"
#   by (auto simp: \<omega>_def image_iff)

# lemma nat_into_Ord [simp]: "n \<in> elts \<omega> \<Longrightarrow> Ord n"
#   by (metis Ord_ord_of_nat \<omega>_def elts_of_set image_iff inf)

# lemma Sup_\<omega>: "\<Squnion>(elts \<omega>) = \<omega>"
#   unfolding \<omega>_def by force

# lemma Ord_\<omega> [iff]: "Ord \<omega>"
#   by (metis Ord_Sup Sup_\<omega> nat_into_Ord)

# lemma zero_in_omega [iff]: "0 \<in> elts \<omega>"
#   by (metis \<omega>_def elts_of_set inf ord_of_nat.simps(1) rangeI)

# lemma succ_in_omega [simp]: "n \<in> elts \<omega> \<Longrightarrow> succ n \<in> elts \<omega>"
#   by (metis \<omega>_def elts_of_set image_iff small_image_nat_V ord_of_nat.simps(2) rangeI)

# lemma ord_of_eq_0: "ord_of_nat j = 0 \<Longrightarrow> j = 0"
#   by (induct j) (auto simp: succ_neq_zero)

# lemma ord_of_nat_le_omega: "ord_of_nat n \<le> \<omega>"
#   by (metis Sup_\<omega> ZFC_in_HOL.Sup_upper \<omega>_def elts_of_set inf rangeI)

# lemma ord_of_eq_0_iff [simp]: "ord_of_nat n = 0 \<longleftrightarrow> n=0"
#   by (auto simp: ord_of_eq_0)

# lemma ord_of_nat_inject [iff]: "ord_of_nat i = ord_of_nat j \<longleftrightarrow> i=j"
# proof (induct i arbitrary: j)
#   case 0 show ?case
#     using ord_of_eq_0 by auto
# next
#   case (Suc i) then show ?case
#     by auto (metis elts_0 elts_succ insert_not_empty not0_implies_Suc ord_of_nat.simps succ_inject_iff)
# qed

# corollary inj_ord_of_nat: "inj ord_of_nat"
#   by (simp add: linorder_injI)

# corollary countable:
#   assumes "countable X" shows "small X"
# proof -
#   have "X \<subseteq> range (from_nat_into X)"
#     by (simp add: assms subset_range_from_nat_into)
#   then show ?thesis
#     by (meson inf_raw inj_ord_of_nat replacement small_def smaller_than_small)
# qed

# corollary infinite_\<omega>: "infinite (elts \<omega>)"
#   using range_inj_infinite [of ord_of_nat]
#   by (simp add: \<omega>_def inj_ord_of_nat)

# corollary ord_of_nat_mono_iff [iff]: "ord_of_nat i \<le> ord_of_nat j \<longleftrightarrow> i \<le> j"
#   by (metis Ord_def Ord_ord_of_nat Transset_def eq_iff mem_ord_of_nat_iff not_less ord_of_nat_inject)

# corollary ord_of_nat_strict_mono_iff [iff]: "ord_of_nat i < ord_of_nat j \<longleftrightarrow> i < j"
#   by (simp add: less_le_not_le)

# lemma small_image_nat [simp]:
#   fixes N :: "nat set" shows "small (g ` N)"
#   by (simp add: countable)

# lemma finite_Ord_omega: "\<alpha> \<in> elts \<omega> \<Longrightarrow> finite (elts \<alpha>)"
#   proof (clarsimp simp add: \<omega>_def)
#   show "finite (elts (ord_of_nat n))" if "\<alpha> = ord_of_nat n" for n
#     using that by (simp add: ord_of_nat_eq_initial [of n])
# qed

# lemma infinite_Ord_omega: "Ord \<alpha> \<Longrightarrow> infinite (elts \<alpha>) \<Longrightarrow> \<omega> \<le> \<alpha>"
#   by (meson Ord_\<omega> Ord_linear2 Ord_mem_iff_lt finite_Ord_omega)

# lemma ord_of_minus_1: "n > 0 \<Longrightarrow> ord_of_nat n = succ (ord_of_nat (n - 1))"
#   by (metis Suc_diff_1 ord_of_nat.simps(2))

# lemma card_ord_of_nat [simp]: "card (elts (ord_of_nat m)) = m"
#   by (induction m) (auto simp: \<omega>_def finite_Ord_omega)

# lemma ord_of_nat_\<omega> [iff]:"ord_of_nat n \<in> elts \<omega>"
#   by (simp add: \<omega>_def)

# lemma succ_\<omega>_iff [iff]: "succ n \<in> elts \<omega> \<longleftrightarrow> n \<in> elts \<omega>"
#   by (metis Ord_\<omega> OrdmemD elts_vinsert insert_iff less_V_def succ_def succ_in_omega vsubsetD)

# lemma \<omega>_gt0 [simp]: "\<omega> > 0"
#   by (simp add: OrdmemD)

# lemma \<omega>_gt1 [simp]: "\<omega> > 1"
#   by (simp add: OrdmemD one_V_def)

# subsubsection\<open>Limit ordinals\<close>

# definition Limit :: "V\<Rightarrow>bool"
#   where "Limit i \<equiv> Ord i \<and> 0 \<in> elts i \<and> (\<forall>y. y \<in> elts i \<longrightarrow> succ y \<in> elts i)"

# lemma zero_not_Limit [iff]: "\<not> Limit 0"
#   by (simp add: Limit_def)

# lemma not_succ_Limit [simp]: "\<not> Limit(succ i)"
#   by (metis Limit_def Ord_mem_iff_lt elts_succ insertI1 less_irrefl)

# lemma Limit_is_Ord: "Limit \<xi> \<Longrightarrow> Ord \<xi>"
#   by (simp add: Limit_def)

# lemma succ_in_Limit_iff: "Limit \<xi> \<Longrightarrow> succ \<alpha> \<in> elts \<xi> \<longleftrightarrow> \<alpha> \<in> elts \<xi>"
#   by (metis Limit_def OrdmemD elts_succ insertI1 less_V_def vsubsetD)

# lemma Limit_eq_Sup_self [simp]: "Limit i \<Longrightarrow> Sup (elts i) = i"
#   apply (rule order_antisym)
#   apply (simp add: Limit_def Ord_def Transset_def Sup_least)
#   by (metis Limit_def Ord_equality Sup_V_def SUP_le_iff Sup_upper small_elts)

# lemma zero_less_Limit: "Limit \<beta> \<Longrightarrow> 0 < \<beta>"
#   by (simp add: Limit_def OrdmemD)

# lemma non_Limit_ord_of_nat [iff]: "\<not> Limit (ord_of_nat m)"
#   by (metis Limit_def mem_ord_of_nat_iff not_succ_Limit ord_of_eq_0_iff ord_of_minus_1)

# lemma Limit_omega [iff]: "Limit \<omega>"
#   by (simp add: Limit_def)

# lemma omega_nonzero [simp]: "\<omega> \<noteq> 0"
#   using Limit_omega by fastforce

# lemma Ord_cases_lemma:
#   assumes "Ord k" shows "k = 0 \<or> (\<exists>j. k = succ j) \<or> Limit k"
# proof (cases "Limit k")
#   case False
#   have "succ j \<in> elts k" if  "\<forall>j. k \<noteq> succ j" "j \<in> elts k" for j
#     by (metis Ord_in_Ord Ord_linear Ord_succ assms elts_succ insertE mem_not_sym that)
#   with assms show ?thesis
#     by (auto simp: Limit_def mem_0_Ord)
# qed auto

# lemma Ord_cases [cases type: V, case_names 0 succ limit]:
#   assumes "Ord k"
#   obtains "k = 0" | l where "Ord l" "succ l = k" | "Limit k"
#   by (metis assms Ord_cases_lemma Ord_in_Ord elts_succ insertI1)

# lemma non_succ_LimitI:
#   assumes "i\<noteq>0" "Ord(i)" "\<And>y. succ(y) \<noteq> i"
#   shows "Limit(i)"
#   using Ord_cases_lemma assms by blast

# lemma Ord_induct3 [consumes 1, case_names 0 succ Limit, induct type: V]:
#   assumes \<alpha>: "Ord \<alpha>"
#     and P: "P 0" "\<And>\<alpha>. \<lbrakk>Ord \<alpha>; P \<alpha>\<rbrakk> \<Longrightarrow> P (succ \<alpha>)"
#            "\<And>\<alpha>. \<lbrakk>Limit \<alpha>; \<And>\<xi>. \<xi> \<in> elts \<alpha> \<Longrightarrow> P \<xi>\<rbrakk> \<Longrightarrow> P (\<Squnion>\<xi> \<in> elts \<alpha>. \<xi>)"
#   shows "P \<alpha>"
#   using \<alpha>
# proof (induction \<alpha> rule: Ord_induct)
#   case (step \<alpha>)
#   then show ?case
#     by (metis Limit_eq_Sup_self Ord_cases P elts_succ image_ident insertI1)
# qed


# subsubsection\<open>Properties of LEAST for ordinals\<close>

# lemma
#   assumes "Ord k" "P k"
#   shows Ord_LeastI: "P (LEAST i. Ord i \<and> P i)" and Ord_Least_le: "(LEAST i. Ord i \<and> P i) \<le> k"
# proof -
#   have "P (LEAST i. Ord i \<and> P i) \<and> (LEAST i. Ord i \<and> P i) \<le> k"
#     using assms
#   proof (induct k rule: Ord_induct)
#     case (step x) then have "P x" by simp
#     show ?case proof (rule classical)
#       assume assm: "\<not> (P (LEAST a. Ord a \<and> P a) \<and> (LEAST a. Ord a \<and> P a) \<le> x)"
#       have "\<And>y. Ord y \<and> P y \<Longrightarrow> x \<le> y"
#       proof (rule classical)
#         fix y
#         assume y: "Ord y \<and> P y" "\<not> x \<le> y"
#         with step obtain "P (LEAST a. Ord a \<and> P a)" and le: "(LEAST a. Ord a \<and> P a) \<le> y"
#           by (meson Ord_linear2 Ord_mem_iff_lt)
#         with assm have "x < (LEAST a. Ord a \<and> P a)"
#           by (meson Ord_linear_le y order.trans \<open>Ord x\<close>)
#         then show "x \<le> y"
#           using le by auto
#       qed
#       then have Least: "(LEAST a. Ord a \<and> P a) = x"
#         by (simp add: Least_equality \<open>Ord x\<close> step.prems)
#       with \<open>P x\<close> show ?thesis by simp
#     qed
#   qed
#   then show "P (LEAST i. Ord i \<and> P i)" and "(LEAST i. Ord i \<and> P i) \<le> k" by auto
# qed

# lemma Ord_Least:
#   assumes "Ord k" "P k"
#   shows "Ord (LEAST i. Ord i \<and> P i)"
# proof -
#   have "Ord (LEAST i. Ord i \<and> (Ord i \<and> P i))"
#     using Ord_LeastI [where P = "\<lambda>i. Ord i \<and> P i"] assms by blast
#   then show ?thesis
#     by simp
# qed

# \<comment> \<open>The following 3 lemmas are due to Brian Huffman\<close>
# lemma Ord_LeastI_ex: "\<exists>i. Ord i \<and> P i \<Longrightarrow> P (LEAST i. Ord i \<and> P i)"
#   using Ord_LeastI by blast

# lemma Ord_LeastI2:
#   "\<lbrakk>Ord a; P a; \<And>x. \<lbrakk>Ord x; P x\<rbrakk> \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> Q (LEAST i. Ord i \<and> P i)"
#   by (blast intro: Ord_LeastI Ord_Least)

# lemma Ord_LeastI2_ex:
#   "\<exists>a. Ord a \<and> P a \<Longrightarrow> (\<And>x. \<lbrakk>Ord x; P x\<rbrakk> \<Longrightarrow> Q x) \<Longrightarrow> Q (LEAST i. Ord i \<and> P i)"
#   by (blast intro: Ord_LeastI_ex Ord_Least)

# lemma Ord_LeastI2_wellorder:
#   assumes "Ord a" "P a"
#   and "\<And>a. \<lbrakk> P a; \<forall>b. Ord b \<and> P b \<longrightarrow> a \<le> b \<rbrakk> \<Longrightarrow> Q a"
#   shows "Q (LEAST i. Ord i \<and> P i)"
# proof (rule LeastI2_order)
#   show "Ord (LEAST i. Ord i \<and> P i) \<and> P (LEAST i. Ord i \<and> P i)"
#     using Ord_Least Ord_LeastI assms by auto
# next
#   fix y assume "Ord y \<and> P y" thus "(LEAST i. Ord i \<and> P i) \<le> y"
#     by (simp add: Ord_Least_le)
# next
#   fix x assume "Ord x \<and> P x" "\<forall>y. Ord y \<and> P y \<longrightarrow> x \<le> y" thus "Q x"
#     by (simp add: assms(3))
# qed

# lemma Ord_LeastI2_wellorder_ex:
#   assumes "\<exists>x. Ord x \<and> P x"
#   and "\<And>a. \<lbrakk> P a; \<forall>b. Ord b \<and> P b \<longrightarrow> a \<le> b \<rbrakk> \<Longrightarrow> Q a"
#   shows "Q (LEAST i. Ord i \<and> P i)"
# using assms by clarify (blast intro!: Ord_LeastI2_wellorder)

# lemma not_less_Ord_Least: "\<lbrakk>k < (LEAST x. Ord x \<and> P x); Ord k\<rbrakk> \<Longrightarrow> \<not> P k"
#   using Ord_Least_le less_le_not_le by auto

# lemma exists_Ord_Least_iff: "(\<exists>\<alpha>. Ord \<alpha> \<and> P \<alpha>) \<longleftrightarrow> (\<exists>\<alpha>. Ord \<alpha> \<and> P \<alpha> \<and> (\<forall>\<beta> < \<alpha>. Ord \<beta> \<longrightarrow> \<not> P \<beta>))" (is "?lhs \<longleftrightarrow> ?rhs")
# proof
#   assume ?rhs thus ?lhs by blast
# next
#   assume H: ?lhs then obtain \<alpha> where \<alpha>: "Ord \<alpha>" "P \<alpha>" by blast
#   let ?x = "LEAST \<alpha>. Ord \<alpha> \<and> P \<alpha>"
#   have "Ord ?x"
#     by (metis Ord_Least \<alpha>)
#   moreover
#   { fix \<beta> assume m: "\<beta> < ?x" "Ord \<beta>"
#     from not_less_Ord_Least[OF m] have "\<not> P \<beta>" . }
#   ultimately show ?rhs
#     using Ord_LeastI_ex[OF H] by blast
# qed

# lemma Ord_mono_imp_increasing:
#   assumes fun_hD: "h \<in> D \<rightarrow> D"
#     and mono_h: "strict_mono_on D h"
#     and "D \<subseteq> ON" and \<nu>: "\<nu> \<in> D"
#   shows "\<nu> \<le> h \<nu>"
# proof (rule ccontr)
#   assume non: "\<not> \<nu> \<le> h \<nu>"
#   define \<mu> where "\<mu> \<equiv> LEAST \<mu>. Ord \<mu> \<and> \<not> \<mu> \<le> h \<mu> \<and> \<mu> \<in> D"
#   have "Ord \<nu>"
#     using \<nu> \<open>D \<subseteq> ON\<close> by blast
#   then have \<mu>: "\<not> \<mu> \<le> h \<mu> \<and> \<mu> \<in> D"
#     unfolding \<mu>_def by (rule Ord_LeastI) (simp add: \<nu> non)
#   have "Ord (h \<nu>)"
#     using assms by auto
#   then have "Ord (h (h \<nu>))"
#     by (meson ON_imp_Ord \<nu> assms funcset_mem)
#   have "Ord \<mu>"
#     using \<mu> \<open>D \<subseteq> ON\<close> by blast
#   then have "h \<mu> < \<mu>"
#     by (metis ON_imp_Ord Ord_linear2 PiE \<mu> \<open>D \<subseteq> ON\<close> fun_hD)
#   then have "\<not> h \<mu> \<le> h (h \<mu>)"
#     using \<mu> fun_hD mono_h by (force simp: strict_mono_on_def)
#   moreover have *: "h \<mu> \<in> D"
#     using \<mu> fun_hD by auto
#   moreover have "Ord (h \<mu>)"
#     using \<open>D \<subseteq> ON\<close> * by blast
#   ultimately have "\<mu> \<le> h \<mu>"
#     by (simp add: \<mu>_def Ord_Least_le)
#   then show False
#     using \<mu> by blast
# qed

# lemma le_Sup_iff:
#   assumes "A \<subseteq> ON" "Ord x" "small A" shows "x \<le> \<Squnion>A \<longleftrightarrow> (\<forall>y \<in> ON. y<x \<longrightarrow> (\<exists>a\<in>A. y < a))"
# proof (intro iffI ballI impI)
#   show "\<exists>a\<in>A. y < a"
#     if "x \<le> \<Squnion> A" "y \<in> ON" "y < x"
#     for y
#   proof -
#     have "\<not> \<Squnion> A \<le> y" "Ord y"
#       using that by auto
#     then show ?thesis
#       by (metis Ord_linear2 Sup_least \<open>A \<subseteq> ON\<close> mem_Collect_eq subset_eq)
#   qed
#   show "x \<le> \<Squnion> A"
#     if "\<forall>y\<in>ON. y < x \<longrightarrow> (\<exists>a\<in>A. y < a)"
#     using that assms
#     by (metis Ord_Sup Ord_linear_le Sup_upper less_le_not_le mem_Collect_eq subsetD)
# qed

# lemma le_SUP_iff: "\<lbrakk>f ` A \<subseteq> ON; Ord x; small A\<rbrakk> \<Longrightarrow> x \<le> \<Squnion>(f ` A) \<longleftrightarrow> (\<forall>y \<in> ON. y<x \<longrightarrow> (\<exists>i\<in>A. y < f i))"
#   by (simp add: le_Sup_iff)

# subsection\<open>Transfinite Recursion and the V-levels\<close>

# definition transrec :: "((V \<Rightarrow> 'a) \<Rightarrow> V \<Rightarrow> 'a) \<Rightarrow> V \<Rightarrow> 'a"
#   where "transrec H a \<equiv> wfrec {(x,y). x \<in> elts y} H a"

# lemma transrec: "transrec H a = H (\<lambda>x \<in> elts a. transrec H x) a"
# proof -
#   have "(cut (wfrec {(x, y). x \<in> elts y} H) {(x, y). x \<in> elts y} a)
#       = (\<lambda>x\<in>elts a. wfrec {(x, y). x \<in> elts y} H x)"
#     by (force simp: cut_def)
#   then show ?thesis
#     unfolding transrec_def
#     by (simp add: foundation wfrec)
# qed

# text\<open>Avoids explosions in proofs; resolve it with a meta-level definition\<close>
# lemma def_transrec:
#     "\<lbrakk>\<And>x. f x \<equiv> transrec H x\<rbrakk> \<Longrightarrow> f a = H(\<lambda>x \<in> elts a. f x) a"
#   by (metis restrict_ext transrec)

# lemma eps_induct [case_names step]:
#   assumes "\<And>x. (\<And>y. y \<in> elts x \<Longrightarrow> P y) \<Longrightarrow> P x"
#   shows "P a"
#   using wf_induct [OF foundation] assms by auto


# definition Vfrom :: "[V,V] \<Rightarrow> V"
#   where "Vfrom a \<equiv> transrec (\<lambda>f x. a \<squnion> \<Squnion>((\<lambda>y. VPow(f y)) ` elts x))"

# abbreviation Vset :: "V \<Rightarrow> V" where "Vset \<equiv> Vfrom 0"

# lemma Vfrom: "Vfrom a i = a \<squnion> \<Squnion>((\<lambda>j. VPow(Vfrom a j)) ` elts i)"
#   apply (subst Vfrom_def)
#   apply (subst transrec)
#   using Vfrom_def by auto

# lemma Vfrom_0 [simp]: "Vfrom a 0 = a"
#   by (subst Vfrom) auto

# lemma Vset: "Vset i = \<Squnion>((\<lambda>j. VPow(Vset j)) ` elts i)"
#   by (subst Vfrom) auto

# lemma Vfrom_mono1:
#   assumes "a \<le> b" shows "Vfrom a i \<le> Vfrom b i"
# proof (induction i rule: eps_induct)
#   case (step i)
#   then have "a \<squnion> (\<Squnion>j\<in>elts i. VPow (Vfrom a j)) \<le> b \<squnion> (\<Squnion>j\<in>elts i. VPow (Vfrom b j))"
#     by (intro sup_mono cSUP_subset_mono \<open>a \<le> b\<close>) auto
#   then show ?case
#     by (metis Vfrom)
# qed

# lemma Vfrom_mono2: "Vfrom a i \<le> Vfrom a (i \<squnion> j)"
# proof (induction arbitrary: j rule: eps_induct)
#   case (step i)
#   then have "a \<squnion> (\<Squnion>j\<in>elts i. VPow (Vfrom a j))
#            \<le> a \<squnion> (\<Squnion>j\<in>elts (i \<squnion> j). VPow (Vfrom a j))"
#     by (intro sup_mono cSUP_subset_mono order_refl) auto
#   then show ?case
#     by (metis Vfrom)
# qed

# lemma Vfrom_mono: "\<lbrakk>Ord i; a\<le>b; i\<le>j\<rbrakk> \<Longrightarrow> Vfrom a i \<le> Vfrom b j"
#   by (metis (no_types) Vfrom_mono1 Vfrom_mono2 dual_order.trans sup.absorb_iff2)

# lemma Transset_Vfrom: "Transset(A) \<Longrightarrow> Transset(Vfrom A i)"
# proof (induction i rule: eps_induct)
#   case (step i)
#   then show ?case
#     by (metis Transset_SUP Transset_VPow Transset_sup Vfrom)
# qed

# lemma Transset_Vset [simp]: "Transset(Vset i)"
#   by (simp add: Transset_Vfrom)

# lemma Vfrom_sup: "Vfrom a (i \<squnion> j) = Vfrom a i \<squnion> Vfrom a j"
# proof (rule order_antisym)
#   show "Vfrom a (i \<squnion> j) \<le> Vfrom a i \<squnion> Vfrom a j"
#     by (simp add: Vfrom [of a "i \<squnion> j"] Vfrom [of a i] Vfrom [of a j] Sup_Un_distrib image_Un sup.assoc sup.left_commute)
#   show "Vfrom a i \<squnion> Vfrom a j \<le> Vfrom a (i \<squnion> j)"
#     by (metis Vfrom_mono2 le_supI sup_commute)
# qed

# lemma Vfrom_succ_Ord:
#   assumes "Ord i" shows "Vfrom a (succ i) = a \<squnion> VPow(Vfrom a i)"
# proof (cases "i = 0")
#   case True
#   then show ?thesis
#     by (simp add: Vfrom [of _ "succ 0"])
# next
#   case False
#   have *: "(\<Squnion>x\<in>elts i. VPow (Vfrom a x)) \<le> VPow (Vfrom a i)"
#   proof (rule cSup_least)
#     show "(\<lambda>x. VPow (Vfrom a x)) ` elts i \<noteq> {}"
#       using False by auto
#     show "x \<le> VPow (Vfrom a i)" if "x \<in> (\<lambda>x. VPow (Vfrom a x)) ` elts i" for x
#       using that
#       by clarsimp (meson Ord_in_Ord Ord_linear_le Vfrom_mono assms mem_not_refl order_refl vsubsetD)
#   qed
#   show ?thesis
#   proof (rule Vfrom [THEN trans])
#     show "a \<squnion> (\<Squnion>j\<in>elts (succ i). VPow (Vfrom a j)) = a \<squnion> VPow (Vfrom a i)"
#       using assms
#       by (intro sup_mono order_antisym) (auto simp: Sup_V_insert *)
#   qed
# qed

# lemma Vset_succ: "Ord i \<Longrightarrow> Vset(succ(i)) = VPow(Vset(i))"
#   by (simp add: Vfrom_succ_Ord)

# lemma Vfrom_Sup:
#   assumes "X \<noteq> {}" "small X"
#   shows "Vfrom a (Sup X) = (\<Squnion>y\<in>X. Vfrom a y)"
# proof (rule order_antisym)
#   have "Vfrom a (\<Squnion> X) = a \<squnion> (\<Squnion>j\<in>elts (\<Squnion> X). VPow (Vfrom a j))"
#     by (metis Vfrom)
#   also have "\<dots> \<le> \<Squnion> (Vfrom a ` X)"
#   proof -
#     have "a \<le> \<Squnion> (Vfrom a ` X)"
#       by (metis Vfrom all_not_in_conv assms bdd_above_iff_small cSUP_upper2 replacement sup_ge1)
#     moreover have "(\<Squnion>j\<in>elts (\<Squnion> X). VPow (Vfrom a j)) \<le> \<Squnion> (Vfrom a ` X)"
#     proof -
#       have "VPow (Vfrom a x) \<le> \<Squnion> (Vfrom a ` X)"
#         if "y \<in> X" "x \<in> elts y" for x y
#       proof -
#         have "VPow (Vfrom a x) \<le> Vfrom a y"
#           by (metis Vfrom bdd_above_iff_small cSUP_upper2 le_supI2 order_refl replacement small_elts that(2))
#         also have "\<dots> \<le> \<Squnion> (Vfrom a ` X)"
#           using assms that by (force intro: cSUP_upper)
#         finally show ?thesis .
#       qed
#       then show ?thesis
#         by (simp add: SUP_le_iff \<open>small X\<close>)
#     qed
#     ultimately show ?thesis
#       by auto
#   qed
#   finally show "Vfrom a (\<Squnion> X) \<le> \<Squnion> (Vfrom a ` X)" .
#   have "\<And>x. x \<in> X \<Longrightarrow>
#          a \<squnion> (\<Squnion>j\<in>elts x. VPow (Vfrom a j))
#          \<le> a \<squnion> (\<Squnion>j\<in>elts (\<Squnion> X). VPow (Vfrom a j))"
#     using cSUP_subset_mono \<open>small X\<close> by auto
#   then show "\<Squnion> (Vfrom a ` X) \<le> Vfrom a (\<Squnion> X)"
#     by (metis Vfrom assms(1) cSUP_least)
# qed

# lemma Limit_Vfrom_eq:
#     "Limit(i) \<Longrightarrow> Vfrom a i = (\<Squnion>y \<in> elts i. Vfrom a y)"
#   by (metis Limit_def Limit_eq_Sup_self Vfrom_Sup ex_in_conv small_elts)

# end

# %%
