theory SPES
  imports "HOL-Library.Multiset"
begin

datatype query = Table string

datatype svalue = SNull | SNat nat
type_synonym row = "svalue list"
type_synonym table = "row multiset"
type_synonym db = "string \<Rightarrow> table"
consts schema :: "string \<Rightarrow> nat"

definition wellformed_table :: "table \<Rightarrow> nat \<Rightarrow> bool" where
"wellformed_table t n \<equiv> \<forall>r\<in>#t. length r = n"

definition wellformed_db :: "db \<Rightarrow> bool" where
"wellformed_db db \<equiv> \<forall>t. wellformed_table (db t) (schema t)"

datatype fol_expr = Var nat | Const nat | Neg fol_expr | And fol_expr fol_expr | Or fol_expr fol_expr | Eq fol_expr fol_expr

type_synonym fol_env = "nat \<Rightarrow> nat"

fun bneg :: "nat \<Rightarrow> nat" where
"bneg 0 = 1" |
"bneg _ = 0"

fun band :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"band (Suc _) (Suc _) = 1" |
"band _ _ = 0"

fun bor :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"bor 0 0 = 0" |
"bor _ _ = 1"

fun fol_eval :: "fol_expr \<Rightarrow> fol_env \<Rightarrow> nat" where
"fol_eval (Var i) env = env i" |
"fol_eval (Const c) _ = c" |
"fol_eval (Neg e) env = bneg (fol_eval e env)" |
"fol_eval (And e1 e2) env = band (fol_eval e1 env) (fol_eval e2 env)" |
"fol_eval (Or e1 e2) env = bor (fol_eval e1 env) (fol_eval e2 env)" |
"fol_eval (Eq e1 e2) env = (if fol_eval e1 env = fol_eval e2 env then 1 else 0)"

definition imp :: "fol_expr \<Rightarrow> fol_expr \<Rightarrow> fol_expr" where
"imp f1 f2 \<equiv> (Or (Neg f1) f2)"

record symbolic_column =
  val :: fol_expr
  is_null :: fol_expr

record qpsr =
  cols1 :: "symbolic_column list"
  cols2 :: "symbolic_column list"
  cond  :: fol_expr

type_synonym qpsr_env = "fol_env multiset"

definition include_qpsr_row :: "fol_expr \<Rightarrow> fol_env \<Rightarrow> bool" where
"include_qpsr_row condp env \<equiv> fol_eval condp env > 0"

definition eval_symbolic_column :: "symbolic_column \<Rightarrow> fol_env \<Rightarrow> svalue" where
"eval_symbolic_column c env \<equiv> if fol_eval (is_null c) env > 0 then SNull else SNat (fol_eval (val c) env)"

definition eval_qpsr_row :: "symbolic_column list \<Rightarrow> fol_env \<Rightarrow> row" where
"eval_qpsr_row cols env \<equiv> map (\<lambda>col. eval_symbolic_column col env) cols"

definition eval_qpsr_table :: "symbolic_column list \<Rightarrow> fol_expr \<Rightarrow> qpsr_env \<Rightarrow> table" where
"eval_qpsr_table cols condp env \<equiv> image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row condp) env)"

definition eval_qpsr :: "qpsr \<Rightarrow> qpsr_env \<Rightarrow> (table \<times> table)" where
"eval_qpsr qpsr env \<equiv> (eval_qpsr_table (cols1 qpsr) (cond qpsr) env, eval_qpsr_table (cols2 qpsr) (cond qpsr) env)"

fun eval_query :: "query \<Rightarrow> db \<Rightarrow> table" where
"eval_query (Table t) db = db t"

fun init_tuple :: "nat \<Rightarrow> nat \<Rightarrow> symbolic_column list" where
"init_tuple _ 0 = []" |
"init_tuple i (Suc c) = \<lparr> val = Var i, is_null = Var (i+1) \<rparr>#init_tuple (i+2) c"

definition veri_table :: "string \<Rightarrow> string \<Rightarrow> qpsr option" where
"veri_table t1 t2 \<equiv> if t1 = t2 then Some (\<lparr> cols1 = init_tuple 0 (schema t1), cols2 = init_tuple 0 (schema t1), cond = Const 1 \<rparr>) else None"

fun veri_card :: "query \<Rightarrow> query \<Rightarrow> qpsr option" where
"veri_card (Table t1) (Table t2) = veri_table t1 t2"

definition symbolic_col_eq_expr :: "symbolic_column \<Rightarrow> symbolic_column \<Rightarrow> fol_expr" where
"symbolic_col_eq_expr c1 c2 \<equiv> Or (And (is_null c1) (is_null c2)) (And (Eq (val c1) (val c2)) (Eq (is_null c1) (is_null c2)))"

fun symbolic_cols_eq_expr :: "symbolic_column list \<Rightarrow> symbolic_column list \<Rightarrow> fol_expr" where
"symbolic_cols_eq_expr [] [] = Const 1" |
"symbolic_cols_eq_expr (x#xs) (y#ys) = And (symbolic_col_eq_expr x y) (symbolic_cols_eq_expr xs ys)" |
"symbolic_cols_eq_expr _ _ = Const 0"

definition qpsr_is_eq :: "qpsr \<Rightarrow> bool" where
"qpsr_is_eq qpsr \<equiv> \<forall>env. fol_eval (imp (cond qpsr) (symbolic_cols_eq_expr (cols1 qpsr) (cols2 qpsr))) env > 0"

definition spes :: "query \<Rightarrow> query \<Rightarrow> bool" where
"spes q1 q2 \<equiv> case veri_card q1 q2 of None \<Rightarrow> False | Some qpsr \<Rightarrow> qpsr_is_eq qpsr"

lemma impr:
  assumes "fol_eval a env > 0"
  shows "(fol_eval (imp a b) env > 0) = (fol_eval b env > 0)"
  by (metis One_nat_def assms bneg.elims bor.elims fol_eval.simps(3,5) gr0_conv_Suc imp_def)

lemma eval_qpsr_table_row:
  assumes "\<forall>r\<in>#t. \<exists>envr. include_qpsr_row condp envr \<and> eval_qpsr_row cols envr = r"
  shows "\<exists>env. eval_qpsr_table cols condp env = t"
using assms proof (induct t)
  case empty
  then show ?case
    by (metis eval_qpsr_table_def filter_empty_mset image_mset_empty)
next
  case (add x t)
  then show ?case
    by (smt (verit, del_insts) add_mset_commute eval_qpsr_table_def filter_mset_add_mset image_mset_add_mset multi_member_split union_single_eq_member)
qed

lemma init_tuple_env_cong:
  "(\<forall>j\<ge>i. env1 j = env2 j) \<Longrightarrow> eval_qpsr_row (init_tuple i n) env1 = eval_qpsr_row (init_tuple i n) env2"
proof (induct n arbitrary: i)
  case 0
  then show ?case by (simp add: eval_qpsr_row_def)
next
  case (Suc n)
  have tail: "eval_qpsr_row (init_tuple (i+2) n) env1 = eval_qpsr_row (init_tuple (i+2) n) env2"
    using Suc.hyps Suc.prems by force
  have "env1 i = env2 i" "env1 (i+1) = env2 (i+1)" using Suc.prems by auto
  then have head: "eval_symbolic_column \<lparr>val = Var i, is_null = Var (i+1)\<rparr> env1
                  = eval_symbolic_column \<lparr>val = Var i, is_null = Var (i+1)\<rparr> env2"
    by (simp add: eval_symbolic_column_def)
  show ?case using head tail by (simp add: eval_qpsr_row_def)
qed

lemma veri_table_qpsr_h4_gen:
  "\<exists>envr. eval_qpsr_row (init_tuple i (length r)) envr = r"
proof (induct r arbitrary: i)
  case Nil
  then show ?case by (simp add: eval_qpsr_row_def)
next
  case (Cons a r)
  obtain envr where IH: "eval_qpsr_row (init_tuple (i+2) (length r)) envr = r"
    using Cons.hyps by blast
  define envr' where "envr' \<equiv> envr(i := (case a of SNat v \<Rightarrow> v | SNull \<Rightarrow> 0),
                                       i+1 := (case a of SNat _ \<Rightarrow> 0 | SNull \<Rightarrow> 1))"
  have tail: "eval_qpsr_row (init_tuple (i+2) (length r)) envr' = r"
  proof -
    have "\<forall>j\<ge>i+2. envr' j = envr j" unfolding envr'_def by auto
    then show ?thesis
      by (metis (full_types) IH init_tuple_env_cong)
  qed
  have head: "eval_symbolic_column \<lparr>val = Var i, is_null = Var (i+1)\<rparr> envr' = a"
  proof (cases a)
    case SNull
    then show ?thesis unfolding envr'_def eval_symbolic_column_def by simp
  next
    case (SNat v)
    then show ?thesis unfolding envr'_def eval_symbolic_column_def by simp
  qed
  have "eval_qpsr_row (init_tuple i (Suc (length r))) envr' = a # r"
    using head tail by (simp add: eval_qpsr_row_def)
  then show ?case by auto
qed

lemma veri_table_qpsr_h4:
  shows "\<exists>envr. eval_qpsr_row (init_tuple 0 (length r)) envr = r"
  using veri_table_qpsr_h4_gen by blast

lemma veri_table_qpsr_h3:
  shows "\<exists>envr. include_qpsr_row (Const 1) envr \<and> eval_qpsr_row (init_tuple 0 (length r)) envr = r"
  by (simp add: include_qpsr_row_def veri_table_qpsr_h4)

lemma veri_table_qpsr_h2:
  assumes "wellformed_table x l"
  shows "\<exists>env. eval_qpsr_table (init_tuple 0 l) (Const 1) env = x"
  by (smt (verit, del_insts) assms eval_qpsr_table_row veri_table_qpsr_h3 wellformed_table_def)

lemma veri_table_qpsr_h:
  assumes "wellformed_db db"
  shows "\<exists>env. eval_qpsr_table (init_tuple 0 (schema t)) (Const 1) env = eval_query (Table t) db"
  by (metis assms veri_table_qpsr_h2 eval_query.simps wellformed_db_def)               

lemma veri_table_qpsr:
  assumes "wellformed_db db"
  assumes "veri_table t1 t2 = Some qpsr"
  shows "\<exists>env. eval_qpsr qpsr env = (eval_query (Table t1) db, eval_query (Table t2) db)"
  by (metis assms(1,2) eval_qpsr_def option.distinct(1) option.sel qpsr.ext_inject qpsr.surjective veri_table_def veri_table_qpsr_h)

lemma veri_card_qpsr:
  assumes "wellformed_db db"
  assumes "veri_card q1 q2 = Some qpsr"
  shows "\<exists>env. eval_qpsr qpsr env = (eval_query q1 db, eval_query q2 db)"
using assms proof (induct rule: veri_card.induct)
  case (1 t1 t2)
  then show ?case
    using veri_table_qpsr by auto
qed

lemma qpsr_is_eq_cond_true_h:
  assumes "qpsr_is_eq qpsr"
  assumes "include_qpsr_row (cond qpsr) envr"
  shows "fol_eval (symbolic_cols_eq_expr (cols1 qpsr) (cols2 qpsr)) envr > 0"
  by (metis assms(2) assms(1) qpsr_is_eq_def include_qpsr_row_def impr)

lemma qpsr_is_eq_cond_true_h4:
  assumes "fol_eval (symbolic_cols_eq_expr (x#xs) (y#ys)) envr > 0"
  shows "fol_eval (symbolic_col_eq_expr x y) envr > 0"
  by (metis assms band.elims fol_eval.simps(4) gr0_conv_Suc symbolic_cols_eq_expr.simps(2))

lemma qpsr_is_eq_cond_true_h5:
  assumes "fol_eval (symbolic_col_eq_expr x y) envr > 0"
  shows "eval_symbolic_column x envr = eval_symbolic_column y envr"
proof (cases "fol_eval (And (is_null x) (is_null y)) envr > 0")
  case True
  then show ?thesis
    by (metis band.elims eval_symbolic_column_def fol_eval.simps(4) zero_less_Suc)
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) assms band.elims bor.simps(1) eval_symbolic_column_def fol_eval.simps(4,5,6) gr0_conv_Suc symbolic_col_eq_expr_def)
qed

lemma qpsr_is_eq_cond_true_h3:
  assumes "fol_eval (symbolic_cols_eq_expr (x#xs) (y#ys)) envr > 0"
  shows "eval_symbolic_column x envr = eval_symbolic_column y envr"
  by (metis assms qpsr_is_eq_cond_true_h5 qpsr_is_eq_cond_true_h4)

lemma qpsr_is_eq_cond_true_h2:
  assumes "fol_eval (symbolic_cols_eq_expr c1 c2) envr > 0"
  shows "eval_qpsr_row c1 envr = eval_qpsr_row c2 envr"
using assms proof (induct rule: symbolic_cols_eq_expr.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs y ys)
  then show ?case
    using eval_qpsr_row_def qpsr_is_eq_cond_true_h3 by force
next
  case ("3_1" v va)
  then show ?case by simp
next
  case ("3_2" v va)
  then show ?case by simp
qed

lemma qpsr_is_eq_cond_true:
  assumes "qpsr_is_eq qpsr"
  assumes "include_qpsr_row (cond qpsr) envr"
  shows "eval_qpsr_row (cols1 qpsr) envr = eval_qpsr_row (cols2 qpsr) envr"
  by (metis assms(2) assms(1) qpsr_is_eq_cond_true_h qpsr_is_eq_cond_true_h2)

lemma eval_qpsr_eq:
  assumes "eval_qpsr qpsr env = (x, y)"
  assumes "qpsr_is_eq qpsr"
  shows "x = y"
  by (metis assms(1,2) eval_qpsr_def eval_qpsr_table_def filter_mset_eq_conv fst_conv image_mset_cong qpsr_is_eq_cond_true snd_conv)

theorem spes_sound:
  assumes "wellformed_db db"
  assumes "spes q1 q2"
  shows "eval_query q1 db = eval_query q2 db"
  by (metis assms(1,2) case_optionE eval_qpsr_eq spes_def veri_card_qpsr)

end