theory SPES
  imports "HOL-Library.Multiset"
begin

datatype op = Plus | Minus
datatype sql_expr = Column nat | SConst nat | Null | Bin sql_expr op sql_expr

datatype query = Table string | Project query "sql_expr list"

datatype svalue = SNull | SNat nat
type_synonym row = "svalue list"
type_synonym table = "row multiset"
type_synonym db = "string \<Rightarrow> table"
consts schema :: "string \<Rightarrow> nat"

definition wellformed_table :: "table \<Rightarrow> nat \<Rightarrow> bool" where
"wellformed_table t n \<equiv> \<forall>r\<in>#t. length r = n"

definition wellformed_db :: "db \<Rightarrow> bool" where
"wellformed_db db \<equiv> \<forall>t. wellformed_table (db t) (schema t)"

fun wellformed_sql_expr :: "sql_expr \<Rightarrow> nat \<Rightarrow> bool" where
"wellformed_sql_expr (Column i) n = (i < n)" |
"wellformed_sql_expr (Bin e1 _ e2) n = (wellformed_sql_expr e1 n \<and> wellformed_sql_expr e2 n)" |
"wellformed_sql_expr _ _ = True"

fun query_output_length :: "query \<Rightarrow> nat" where
"query_output_length (Table t) = schema t" |
"query_output_length (Project _ s) = length s"

fun wellformed_query :: "query \<Rightarrow> bool" where
"wellformed_query (Table _) = True" |
"wellformed_query (Project q s) = (wellformed_query q \<and> (\<forall>sv\<in>set s. wellformed_sql_expr sv (query_output_length q)))"

datatype fol_expr = Var nat | Const nat | Neg fol_expr | And fol_expr fol_expr |
  Or fol_expr fol_expr | Eq fol_expr fol_expr | FPlus fol_expr fol_expr | FMinus fol_expr fol_expr

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
"fol_eval (Eq e1 e2) env = (if fol_eval e1 env = fol_eval e2 env then 1 else 0)" |
"fol_eval (FPlus e1 e2) env = fol_eval e1 env + fol_eval e2 env" |
"fol_eval (FMinus e1 e2) env = fol_eval e1 env - fol_eval e2 env"

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

fun op_op :: "op \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat)" where
"op_op Plus = (+)" |
"op_op Minus = (-)"

fun eval_op :: "op \<Rightarrow> svalue \<Rightarrow> svalue \<Rightarrow> svalue" where
"eval_op op (SNat n1) (SNat n2) = SNat (op_op op n1 n2)" |
"eval_op _ _ _ = SNull"

fun project_single :: "sql_expr \<Rightarrow> row \<Rightarrow> svalue" where
"project_single (Column i) r = r ! i" |
"project_single (SConst v) _ = SNat v" |
"project_single Null _ = SNull" |
"project_single (Bin e1 op e2) r = eval_op op (project_single e1 r) (project_single e2 r)"

definition project_row :: "sql_expr list \<Rightarrow> row \<Rightarrow> row" where
"project_row s r \<equiv> map (\<lambda>sv. project_single sv r) s"

definition project :: "sql_expr list \<Rightarrow> table \<Rightarrow> table" where
"project s t \<equiv> image_mset (project_row s) t"

fun eval_query :: "query \<Rightarrow> db \<Rightarrow> table" where
"eval_query (Table t) db = db t" |
"eval_query (Project q s) db = project s (eval_query q db)"

fun init_tuple :: "nat \<Rightarrow> nat \<Rightarrow> symbolic_column list" where
"init_tuple _ 0 = []" |
"init_tuple i (Suc c) = \<lparr> val = Var i, is_null = Var (i+1) \<rparr>#init_tuple (i+2) c"

definition veri_table :: "string \<Rightarrow> string \<Rightarrow> qpsr option" where
"veri_table t1 t2 \<equiv> if t1 = t2 then Some (\<lparr> cols1 = init_tuple 0 (schema t1), cols2 = init_tuple 0 (schema t1), cond = Const 1 \<rparr>) else None"

fun const_op_h :: "op \<Rightarrow> fol_expr \<Rightarrow> fol_expr \<Rightarrow> fol_expr" where
"const_op_h Plus a b = FPlus a b" |
"const_op_h Minus a b = FMinus a b"

definition const_op :: "op \<Rightarrow> symbolic_column \<Rightarrow> symbolic_column \<Rightarrow> symbolic_column" where
"const_op op c1 c2 \<equiv> \<lparr> val = const_op_h op (val c1) (val c2), is_null = Or (is_null c1) (is_null c2) \<rparr>"

fun const_expr :: "symbolic_column list \<Rightarrow> sql_expr \<Rightarrow> symbolic_column" where
"const_expr cols (Column i) = cols ! i" |
"const_expr _ (SConst v) = \<lparr> val = Const v, is_null = Const 0 \<rparr>" |
"const_expr _ Null = \<lparr> val = Const 0, is_null = Const 1 \<rparr>" |
"const_expr cols (Bin e1 op e2) = const_op op (const_expr cols e1) (const_expr cols e2)"

definition const_expr_list :: "symbolic_column list \<Rightarrow> sql_expr list \<Rightarrow> symbolic_column list" where
"const_expr_list cols s \<equiv> map (const_expr cols) s"

definition veri_project :: "qpsr \<Rightarrow> sql_expr list \<Rightarrow> sql_expr list \<Rightarrow> qpsr" where
"veri_project qpsr s1 s2 \<equiv> \<lparr> cols1 = const_expr_list (cols1 qpsr) s1, cols2 = const_expr_list (cols2 qpsr) s2, cond = cond qpsr \<rparr>"

fun veri_card :: "query \<Rightarrow> query \<Rightarrow> qpsr option" where
"veri_card (Table t1) (Table t2) = veri_table t1 t2" |
"veri_card (Project q1 s1) (Project q2 s2) = (case veri_card q1 q2 of None \<Rightarrow> None | Some qpsr \<Rightarrow> Some (veri_project qpsr s1 s2))" |
"veri_card _ _ = None"

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

lemma imp_elim:
  assumes "fol_eval a env > 0"
  shows "(fol_eval (imp a b) env > 0) = (fol_eval b env > 0)"
  by (metis One_nat_def assms bneg.elims bor.elims fol_eval.simps(3,5) gr0_conv_Suc imp_def)

lemma wellformed_query_sub:
  assumes "wellformed_query (Project q s)"
  shows "wellformed_query q"
  by (metis assms wellformed_query.simps(2))

lemma eval_qpsr_table_from_rows:
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

lemma init_tuple_surj:
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

lemma init_tuple_surj_with_cond:
  shows "\<exists>envr. include_qpsr_row (Const 1) envr \<and> eval_qpsr_row (init_tuple 0 (length r)) envr = r"
  by (metis include_qpsr_row_def init_tuple_surj fol_eval.simps(2) less_one)

lemma eval_qpsr_table_surj:
  assumes "wellformed_table x l"
  shows "\<exists>env. eval_qpsr_table (init_tuple 0 l) (Const 1) env = x"
  by (smt (verit, del_insts) assms eval_qpsr_table_from_rows init_tuple_surj_with_cond wellformed_table_def)

lemma eval_qpsr_table_surj_db:
  assumes "wellformed_db db"
  shows "\<exists>env. eval_qpsr_table (init_tuple 0 (schema t)) (Const 1) env = eval_query (Table t) db"
  by (metis assms eval_qpsr_table_surj wellformed_db_def eval_query.simps(1))

lemma veri_table_correct:
  assumes "wellformed_db db"
  assumes "veri_table t1 t2 = Some qpsr"
  shows "\<exists>env. eval_qpsr qpsr env = (eval_query (Table t1) db, eval_query (Table t2) db)"
  by (metis assms(1,2) eval_qpsr_def option.distinct(1) option.sel qpsr.ext_inject qpsr.surjective veri_table_def eval_qpsr_table_surj_db)

lemma project_image_mset:
  shows "project s (image_mset f x) = image_mset (\<lambda>r. project_row s (f r)) x"
  by (metis (no_types, lifting) ext SPES.project_def empty_iff image_mset.compositionality image_mset_single insert_iff set_mset_add_mset_insert set_mset_empty)

lemma eval_qpsr_row_map:
  shows "eval_qpsr_row (map f x) envr = map (\<lambda>col. eval_symbolic_column (f col) envr) x"
  using eval_qpsr_row_def by auto

lemma eval_const_op:
  "eval_symbolic_column (const_op opr c1 c2) envr = eval_op opr (eval_symbolic_column c1 envr) (eval_symbolic_column c2 envr)"
  unfolding eval_symbolic_column_def const_op_def
  by (cases "fol_eval (is_null c1) envr"; cases "fol_eval (is_null c2) envr"; cases opr) auto

lemma const_expr_correct:
  assumes "wellformed_sql_expr sv (length cols)"
  shows "eval_symbolic_column ((const_expr cols) sv) envr = project_single sv (map (\<lambda>col. eval_symbolic_column col envr) cols)"
using assms proof (induct sv)
  case (Column i)
  have "eval_symbolic_column (cols ! i) envr = (map (\<lambda>col. eval_symbolic_column col envr) cols) ! i"
    using Column by force
  then show ?case by simp
next
  case (SConst x)
  then show ?case
    by (simp add: eval_symbolic_column_def)
next
  case Null
  have "eval_symbolic_column \<lparr> val = Const 0, is_null = Const 1 \<rparr> envr = SNull"
    by (simp add: eval_symbolic_column_def)
  then show ?case by simp
next
  case (Bin e1 op e2)
  then show ?case
    using eval_const_op by force
qed

lemma const_expr_list_correct_row:
  assumes "\<forall>sv \<in> set s. wellformed_sql_expr sv (length cols)"
  shows "eval_qpsr_row (const_expr_list cols s) envr = project_row s (eval_qpsr_row cols envr)"
  using const_expr_list_def assms const_expr_correct eval_qpsr_row_def project_row_def by simp

lemma const_expr_list_correct_table:
  assumes "\<forall>sv \<in> set s. wellformed_sql_expr sv (length cols)"
  shows "eval_qpsr_table (const_expr_list cols s) condp env = project s (eval_qpsr_table cols condp env)"
  by (metis (mono_tags, lifting) assms eval_qpsr_table_def multiset.map_cong project_image_mset const_expr_list_correct_row)

lemma veri_project_correct:
  assumes "\<forall>sv \<in> set s1. wellformed_sql_expr sv (length (cols1 qpsr))"
  assumes "\<forall>sv \<in> set s2. wellformed_sql_expr sv (length (cols2 qpsr))"
  assumes "eval_qpsr qpsr env = (x, y)"
  shows "eval_qpsr (veri_project qpsr s1 s2) env = (project s1 x, project s2 y)"
  unfolding eval_qpsr_def
  using assms eval_qpsr_def veri_project_def const_expr_list_correct_table by auto

lemma veri_project_correct_query:
  assumes "\<forall>sv \<in> set s1. wellformed_sql_expr sv (length (cols1 qpsr))"
  assumes "\<forall>sv \<in> set s2. wellformed_sql_expr sv (length (cols2 qpsr))"
  assumes "eval_qpsr qpsr env = (eval_query q1 db, eval_query q2 db)"
  shows "eval_qpsr (veri_project qpsr s1 s2) env = (eval_query (Project q1 s1) db, eval_query (Project q2 s2) db)"
  by (simp add: assms(1,2,3) veri_project_correct)

lemma veri_card_cols_length:
  assumes "wellformed_query q1"
  assumes "wellformed_query q2"
  assumes "veri_card q1 q2 = Some qpsr"
  shows "length (cols1 qpsr) = query_output_length q1 \<and> length (cols2 qpsr) = query_output_length q2"
using assms proof (induct rule: veri_card.induct)
  case (1 t1 t2)
  have "length (init_tuple 0 (schema t1)) = schema t1"
    by (metis Ex_list_of_length eval_qpsr_row_def length_map init_tuple_surj)
  then show ?case
    by (metis "1.prems"(3) option.distinct(1) option.inject qpsr.ext_inject qpsr.surjective query_output_length.simps(1) veri_card.simps(1) veri_table_def)
next
  case (2 q1 s1 q2 s2)
  obtain qpsr where "veri_card q1 q2 = Some qpsr"
    using "2.prems"(3) by fastforce
  have "length (const_expr_list (cols1 qpsr) s1) = query_output_length (Project q1 s1)"
    using const_expr_list_def by auto
  have "length (const_expr_list (cols2 qpsr) s2) = query_output_length (Project q2 s2)"
    by (simp add: const_expr_list_def)
  then show ?case
    using "2.prems"(3) \<open>length (const_expr_list (cols1 qpsr) s1) = query_output_length (Project q1 s1)\<close> \<open>veri_card q1 q2 = Some qpsr\<close> veri_project_def by auto
next
  case ("3_1" v va vb)
  then show ?case by simp
next
  case ("3_2" vb v va)
  then show ?case by simp
qed

lemma veri_card_correct:
  assumes "wellformed_db db"
  assumes "wellformed_query q1"
  assumes "wellformed_query q2"
  assumes "veri_card q1 q2 = Some qpsr"
  shows "\<exists>env. eval_qpsr qpsr env = (eval_query q1 db, eval_query q2 db)"
using assms proof (induct arbitrary: qpsr rule: veri_card.induct)
  case (1 t1 t2)
  then show ?case
    using veri_table_correct by auto
next
  case (2 q1 s1 q2 s2)
  obtain qpsr where "veri_card q1 q2 = Some qpsr"
    using "2.prems"(4) by fastforce
  obtain env where "eval_qpsr qpsr env = (eval_query q1 db, eval_query q2 db)"
    using "2.hyps" "2.prems"(2,3) \<open>veri_card q1 q2 = Some qpsr\<close> assms(1) wellformed_query_sub by blast
  then show ?case
    by (smt (verit) "2.prems"(2,3,4) \<open>veri_card q1 q2 = Some qpsr\<close> option.sel option.simps(5) veri_card.simps(2) veri_project_correct_query wellformed_query.simps(2) veri_card_cols_length)
next
  case ("3_1" v va vb)
  then show ?case by simp
next
  case ("3_2" vb v va)
  then show ?case by simp
qed

lemma symbolic_col_eq_expr_head:
  assumes "fol_eval (symbolic_cols_eq_expr (x#xs) (y#ys)) envr > 0"
  shows "fol_eval (symbolic_col_eq_expr x y) envr > 0"
  by (metis assms band.elims fol_eval.simps(4) gr0_conv_Suc symbolic_cols_eq_expr.simps(2))

lemma symbolic_col_eq_expr_correct:
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

lemma symbolic_cols_eq_expr_correct:
  assumes "fol_eval (symbolic_cols_eq_expr c1 c2) envr > 0"
  shows "eval_qpsr_row c1 envr = eval_qpsr_row c2 envr"
using assms proof (induct rule: symbolic_cols_eq_expr.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs y ys)
  then show ?case
    using eval_qpsr_row_def symbolic_col_eq_expr_correct symbolic_col_eq_expr_head by fastforce
next
  case ("3_1" v va)
  then show ?case by simp
next
  case ("3_2" v va)
  then show ?case by simp
qed

lemma qpsr_is_eq_rows_eq:
  assumes "qpsr_is_eq qpsr"
  assumes "include_qpsr_row (cond qpsr) envr"
  shows "eval_qpsr_row (cols1 qpsr) envr = eval_qpsr_row (cols2 qpsr) envr"
  by (meson SPES.imp_elim assms(1,2) include_qpsr_row_def qpsr_is_eq_def symbolic_cols_eq_expr_correct)

lemma eval_qpsr_eq:
  assumes "eval_qpsr qpsr env = (x, y)"
  assumes "qpsr_is_eq qpsr"
  shows "x = y"
  by (metis assms(1,2) eval_qpsr_def eval_qpsr_table_def filter_mset_eq_conv fst_conv image_mset_cong qpsr_is_eq_rows_eq snd_conv)

theorem spes_sound:
  assumes "wellformed_db db"
  assumes "wellformed_query q1"
  assumes "wellformed_query q2"
  assumes "spes q1 q2"
  shows "eval_query q1 db = eval_query q2 db"
proof -
  obtain qpsr where vc: "veri_card q1 q2 = Some qpsr" and eq: "qpsr_is_eq qpsr"
    using assms(4) unfolding spes_def by (auto split: option.splits)
  obtain env where "eval_qpsr qpsr env = (eval_query q1 db, eval_query q2 db)"
    using veri_card_correct[OF assms(1,2,3) vc] by blast
  then show ?thesis
    using eval_qpsr_eq eq by auto
qed

end