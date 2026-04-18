theory SPES
  imports "HOL-Library.Multiset"
begin

datatype op = Plus | Minus
datatype sql_expr = Column nat | SConst nat | Null | Bin sql_expr op sql_expr
datatype logic = LAnd | LOr
datatype sql_pred = IsNull sql_expr | Not sql_pred | BinL sql_pred logic sql_pred

datatype query = Table string | Project query "sql_expr list" | Select query sql_pred | Union "query list"

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

fun wellformed_sql_pred :: "sql_pred \<Rightarrow> nat \<Rightarrow> bool" where
"wellformed_sql_pred (IsNull e) n = wellformed_sql_expr e n" |
"wellformed_sql_pred (Not p) n = wellformed_sql_pred p n" |
"wellformed_sql_pred (BinL p1 _ p2) n = (wellformed_sql_pred p1 n \<and> wellformed_sql_pred p2 n)"

fun query_output_length :: "query \<Rightarrow> nat" where
"query_output_length (Table t) = schema t" |
"query_output_length (Project _ s) = length s" |
"query_output_length (Select q _) = query_output_length q" |
"query_output_length (Union []) = 0" |
"query_output_length (Union (x#xs)) = query_output_length x"

fun wellformed_query :: "query \<Rightarrow> bool" where
"wellformed_query (Table _) = True" |
"wellformed_query (Project q s) = (wellformed_query q \<and> (\<forall>sv\<in>set s. wellformed_sql_expr sv (query_output_length q)))" |
"wellformed_query (Select q c) = (wellformed_query q \<and> (wellformed_sql_pred c (query_output_length q)))" |
"wellformed_query (Union qs) = (\<exists>k. \<forall>q\<in> set qs. wellformed_query q \<and> query_output_length q = k)"

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

fun eval_l :: "logic \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
"eval_l LAnd = (\<and>)" |
"eval_l LOr = (\<or>)"

fun satisfies_cond :: "sql_pred \<Rightarrow> row \<Rightarrow> bool" where
"satisfies_cond (IsNull e) r = (project_single e r = SNull)" |
"satisfies_cond (Not p) r = (\<not>satisfies_cond p r)" |
"satisfies_cond (BinL p1 l p2) r = eval_l l (satisfies_cond p1 r) (satisfies_cond p2 r)"

definition select :: "sql_pred \<Rightarrow> table \<Rightarrow> table" where
"select c t \<equiv> filter_mset (satisfies_cond c) t"

fun eval_query :: "query \<Rightarrow> db \<Rightarrow> table" where
"eval_query (Table t) db = db t" |
"eval_query (Project q s) db = project s (eval_query q db)" |
"eval_query (Select q c) db = select c (eval_query q db)" |
"eval_query (Union qs) db = sum_mset (mset (map (\<lambda>q. eval_query q db) qs))"

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

fun const_logic :: "logic \<Rightarrow> fol_expr \<Rightarrow> fol_expr \<Rightarrow> fol_expr" where
"const_logic LAnd = And" |
"const_logic LOr = Or"

fun const_pred :: "symbolic_column list \<Rightarrow> sql_pred \<Rightarrow> fol_expr" where
"const_pred cols (IsNull e) = is_null (const_expr cols e)" |
"const_pred cols (Not p) = Neg (const_pred cols p)" |
"const_pred cols (BinL p1 l p2) = const_logic l (const_pred cols p1) (const_pred cols p2)"

definition veri_select :: "qpsr \<Rightarrow> sql_pred \<Rightarrow> sql_pred \<Rightarrow> qpsr option" where
"veri_select qpsr c1 c2 \<equiv> let c1' = const_pred (cols1 qpsr) c1; c2' = const_pred (cols2 qpsr) c2 in (
  if (\<forall>env. fol_eval c1' env = fol_eval c2' env) then
    Some \<lparr> cols1 = cols1 qpsr, cols2 = cols2 qpsr, cond = And (cond qpsr) c1' \<rparr>
  else None
)"

definition symbolic_col_eq_expr :: "symbolic_column \<Rightarrow> symbolic_column \<Rightarrow> fol_expr" where
"symbolic_col_eq_expr c1 c2 \<equiv> Or (And (is_null c1) (is_null c2)) (And (Eq (val c1) (val c2)) (Eq (is_null c1) (is_null c2)))"

fun symbolic_cols_eq_expr :: "symbolic_column list \<Rightarrow> symbolic_column list \<Rightarrow> fol_expr" where
"symbolic_cols_eq_expr [] [] = Const 1" |
"symbolic_cols_eq_expr (x#xs) (y#ys) = And (symbolic_col_eq_expr x y) (symbolic_cols_eq_expr xs ys)" |
"symbolic_cols_eq_expr _ _ = Const 0"

definition qpsr_is_eq :: "qpsr \<Rightarrow> bool" where
"qpsr_is_eq qpsr \<equiv> (length (cols1 qpsr) = length (cols2 qpsr)) \<and> (\<forall>env. fol_eval (imp (cond qpsr) (symbolic_cols_eq_expr (cols1 qpsr) (cols2 qpsr))) env > 0)"

fun veri_card :: "query \<Rightarrow> query \<Rightarrow> qpsr option" and
    veri_union :: "query list \<Rightarrow> query list \<Rightarrow> qpsr option" where
"veri_card (Table t1) (Table t2) = veri_table t1 t2" |
"veri_card (Project q1 s1) (Project q2 s2) = (case veri_card q1 q2 of None \<Rightarrow> None | Some qpsr \<Rightarrow> Some (veri_project qpsr s1 s2))" |
"veri_card (Select q1 c1) (Select q2 c2) = (case veri_card q1 q2 of None \<Rightarrow> None | Some qpsr \<Rightarrow> veri_select qpsr c1 c2)" |
"veri_card (Union qs1) (Union qs2) = veri_union qs1 qs2" |
"veri_card _ _ = None" |

"veri_union [] []  = Some \<lparr> cols1 = [], cols2 = [], cond = Const 1 \<rparr>" |
"veri_union (x#xs) (y#ys) = (case veri_card x y of None \<Rightarrow> None | Some qpsr1 \<Rightarrow> (if qpsr_is_eq qpsr1 then (
  case veri_union xs ys of None \<Rightarrow> None |
  Some _ \<Rightarrow> Some \<lparr> cols1 = init_tuple 0 (query_output_length x), cols2 = init_tuple 0 (query_output_length x), cond = Const 1 \<rparr>
) else None))" |
"veri_union _ _ = None"

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

lemma qpsr_is_eq_:
  assumes "qpsr_is_eq qpsr"
  shows "length (cols1 qpsr) = length (cols2 qpsr)"
  using assms qpsr_is_eq_def by blast

lemma veri_card_cols_length:
   "\<lbrakk>wellformed_query q1; wellformed_query q2; veri_card q1 q2 = Some qpsr\<rbrakk> \<Longrightarrow> (length (cols1 qpsr) = query_output_length q1) \<and> (length (cols2 qpsr) = query_output_length q2)"
and veri_union_cols_length: "\<lbrakk>wellformed_query (query.Union qs1); wellformed_query (query.Union qs2); veri_union qs1 qs2 = Some qpsr\<rbrakk> \<Longrightarrow> (length (cols1 qpsr) = query_output_length (query.Union qs1)) \<and> (length (cols2 qpsr) = query_output_length (query.Union qs2))"
proof (induct arbitrary: qpsr and qpsr rule: veri_card_veri_union.induct)
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
  case (3 q1 c1 q2 c2)
  obtain qpsr where "veri_card q1 q2 = Some qpsr"
    using "3.prems"(3) by force
  have "length (cols1 qpsr) = query_output_length q1 \<and> length (cols2 qpsr) = query_output_length q2"
    using "3.hyps" "3.prems"(1,2) \<open>veri_card q1 q2 = Some qpsr\<close> by auto
  then have "length (cols1 qpsr) = query_output_length (Select q1 c1) \<and> length (cols2 qpsr) = query_output_length (Select q2 c2)" by simp
  then show ?case
    by (smt (verit) "3.prems"(3) \<open>veri_card q1 q2 = Some qpsr\<close> option.distinct(1) option.sel option.simps(5) qpsr.select_convs(1,2) veri_card.simps(3) veri_select_def)
next
  case (4 qs1 qs2)
  then show ?case by simp
next
  case ("5_1" v va vb)
  then show ?case by simp
next
  case ("5_2" v va vb vc)
  then show ?case by simp
next
  case ("5_3" v va vb)
  then show ?case by simp
next
  case ("5_4" v va vb)
  then show ?case by simp
next
  case ("5_5" v va vb vc)
  then show ?case by simp
next
  case ("5_6" v va vb)
  then show ?case by simp
next
  case ("5_7" v va)
  then show ?case by simp
next
  case ("5_8" v va vb)
  then show ?case by simp
next
  case ("5_9" v va vb)
  then show ?case by simp
next
  case ("5_10" vb v va)
  then show ?case by simp
next
  case ("5_11" vb vc v va)
  then show ?case by simp
next
  case ("5_12" vb v va)
  then show ?case by simp
next
  case ("5_13" vb v va)
  then show ?case by simp
next
  case ("5_14" vb vc v va)
  then show ?case by simp
next
  case ("5_15" vb v va)
  then show ?case by simp
next
  case ("5_16" va v)
  then show ?case by simp
next
  case ("5_17" va vb v)
  then show ?case by simp
next
  case ("5_18" va vb v)
  then show ?case by simp
next
  case (6 uw)
  then show ?case by auto
next
  case (7 x xs y ys n)
  have "cols1 n = init_tuple 0 (query_output_length x)"
    by (smt (verit, del_insts) "7.prems"(3) option.case_eq_if option.distinct(1) option.sel qpsr.select_convs(1) veri_union.simps(2))
  have "cols2 n = init_tuple 0 (query_output_length x)"
    by (smt (verit, del_insts) "7.prems"(3) option.case_eq_if option.distinct(1) option.sel qpsr.select_convs(2) veri_union.simps(2))
  have "query_output_length x = query_output_length y" proof (cases "veri_card x y")
    case None
    then show ?thesis
      using "7.prems"(3) by auto
  next
    case (Some qpsr1)
    have "qpsr_is_eq qpsr1"
      by (metis (mono_tags, lifting) "7.prems"(3) Some option.distinct(1) option.simps(5) veri_union.simps(2))
    have "query_output_length x = length (cols1 qpsr1)"
      by (metis "7.hyps"(1) "7.prems"(1,2) Some list.set_intros(1) wellformed_query.simps(4))
    have "query_output_length y = length (cols2 qpsr1)"
      using "7.hyps"(1) "7.prems"(1,2) Some by fastforce
    then show ?thesis
      using \<open>qpsr_is_eq qpsr1\<close> \<open>query_output_length x = length (cols1 qpsr1)\<close> qpsr_is_eq_def by fastforce
  qed
  have "length (cols1 n) = query_output_length x \<and> length (cols2 n) = query_output_length y"
    by (metis Ex_list_of_length \<open>cols1 n = init_tuple 0 (query_output_length x)\<close> \<open>cols2 n = init_tuple 0 (query_output_length x)\<close> \<open>query_output_length x = query_output_length y\<close> eval_qpsr_row_def init_tuple_surj_with_cond
        length_map)
  then show ?case by simp
next
  case ("8_1" v va uz)
  then show ?case by simp
next
  case ("8_2" v va uz)
  then show ?case by simp
qed

lemma eval_qpsr_table_filter:
  shows "eval_qpsr_table cols condp (filter_mset f x) = image_mset (eval_qpsr_row cols) (filter_mset (\<lambda>xv. include_qpsr_row condp xv \<and> f xv) x)"
  by (smt (verit, best) eval_qpsr_table_def filter_filter_mset filter_mset_cong0)

lemma eval_qpsr_table_empty [simp]: "eval_qpsr_table a b {#} = {#}"
  unfolding eval_qpsr_table_def
  by simp

lemma include_qpsr_row_and [simp]:
  "include_qpsr_row (And a b) = (\<lambda>x. include_qpsr_row a x \<and> include_qpsr_row b x)"
  unfolding include_qpsr_row_def proof
  fix env
  show "(0 < fol_eval (And a b) env) = (0 < fol_eval a env \<and> 0 < fol_eval b env)"
    by (metis band.elims band.simps(2,3) bot_nat_0.not_eq_extremum fol_eval.simps(4) zero_less_one)
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

lemma fol_eval_and_intro:
  assumes "\<forall>env. fol_eval a env = fol_eval b env"
  shows "\<forall>env. fol_eval (And x a) env = fol_eval (And x b) env"
  by (simp add: assms)

lemma eval_qpsr_table_eq_cond:
  assumes "\<forall>env. fol_eval c1 env = fol_eval c2 env"
  shows "\<forall>env. eval_qpsr_table c c1 env = eval_qpsr_table c c2 env"
  using assms eval_qpsr_table_def include_qpsr_row_def by presburger

lemma veri_select_correct4:
  assumes "wellformed_sql_pred c (length cols)"
  shows "include_qpsr_row (const_pred cols c) env = satisfies_cond c (eval_qpsr_row cols env)"
using assms proof (induct c)
  case (IsNull e)
  then have wf: "wellformed_sql_expr e (length cols)" by simp
  have "eval_symbolic_column (const_expr cols e) env
          = project_single e (eval_qpsr_row cols env)"
    using const_expr_correct[OF wf] by (simp add: eval_qpsr_row_def)
  then show ?case
    by (metis const_pred.simps(1) eval_symbolic_column_def include_qpsr_row_def
              satisfies_cond.simps(1) svalue.simps(3))
next
  case (Not p)
  from Not.prems have wf: "wellformed_sql_pred p (length cols)" by simp
  with Not.hyps have IH:
    "include_qpsr_row (const_pred cols p) env = satisfies_cond p (eval_qpsr_row cols env)"
    by simp
  have neg_eq:
    "(fol_eval (Neg (const_pred cols p)) env > 0)
       = (\<not> (fol_eval (const_pred cols p) env > 0))"
    by (cases "fol_eval (const_pred cols p) env") auto
  show ?case
    using IH neg_eq by (simp add: include_qpsr_row_def)
next
  case (BinL p1 l p2)
  from BinL.prems have wf1: "wellformed_sql_pred p1 (length cols)"
                    and wf2: "wellformed_sql_pred p2 (length cols)" by auto
  from BinL.hyps(1) wf1 have IH1:
    "include_qpsr_row (const_pred cols p1) env = satisfies_cond p1 (eval_qpsr_row cols env)"
    by simp
  from BinL.hyps(2) wf2 have IH2:
    "include_qpsr_row (const_pred cols p2) env = satisfies_cond p2 (eval_qpsr_row cols env)"
    by simp
  have include_or:
    "include_qpsr_row (Or a b) env = (include_qpsr_row a env \<or> include_qpsr_row b env)" for a b
    unfolding include_qpsr_row_def
    by (cases "fol_eval a env"; cases "fol_eval b env") auto
  show ?case
  proof (cases l)
    case LAnd
    then show ?thesis using IH1 IH2 by simp
  next
    case LOr
    then show ?thesis using IH1 IH2 include_or by simp
  qed
qed

lemma veri_select_correct3:
  assumes "wellformed_sql_pred c (length cols)"
  shows "eval_qpsr_table cols (And condp (const_pred cols c)) env = select c (eval_qpsr_table cols condp env)"
  unfolding eval_qpsr_table_def select_def proof -
  show "image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row (And condp (const_pred cols c))) env) =
        filter_mset (satisfies_cond c) (image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row condp) env))" proof (induct env)
    case empty
    then show ?case by simp
  next
    case (add x env)
    have "image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row (And condp (const_pred cols c))) env) =
          filter_mset (satisfies_cond c) (image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row condp) env))"
      using add by blast
    then have h: "image_mset (eval_qpsr_row cols) (filter_mset (\<lambda>v. include_qpsr_row condp v \<and> include_qpsr_row (const_pred cols c) v) env) =
          filter_mset (satisfies_cond c) (image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row condp) env))" by simp


    have "image_mset (eval_qpsr_row cols) (filter_mset (\<lambda>v. include_qpsr_row condp v \<and> include_qpsr_row (const_pred cols c) v) (add_mset x env)) =
    filter_mset (satisfies_cond c) (image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row condp) (add_mset x env)))" proof (cases "include_qpsr_row condp x")
      case True
      have "image_mset (eval_qpsr_row cols) (filter_mset (\<lambda>v. include_qpsr_row condp v \<and> include_qpsr_row (const_pred cols c) v) (add_mset x env)) =
    filter_mset (satisfies_cond c) (add_mset (eval_qpsr_row cols x) ((image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row condp) env))))"
        using True h veri_select_correct4 assms by force
      then show ?thesis
        using \<open>image_mset (eval_qpsr_row cols)
 {#v \<in># add_mset x env.
  include_qpsr_row condp v \<and> include_qpsr_row (const_pred cols c) v#} =
filter_mset (satisfies_cond c)
 (add_mset (eval_qpsr_row cols x)
   (image_mset (eval_qpsr_row cols)
     (filter_mset (include_qpsr_row condp) env)))\<close> \<open>image_mset (eval_qpsr_row cols)
 (filter_mset (include_qpsr_row (And condp (const_pred cols c))) env) =
filter_mset (satisfies_cond c)
 (image_mset (eval_qpsr_row cols)
   (filter_mset (include_qpsr_row condp) env))\<close> by fastforce
    next
      case False
      then show ?thesis
        by (simp add: h)
    qed
    then show "image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row (And condp (const_pred cols c))) (add_mset x env)) =
    filter_mset (satisfies_cond c) (image_mset (eval_qpsr_row cols) (filter_mset (include_qpsr_row condp) (add_mset x env)))" by simp
  qed
qed

lemma veri_select_correct2:
  assumes "wellformed_sql_pred c1 (length cols1p)"
  assumes "wellformed_sql_pred c2 (length cols2p)"
  assumes "eval_qpsr_table cols2p condp env = y"
  assumes "\<forall>env. fol_eval (const_pred cols1p c1) env = fol_eval (const_pred cols2p c2) env"
  shows "eval_qpsr_table cols2p (And condp (const_pred cols1p c1)) env = select c2 y"
proof -
  have "\<forall>env. fol_eval (And condp (const_pred cols1p c1)) env = fol_eval (And condp (const_pred cols2p c2)) env" using fol_eval_and_intro assms by simp
  have "eval_qpsr_table cols2p (And condp (const_pred cols2p c2)) env = select c2 (eval_qpsr_table cols2p condp env)" using veri_select_correct3 assms by simp
  have "eval_qpsr_table cols2p (And condp (const_pred cols1p c1)) env = select c2 (eval_qpsr_table cols2p condp env)"
    by (metis \<open>\<forall>env. fol_eval (And condp (const_pred cols1p c1)) env = fol_eval (And condp (const_pred cols2p c2)) env\<close>
        \<open>eval_qpsr_table cols2p (And condp (const_pred cols2p c2)) env = select c2 (eval_qpsr_table cols2p condp env)\<close> eval_qpsr_table_eq_cond)
  then show ?thesis
    by (simp add: assms) 
qed

lemma eval_union_add [simp]:
  shows "eval_query (Union (x#xs)) db = eval_query (Union xs) db + eval_query x db"
  by simp


lemma veri_select_correct:
  assumes "wellformed_sql_pred c1 (length (cols1 qpsr))"
  assumes "wellformed_sql_pred c2 (length (cols2 qpsr))"
  assumes "eval_qpsr qpsr env1 = (x, y)"
  assumes "\<forall>env. fol_eval (const_pred (cols1 qpsr)c1) env = fol_eval (const_pred (cols2 qpsr) c2) env"
  shows "\<exists>env. eval_qpsr \<lparr> cols1 = cols1 qpsr, cols2 = cols2 qpsr, cond = And (cond qpsr) (const_pred (cols1 qpsr) c1) \<rparr> env = (select c1 x, select c2 y)"
proof
  show "eval_qpsr \<lparr>cols1 = cols1 qpsr, cols2 = cols2 qpsr, cond = And (cond qpsr) (const_pred (cols1 qpsr) c1)\<rparr> env1 = (select c1 x, select c2 y)"
    using assms(1,2) eval_qpsr_def veri_select_correct2 assms by auto
qed

lemma eval_qpsr_table_plus:
  assumes "eval_qpsr_table cols condp a = x"
  assumes "eval_qpsr_table cols condp b = y"
  shows "eval_qpsr_table cols condp (a + b) = x + y"
  using assms(1,2) eval_qpsr_table_def by auto

lemma eval_qpsr_plus:
  assumes "eval_qpsr qpsr a = (x1, x2)"
  assumes "eval_qpsr qpsr b = (y1, y2)"
  shows "eval_qpsr qpsr (a + b) = (x1 + y1, x2 + y2)"
  using assms(1,2) eval_qpsr_def eval_qpsr_table_plus by auto

lemma veri_union_h:
  assumes "\<forall>r\<in>#x. length r = n"
  assumes "eval_qpsr \<lparr> cols1 = init_tuple 0 n, cols2 = init_tuple 0 n, cond = Const 1 \<rparr> env1 = (xs, ys)"
  shows "\<exists>env. eval_qpsr \<lparr> cols1 = init_tuple 0 n, cols2 = init_tuple 0 n, cond = Const 1 \<rparr> env = (x + xs, x + ys)"
proof -
  obtain env2 where "eval_qpsr \<lparr> cols1 = init_tuple 0 n, cols2 = init_tuple 0 n, cond = Const 1 \<rparr> env2 = (x, x)"
    using assms(1) eval_qpsr_def eval_qpsr_table_surj wellformed_table_def by fastforce
  then have "eval_qpsr \<lparr> cols1 = init_tuple 0 n, cols2 = init_tuple 0 n, cond = Const 1 \<rparr> (env1 + env2) = (x + xs, x + ys)"
    using assms(2) eval_qpsr_plus by auto
  show ?thesis
    by (metis \<open>eval_qpsr
 \<lparr>cols1 = init_tuple 0 n, cols2 = init_tuple 0 n,
    cond = Const 1\<rparr>
 (env1 + env2) =
(x + xs, x + ys)\<close>)
qed

lemma query_output_length_h:
  assumes "wellformed_db db"
  assumes "wellformed_query q"
  shows "\<forall>r\<in>#eval_query q db. length r = query_output_length q"
using assms proof (induct q arbitrary: db)
  case (Table x)
  then show ?case 
    by (simp add: wellformed_db_def wellformed_table_def)
next
  case (Project q s)
  have "\<forall>x. length (project_row s x) = length s"
    using project_row_def by auto
  then have "\<forall>r\<in>#image_mset (project_row s) (eval_query q db). length r = length s"
    by simp
  then show ?case
    using project_def by auto
next
  case (Select q x2)
  then show ?case
    by (simp add: SPES.select_def)
next
  case (Union x)
  then show ?case using assms proof (induct x)
    case Nil
    then show ?case by simp
  next
    case (Cons a x)
    then show ?case by force
  qed
qed

lemma union_output_len:
  assumes "wellformed_query (Union (x#(xx#xxs)))"
  shows "query_output_length x = query_output_length (Union (xx#xxs))"
  using assms by force

lemma veri_card_correct:
   "\<lbrakk>wellformed_db db; wellformed_query q1; wellformed_query q2; veri_card q1 q2 = Some qpsr\<rbrakk> \<Longrightarrow> \<exists>env. eval_qpsr qpsr env = (eval_query q1 db, eval_query q2 db)"
and veri_union_correct: "\<lbrakk>wellformed_db db; wellformed_query (Union qs1); wellformed_query (Union qs2); veri_union qs1 qs2 = Some qpsr\<rbrakk> \<Longrightarrow> \<exists>env. eval_qpsr qpsr env = (eval_query (Union qs1) db, eval_query (Union qs2) db)"
proof (induct arbitrary: qpsr db and qpsr db rule: veri_card_veri_union.induct)
  case (1 t1 t2)
  then show ?case
    using veri_table_correct by auto
next
  case (2 q1 s1 q2 s2)
  obtain qpsr where "veri_card q1 q2 = Some qpsr"
    using "2.prems"(4) by fastforce
  obtain env where "eval_qpsr qpsr env = (eval_query q1 db, eval_query q2 db)"
    using "2.hyps" "2.prems"(1,2,3) \<open>veri_card q1 q2 = Some qpsr\<close> wellformed_query.simps(2) by blast
  then show ?case
    by (smt (verit) "2.prems"(2,3,4) \<open>veri_card q1 q2 = Some qpsr\<close> option.sel option.simps(5) veri_card.simps(2) veri_project_correct_query wellformed_query.simps(2) veri_card_cols_length)
next
  case (3 q1 c1 q2 c2)
  obtain qpsr1 where "veri_card q1 q2 = Some qpsr1"
    using "3.prems" by fastforce
  then obtain qpsr2 where "veri_select qpsr1 c1 c2 = Some qpsr2" using "3.prems" by force
  obtain env1 where "eval_qpsr qpsr1 env1 = (eval_query q1 db, eval_query q2 db)"
    using "3.hyps" "3.prems"(1,2,3) \<open>veri_card q1 q2 = Some qpsr1\<close> wellformed_query.simps(3) by blast
  have "\<forall>env. fol_eval (const_pred (cols1 qpsr1)c1) env = fol_eval (const_pred (cols2 qpsr1) c2) env"
    by (smt (verit, ccfv_SIG) \<open>veri_select qpsr1 c1 c2 = Some qpsr2\<close> option.distinct(1) veri_select_def)
  have "\<exists>env. eval_qpsr \<lparr> cols1 = cols1 qpsr1, cols2 = cols2 qpsr1, cond = And (cond qpsr1) (const_pred (cols1 qpsr1) c1) \<rparr> env = (select c1 (eval_query q1 db), select c2 (eval_query q2 db))"
    using "3.prems"(2,3) \<open>\<forall>env. fol_eval (const_pred (cols1 qpsr1) c1) env = fol_eval (const_pred (cols2 qpsr1) c2) env\<close> \<open>eval_qpsr qpsr1 env1 = (eval_query q1 db, eval_query q2 db)\<close> \<open>veri_card q1 q2 = Some qpsr1\<close>
      veri_card_cols_length veri_select_correct by auto
  then show ?case
    by (smt (verit, best) "3.prems"(4) \<open>veri_card q1 q2 = Some qpsr1\<close> eval_query.simps(3) option.distinct(1) option.sel option.simps(5) veri_card.simps(3) veri_select_def)
next
  case (4 qs1 qs2)
  then show ?case by simp
next
  case ("5_1" v va vb)
  then show ?case by simp
next
  case ("5_2" v va vb vc)
  then show ?case by simp
next
  case ("5_3" v va vb)
  then show ?case by simp
next
  case ("5_4" v va vb)
  then show ?case by simp
next
  case ("5_5" v va vb vc)
  then show ?case by simp
next
  case ("5_6" v va vb)
  then show ?case by simp
next
  case ("5_7" v va)
  then show ?case by simp
next
  case ("5_8" v va vb)
  then show ?case by simp
next
  case ("5_9" v va vb)
  then show ?case by simp
next
  case ("5_10" vb v va)
  then show ?case by simp
next
  case ("5_11" vb vc v va)
  then show ?case by simp
next
  case ("5_12" vb v va)
  then show ?case by simp
next
  case ("5_13" vb v va)
  then show ?case by simp
next
  case ("5_14" vb vc v va)
  then show ?case by simp
next
  case ("5_15" vb v va)
  then show ?case by simp
next
  case ("5_16" va v)
  then show ?case by simp
next
  case ("5_17" va vb v)
  then show ?case by simp
next
  case ("5_18" va vb v)
  then show ?case by simp
next
  case 6
  have "\<exists>env. eval_qpsr qpsr env = ({#}, {#})"
    by (metis eval_qpsr_def eval_qpsr_table_empty)
  then show ?case by simp
next
  case (7 x xs y ys)
  obtain qpsr1 where a: "veri_card x y = Some qpsr1"
    using "7.prems"(4) by fastforce
  then have "qpsr_is_eq qpsr1"
    using "7.prems"(4) not_Some_eq by fastforce
  then obtain qpsr2 where "veri_union xs ys = Some qpsr2"
    using "7.prems"(4) a by fastforce
  have "eval_query x db = eval_query y db"
    by (meson "7.hyps"(1) "7.prems"(1,2,3) \<open>qpsr_is_eq qpsr1\<close> a eval_qpsr_eq list.set_intros(1) wellformed_query.simps(4))
  have x: "qpsr = \<lparr> cols1 = init_tuple 0 (query_output_length x), cols2 = init_tuple 0 (query_output_length x), cond = Const 1 \<rparr>"
    by (smt (verit, best) "7.prems"(4) option.case_eq_if option.distinct(1) option.inject veri_union.simps(2))
  have "\<exists>env. eval_qpsr \<lparr> cols1 = init_tuple 0 (query_output_length x), cols2 = init_tuple 0 (query_output_length x), cond = Const 1 \<rparr> env = (eval_query (Union xs) db, eval_query (Union ys) db)" proof (cases "xs")
    case Nil
    have "ys = []"
      by (metis \<open>veri_union xs ys = Some qpsr2\<close> is_none_code(2) is_none_simps(1) local.Nil neq_Nil_conv veri_union.simps(4))
    have "eval_qpsr \<lparr>cols1 = init_tuple 0 (query_output_length x), cols2 = init_tuple 0 (query_output_length x), cond = Const 1\<rparr> {#} = ({#}, {#})"
      using eval_qpsr_def by auto
    then have "\<exists>env. eval_qpsr \<lparr>cols1 = init_tuple 0 (query_output_length x), cols2 = init_tuple 0 (query_output_length x), cond = Const 1\<rparr> env = ({#}, {#})" by metis
    then show ?thesis
      by (simp add: \<open>ys = []\<close> local.Nil)
  next
    case (Cons xx xxs)
    obtain yy yys where "ys = yy#yys"
      by (metis \<open>veri_union xs ys = Some qpsr2\<close> list.exhaust local.Cons option.distinct(1) veri_union.simps(3))
    have "query_output_length x = query_output_length (Union xs)"
      using "7.prems"(2) local.Cons union_output_len by blast
    have "query_output_length y = query_output_length (Union ys)"
      using "7.prems"(3) \<open>ys = yy # yys\<close> union_output_len by blast
    have "query_output_length x = query_output_length y"
      by (metis "7.prems"(2,3) \<open>qpsr_is_eq qpsr1\<close> a list.set_intros(1) qpsr_is_eq_ veri_card_cols_length wellformed_query.simps(4))
    then show ?thesis
      by (smt (verit, del_insts) "7.hyps"(2) "7.prems"(1,2,3) \<open>\<And>thesis. (\<And>qpsr2. veri_union xs ys = Some qpsr2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>qpsr_is_eq qpsr1\<close> \<open>query_output_length x = query_output_length (query.Union xs)\<close>
          \<open>ys = yy # yys\<close> a list.set_intros(2) local.Cons option.case_eq_if option.distinct(1) query_output_length.simps(5) veri_union.simps(2) wellformed_query.simps(4))
  qed
  have z: "\<exists>env. eval_qpsr \<lparr> cols1 = init_tuple 0 (query_output_length x), cols2 = init_tuple 0 (query_output_length x), cond = Const 1 \<rparr> env = (eval_query x db + eval_query (Union xs) db, eval_query x db + eval_query (Union ys) db)"
    by (meson "7.prems"(1,2) \<open>\<exists>env. eval_qpsr \<lparr>cols1 = init_tuple 0 (query_output_length x), cols2 = init_tuple 0 (query_output_length x), cond = Const 1\<rparr> env = (eval_query (query.Union xs) db, eval_query (query.Union ys) db)\<close>
        list.set_intros(1) query_output_length_h veri_union_h wellformed_query.simps(4))
  have "\<exists>env. eval_qpsr qpsr env = (eval_query x db + eval_query (Union xs) db, eval_query x db + eval_query (Union ys) db)"
    using x z by blast
  then show ?case
    by (simp add: \<open>eval_query x db = eval_query y db\<close>)
next
  case ("8_1" v va)
  then show ?case by simp
next
  case ("8_2" v va)
  then show ?case by simp
qed

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