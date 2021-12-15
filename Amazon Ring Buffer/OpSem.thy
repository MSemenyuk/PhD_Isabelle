theory OpSem 
imports Main HOL.Rat 
begin

type_synonym TS = rat (* Event *)
type_synonym T = nat (* Thread ID *)
type_synonym L = nat (*? Ref?*)
definition "null = (0 :: nat)"

type_synonym V = nat

(* bool: release/aquire or relaxed*)
datatype action =
    Read bool L V
  | Write bool L V
  | Update L V V

print_theorems

fun avar :: "action \<Rightarrow> L" where
    "avar (Read _ x v) = x"
  | "avar (Write _ x v) = x"
  | "avar (Update x e v) = x"

fun wr_val :: "action \<Rightarrow> V option" where
    "wr_val (Write _ _ v) =  Some v"
  | "wr_val (Update _ _ v) = Some  v"
  | "wr_val _ = None"

fun rd_val :: "action \<Rightarrow> V option" where
    "rd_val (Read _ _ v) = Some v"
  | "rd_val (Update _ v _) = Some v"
  | "rd_val _ = None"

fun isRA :: "action \<Rightarrow> bool" where
    "isRA (Read b _ _) = b" 
  | "isRA (Write b _ _) = b"
  | "isRA (Update _ _ _) = True"

fun isWr :: "action \<Rightarrow> bool" where
    "isWr (Read _ _ _) = False" 
  | "isWr (Write _ _ _) = True"
  | "isWr (Update _ _ _) = False"

fun isRd :: "action \<Rightarrow> bool" where
    "isRd (Read _ _ _) = True" 
  | "isRd (Write _ _ _) = False"
  | "isRd (Update _ _ _) = False"

fun isUp :: "action \<Rightarrow> bool" where
    "isUp (Read _ _ _) = False" 
  | "isUp (Write _ _ _) = False"
  | "isUp (Update _ _ _) = True"


abbreviation "reads a \<equiv> a \<in> (dom rd_val)"
abbreviation "writes a \<equiv> a \<in> (dom wr_val)"


type_synonym View = "L \<Rightarrow> T"

type_synonym event = "TS \<times> T \<times> action"

abbreviation time_stamp :: "event \<Rightarrow> TS" where "time_stamp e \<equiv> fst e"
abbreviation tid :: "event \<Rightarrow> T" where "tid e \<equiv> fst (snd e)"
abbreviation act :: "event \<Rightarrow> action" where "act e \<equiv> snd (snd e)"

abbreviation var :: "L \<times> TS \<Rightarrow> L" where "var \<equiv> fst"
abbreviation tst :: "L \<times> TS \<Rightarrow> TS" where "tst \<equiv> snd"

(*
lemma [simp]: "var (x, ts) = x" by(simp add: var_def)
lemma [simp]: "tst (x, ts) = ts" by(simp add: tst_def)
*)

record write_record =
  val :: V
  is_releasing :: bool

record surrey_state =
  writes :: "(L \<times> TS) set"
  thrView :: "T \<Rightarrow> L \<Rightarrow> (L \<times> TS)"
  modView :: "(L \<times> TS) \<Rightarrow> L \<Rightarrow> (L \<times> TS)"
  mods :: "(L \<times> TS) \<Rightarrow> write_record"
  write_available :: "(L \<times> TS) \<Rightarrow> bool" \<comment> \<open>rewrite as "covered" instead of write_available\<close>


definition "value \<sigma> w \<equiv>  val (mods \<sigma> w)"
definition "releasing \<sigma> w \<equiv>  is_releasing (mods \<sigma> w)"

definition "writes_on \<sigma> x = {w . var w = x \<and> w \<in> writes \<sigma>}"
definition "visible_writes \<sigma> t x \<equiv> {w \<in> writes_on \<sigma> x . tst(thrView \<sigma> t x) \<le> tst w}" \<comment> \<open>is this observable writes?\<close>
                                             


lemma writes_on_var [simp]: "w \<in> writes_on \<sigma> x \<Longrightarrow> var w = x"
  by (simp add: writes_on_def)

lemma visible_var [simp]: "w \<in> visible_writes \<sigma> t x \<Longrightarrow> var w = x"
  by (auto simp add: visible_writes_def)

lemma visible_writes_in_writes: "visible_writes \<sigma> t x \<subseteq> writes \<sigma>"
  using visible_writes_def writes_on_def by fastforce

definition "valid_fresh_ts \<sigma> w ts' \<equiv> tst w < ts' \<and> (\<forall> w' \<in> writes_on \<sigma> (var w). tst w < tst w' \<longrightarrow> ts' < tst w')"

definition "ts_oride m m' x \<equiv> if tst (m x) \<le> tst (m' x) then m' x else m x"

definition rev_app :: "'s \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> 't" (infixl ";;" 150)
  where
  "rev_app s f \<equiv> f s"


definition 
  "update_thrView t nv \<sigma> \<equiv> \<sigma> \<lparr> thrView := (thrView \<sigma>)(t := nv)\<rparr>"

definition 
  "update_modView w nv \<sigma> \<equiv> \<sigma> \<lparr> modView := (modView \<sigma>)(w := nv) \<rparr>"

definition 
  "update_mods w nwr \<sigma> \<equiv> \<sigma> \<lparr> mods := (mods \<sigma>)(w := nwr)\<rparr> \<lparr>writes := writes \<sigma> \<union> {w}\<rparr>"

definition 
  "update_wa w b \<sigma> \<equiv> \<sigma> \<lparr> write_available := (write_available \<sigma>)(w := b)\<rparr>"

definition "syncing \<sigma> w b \<equiv> releasing \<sigma> w \<and> b"

lemma [simp]: "syncing \<sigma> w False = False"
  by (simp add: syncing_def)

lemma [simp]: "syncing \<sigma> w True = releasing \<sigma> w"
  by (simp add: syncing_def)

definition
  "read_trans t b w \<sigma>  \<equiv>
       let new_thr_idx = (thrView \<sigma> t)(var w := w) in
       let new_thr_idx' = 
             if syncing \<sigma> w b then ts_oride new_thr_idx (modView \<sigma> w) else new_thr_idx in
          \<sigma> ;; update_thrView t new_thr_idx'"

lemma [simp]: "\<not> syncing \<sigma> w b \<Longrightarrow> thrView (read_trans t b w \<sigma>) t = (thrView \<sigma> t)(var w := w)"
  by (simp add: read_trans_def rev_app_def update_thrView_def)

lemma syncing_thrView_read_trans [simp]: "syncing \<sigma> w b \<Longrightarrow>
                     thrView (read_trans t b w \<sigma>) t = ts_oride ((thrView \<sigma> t)(var w := w)) (modView \<sigma> w)"
  by (simp add: read_trans_def rev_app_def update_thrView_def)


lemma [simp]: "t' \<noteq> t \<Longrightarrow> thrView (read_trans t b w \<sigma>) t' = (thrView \<sigma> t')"
  apply (simp add: read_trans_def rev_app_def update_thrView_def)
  by (metis fun_upd_other surrey_state.select_convs(2) surrey_state.surjective surrey_state.update_convs(2))

lemma [simp]: "var w \<noteq> x \<Longrightarrow> b = False \<Longrightarrow> thrView (read_trans t b w \<sigma>) t x = thrView \<sigma> t x"
  by (simp add: read_trans_def rev_app_def update_thrView_def Let_def ts_oride_def)

lemma [simp]: "modView (read_trans t b w \<sigma>) = modView \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "mods (read_trans t b w \<sigma>) = mods \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
                                                            
lemma [simp]: "write_available (read_trans t b w \<sigma>) = write_available \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "writes (read_trans t b w \<sigma>) = writes \<sigma>"
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "writes_on (read_trans t b w \<sigma>) x = writes_on \<sigma> x"
  apply(unfold writes_on_def)
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)


lemma [simp]: "value (read_trans t False w \<sigma>) x  = value \<sigma> x"
  apply(unfold value_def)
  by(simp add: read_trans_def Let_def rev_app_def update_thrView_def)


definition
  "write_trans t b w v \<sigma> ts' \<equiv>
          \<sigma> ;; update_thrView t ((thrView \<sigma> t)(var w := (var w, ts'))) 
            ;; update_modView (var w, ts') ((thrView \<sigma> t)(var w := (var w, ts')))
            ;; update_mods (var w, ts') \<lparr> val = v, is_releasing = b\<rparr> 
            ;; update_wa (var w, ts') True"


lemma [simp]: "thrView (write_trans t b w v \<sigma> ts') t = (thrView \<sigma> t)(var w := (var w, ts'))"
  by (simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "t' \<noteq> t \<Longrightarrow> thrView (write_trans t b w v \<sigma> ts') t' = (thrView \<sigma> t')"
  by (simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' = (thrView \<sigma> t)(var w := (var w, ts'))"
  apply (simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' y = modView \<sigma> w' y"
  by (auto simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> modView (write_trans t b w v \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow> mods (write_trans t b w v \<sigma> ts') w' = \<lparr> val = v, is_releasing = b\<rparr>"
  apply (simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> mods (write_trans t b w v \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> mods (write_trans t b w v \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow> write_available (write_trans t b w v \<sigma> ts') w' = True"
  apply (simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow>
                write_available (write_trans t b w v \<sigma> ts') w' = write_available \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> write_available (write_trans t b w v \<sigma> ts') w' = write_available \<sigma> w'"
  by (auto simp add: write_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma writes_new_w [simp]: "writes (write_trans t b w v \<sigma> ts') = writes \<sigma> \<union> {(var w, ts')}"
  by(simp add: Let_def rev_app_def
                   write_trans_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "x = var w \<Longrightarrow> writes_on (write_trans t b w v \<sigma> ts') x = writes_on \<sigma> x \<union> {(var w, ts')}"
  apply(unfold writes_on_def)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  using Collect_cong by auto

lemma [simp]: "y \<noteq> var w \<Longrightarrow> writes_on (write_trans t b w v \<sigma> ts') y = writes_on \<sigma> y"
  apply(unfold writes_on_def)
  by(auto simp add: read_trans_def Let_def rev_app_def update_thrView_def)

lemma [simp]: "w \<in> writes_on \<sigma> y \<Longrightarrow>  w \<in> writes_on (write_trans t b w' v \<sigma> ts') y"
  apply(unfold writes_on_def)
  by simp




definition "update_trans t w v' \<sigma> ts' \<equiv> 
       let new_thr_idx = (thrView \<sigma> t)(var w := (var w, ts')) in
         let new_thr_idx' =
             if releasing \<sigma> w
             then
                 ts_oride new_thr_idx (modView \<sigma> w) 
             else
                 new_thr_idx 
             in
                 \<sigma> ;; update_thrView t new_thr_idx' 
                   ;; update_modView (var w, ts') new_thr_idx' \<comment> \<open>TODO: check this prime on new_thr_idx\<close> 
                   ;; update_mods (var w, ts') \<lparr> val = v', is_releasing = True\<rparr>
                   ;; update_wa (var w, ts') True
                   ;; update_wa w False"


lemma [simp]: "\<not> releasing \<sigma> w \<Longrightarrow>
                     thrView (update_trans  t w v' \<sigma> ts') t = (thrView \<sigma> t)(var w := (var w, ts'))"
  by (simp add: Let_def rev_app_def update_modView_def update_mods_def update_thrView_def update_trans_def update_wa_def)

lemma [simp]: " releasing \<sigma> w \<Longrightarrow> 
                  thrView (update_trans  t w v' \<sigma> ts') t = ts_oride ((thrView \<sigma> t)(var w := (var w, ts'))) (modView \<sigma> w)"
  by (auto simp add: Let_def update_trans_def update_wa_def rev_app_def update_modView_def update_mods_def update_thrView_def)

lemma [simp]: "t' \<noteq> t \<Longrightarrow> thrView (update_trans  t w v' \<sigma> ts') t' = (thrView \<sigma> t')"
  by (simp add: Let_def update_trans_def update_wa_def rev_app_def update_modView_def update_mods_def update_thrView_def)


lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow>
             \<not> releasing \<sigma> w \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = (thrView \<sigma> t)(var w := (var w, ts'))"
  apply (simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow>
             releasing \<sigma> w \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = ts_oride ((thrView \<sigma> t)(var w := (var w, ts'))) (modView \<sigma> w)"
  apply (simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: Let_def fun_upd_idem_iff fun_upd_twist rev_app_def update_modView_def update_mods_def update_thrView_def update_trans_def update_wa_def)
  
lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> modView (update_trans t w v' \<sigma> ts') w' = modView \<sigma> w'"
  by (auto simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> mods (update_trans t w v' \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<Longrightarrow> mods (update_trans t w v' \<sigma> ts') w' = mods \<sigma> w'"
  by (auto simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow>
             mods (update_trans t w v' \<sigma> ts') w' = \<lparr> val = v', is_releasing = True\<rparr>"
  apply (simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse)

lemma [simp]: "var w' = var w \<Longrightarrow> tst w' = ts' \<Longrightarrow> 
       tst w \<noteq> ts' \<Longrightarrow> write_available (update_trans t w v' \<sigma> ts') w'"
  apply (auto simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)
  by (metis prod.collapse)

lemma [simp]: "var w' \<noteq> var w \<Longrightarrow> write_available (update_trans t w v' \<sigma> ts') w' = write_available \<sigma> w'"
  by (auto simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "\<not> write_available (update_trans t w v' \<sigma> ts') w"
  by (simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "tst w' \<noteq> ts' \<and> tst w' \<noteq> tst w \<Longrightarrow> write_available (update_trans t w v' \<sigma> ts') w' = write_available \<sigma> w'"
 by (auto simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "writes (update_trans t w v' \<sigma> ts') = writes \<sigma> \<union> {(var w, ts')}"
 by (auto simp add: Let_def update_trans_def rev_app_def update_wa_def update_thrView_def
                   update_modView_def update_mods_def)

lemma [simp]: "x = var w \<Longrightarrow> writes_on (update_trans t w v' \<sigma> ts') x = writes_on \<sigma> x \<union> {(x, ts')}"
  apply(unfold writes_on_def)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  using Collect_cong by auto

lemma [simp]: "y \<noteq> var w \<Longrightarrow> writes_on (update_trans t w v' \<sigma> ts') y = writes_on \<sigma> y"
  apply(unfold writes_on_def)
  by(auto simp add: read_trans_def Let_def rev_app_def update_thrView_def)


definition step :: "T \<Rightarrow> action \<Rightarrow> surrey_state \<Rightarrow> surrey_state \<Rightarrow> bool"
  where
    "step t a \<sigma> \<sigma>'\<equiv>
       \<exists> w. w \<in> visible_writes \<sigma> t (avar a) \<and>
       (case a of
         Read b x v \<Rightarrow>
           v = value \<sigma> w \<and>
           \<sigma>' = read_trans t b w \<sigma>
       | Write b x v \<Rightarrow> \<exists> ts'.
           write_available \<sigma> w \<and> \<comment> \<open> TODO: use sets and predicates consistently \<close>
           valid_fresh_ts \<sigma> w ts' \<and>
           \<sigma>' = write_trans t b w v \<sigma> ts'
       | Update x v v' \<Rightarrow> \<exists> ts'.
           v = value \<sigma> w \<and> 
           write_available \<sigma> w \<and>
           valid_fresh_ts \<sigma> w ts' \<and>
           \<sigma>' = update_trans t w v' \<sigma> ts')
           "

lemma step_cases:
       "step t a \<sigma> \<sigma>'
          \<Longrightarrow> 
        \<lbrakk>\<And> w b x v. \<sigma>' = read_trans t b w \<sigma> \<and> a = Read b x v \<and> w \<in> visible_writes \<sigma> t (avar a) \<and>
          v = value \<sigma> w \<Longrightarrow> P \<sigma> (read_trans t b w \<sigma>)\<rbrakk>
         \<Longrightarrow>
       \<lbrakk>\<And> w b x v ts'. \<sigma>' = write_trans t b w v \<sigma> ts' \<and> a = Write b x v \<and> w \<in> visible_writes \<sigma> t (avar a) \<and>
           write_available \<sigma> w \<and>
           valid_fresh_ts \<sigma> w ts'
           \<Longrightarrow> P \<sigma> (write_trans t b w v \<sigma> ts') \<rbrakk>
         \<Longrightarrow>
       \<lbrakk>\<And> w x v v' ts'. \<sigma>' = update_trans t w v' \<sigma> ts' \<and> a = Update x v v' \<and>
           w \<in> visible_writes \<sigma> t (avar a) \<and>
           v = value \<sigma> w \<and>
           write_available \<sigma> w \<and>
           valid_fresh_ts \<sigma> w ts'
           \<Longrightarrow> P \<sigma> (update_trans t w v' \<sigma> ts')\<rbrakk>
  \<Longrightarrow> P \<sigma> \<sigma>'"
  apply(simp add: step_def) apply(case_tac a) by auto



definition "WrX x v \<equiv> Write False x v"
definition "WrR x v \<equiv> Write True x v"
definition "RdX x v \<equiv> Read False x v"
definition "RdA x v \<equiv> Read True x v"



abbreviation WrX_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ [_ := _]\<^sub>_ _" [100,100,100,100,100])
  where "\<sigma> [x := v]\<^sub>t \<sigma>' \<equiv> step t (WrX x v) \<sigma> \<sigma>'"

abbreviation WrR_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ [_ :=\<^sup>R _]\<^sub>_ _" [100,100,100,100,100])
  where "\<sigma> [x :=\<^sup>R v]\<^sub>t \<sigma>' \<equiv> step t (WrR x v) \<sigma> \<sigma>'"

abbreviation RdX_state_abbr:: " surrey_state \<Rightarrow> V \<Rightarrow> L \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ [_ \<leftarrow> _]\<^sub>_ _" [100,100,100,100,100])
  where "\<sigma> [r \<leftarrow> x]\<^sub>t \<sigma>' \<equiv> step t (RdX x r) \<sigma> \<sigma>'"

abbreviation RdA_state_abbr:: " surrey_state \<Rightarrow> V \<Rightarrow> L \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ [_ \<leftarrow>\<^sup>A _]\<^sub>_ _" [100,100,100,100,100])
  where "\<sigma> [r \<leftarrow>\<^sup>A x]\<^sub>t \<sigma>' \<equiv> step t (RdA x r) \<sigma> \<sigma>'"

abbreviation Up_state_abbr:: " surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ RMW[_, _, _]\<^sub>_ _" [100,100,100,100,100,100])
  where "\<sigma> RMW[x, u, v]\<^sub>t \<sigma>' \<equiv> step t (Update x u v) \<sigma> \<sigma>'"




definition "initial_state \<sigma> I \<equiv>
                 \<exists> F . writes \<sigma> = (\<lambda>x. (x, F x)) ` UNIV \<and>
                       (\<forall> t x. thrView \<sigma> t x = (x, F x)) \<and>
                       (\<forall> w x. modView \<sigma> w x = (x, F x)) \<and>
                       (\<forall> w. mods \<sigma> w = \<lparr> val = I (var w), is_releasing = False \<rparr>) \<and>
                       (\<forall> w. write_available \<sigma> w = True)"

(*
definition "initial_state \<sigma> I \<equiv>
                 \<exists> F . writes \<sigma> = {(x, F x) | x. True} \<and>
                       (\<forall> t x. thrView \<sigma> t x = (x, F x)) \<and>
                       (\<forall> w x. modView \<sigma> w x = (x, F x)) \<and>
                       (\<forall> w. mods \<sigma> w = \<lparr> val = I (var w), is_releasing = False \<rparr>) \<and>
                       (\<forall> w. write_available \<sigma> w = True)"
*)

definition  "lastWr \<sigma> x \<equiv> (x, Max (tst`(writes_on \<sigma> x)))" 


definition
  "wfs \<sigma> \<equiv>
      (\<forall> t x. thrView \<sigma> t x \<in> writes_on \<sigma> x) \<and>
      (\<forall> w x. modView \<sigma> w x \<in> writes_on \<sigma> x) \<and>
      (\<forall> x. finite(writes_on \<sigma> x)) \<and>
      (\<forall> w. w \<in> writes \<sigma> \<longrightarrow> modView \<sigma> w (var w) = w) \<and>
      (\<forall> w x. w = lastWr \<sigma> x \<longrightarrow> write_available \<sigma> w )"

lemma initially_write_unique: 
  "initial_state \<sigma> I \<Longrightarrow> w \<in> writes_on \<sigma> x \<Longrightarrow> w' \<in> writes_on \<sigma> x \<Longrightarrow> w = w'"
  apply(unfold initial_state_def writes_on_def) by auto

  lemma finite_single_fst_eq: \<open>finite {w. fst w = x \<and> (\<exists>x. w = (x, F
    x))}\<close> (is \<open>finite ?A\<close>) proof - have \<open>?A \<subseteq> {(x, F x)}\<close> by auto from
    finite_subset[OF this] show ?thesis by auto qed

  lemma in_writes_onI: \<open>var w = x \<Longrightarrow> w \<in> writes \<sigma> \<Longrightarrow> w \<in> writes_on \<sigma> x\<close>
    unfolding writes_on_def by auto

(*
  lemma initial_wfs: assumes "initial_state \<sigma> I" shows "wfs \<sigma>" using
    assms initially_write_unique[OF assms(1)]  
    
    apply (auto simp add: wfs_def
     initial_state_def lastWr_def 
     intro: in_writes_onI)

    sledgehammer
*)
  
(* TODO: do something about SMTs *)
lemma initial_wfs: 
  assumes "initial_state \<sigma> I"  
  shows "wfs \<sigma>"
  apply(simp add: initial_state_def wfs_def)
  apply(rule conjI) apply (unfold writes_on_def, clarify) 
  apply (metis (mono_tags) UNIV_I assms fst_conv image_eqI initial_state_def) 
  apply(rule conjI)
  using assms apply (simp add: initial_state_def) 
   apply auto[1] 
  apply rule using initially_write_unique[OF assms] 
  apply (smt Collect_cong empty_iff finite.intros(1) finite.intros(2) insert_compr mem_Collect_eq not_finite_existsD writes_on_def) 
  using assms apply safe
  apply (simp add: initial_state_def) apply auto[1]
  using initial_state_def by blast 



lemma allI_case: "\<lbrakk>\<And> y. x \<noteq> y \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> \<lbrakk>P x\<rbrakk> \<Longrightarrow> \<forall> y. P y" by fastforce


lemma [simp]: "wfs \<sigma> \<Longrightarrow> writes_on \<sigma> x \<noteq> {}"
  apply(simp add: wfs_def)
  by (metis empty_iff)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> finite(writes_on \<sigma> x)"
  by(simp add: wfs_def)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> thrView \<sigma> t x \<in> writes_on \<sigma> x"
  by(simp add: wfs_def)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> modView \<sigma> w x \<in> writes_on \<sigma> x"
  using wfs_def by blast


lemma [simp]: "wfs \<sigma> \<Longrightarrow> modView (read_trans t b w \<sigma>) w x \<in> writes_on (read_trans t b w \<sigma>) x"
  by auto

lemma [simp]: "wfs \<sigma> \<Longrightarrow> writes_on \<sigma> x =  writes_on (read_trans t b w \<sigma>) x"
  by auto


lemma own_ModView:
  assumes "wfs \<sigma>"
      and "w \<in> writes \<sigma>"
    shows "modView \<sigma> w (var w) = w"
  using assms apply(unfold wfs_def)
  by blast

lemma ts_oride_same_var:
  assumes "wfs \<sigma>"
      and "x = var w"
      and "w \<in> visible_writes \<sigma> t (var w)"
    shows "ts_oride ((thrView \<sigma> t)(var w := w)) (modView \<sigma> w) x = w"
  apply(simp add: ts_oride_def) apply safe using assms
  apply (meson own_ModView subsetCE visible_writes_in_writes)
  using assms(2) apply blast 
  using assms(2) by blast

lemma ts_oride_diff_var:
  assumes "wfs \<sigma>"
      and "x \<noteq> var w"
      and "w \<in> visible_writes \<sigma> t (var w)"
    shows "ts_oride ((thrView \<sigma> t)(var w := w')) (modView \<sigma> w) x = ts_oride (thrView \<sigma> t) (modView \<sigma> w) x"
  apply(simp add: ts_oride_def)
  using assms(2) by blast

lemma ts_oride_split:
  assumes "tst (m' x) \<le> tst (m x) \<Longrightarrow> P (m x)"
      and "tst (m x) \<le> tst (m' x) \<Longrightarrow> P (m' x)"
    shows "P (ts_oride m m' x)"
  apply(simp add: ts_oride_def)
  by (simp add: assms(1) assms(2))

lemma wr_other_pres_last: "wfs \<sigma> \<Longrightarrow> x \<noteq> xa \<Longrightarrow> lastWr (write_trans t ba (x, b) v \<sigma> ts') xa = lastWr \<sigma> xa"
  by(simp add: lastWr_def)

lemma upd_other_pres_last: "wfs \<sigma> \<Longrightarrow> x \<noteq> xa \<Longrightarrow> lastWr (update_trans t (x, b) v \<sigma> ts') xa = lastWr \<sigma> xa"
  by(simp add: lastWr_def)

lemma last_w_not_last: "wfs \<sigma> \<Longrightarrow> (xa, b) \<in> visible_writes \<sigma> t xa \<Longrightarrow> valid_fresh_ts \<sigma> (xa,b) ts'  \<Longrightarrow> b \<noteq> Max (tst ` writes_on \<sigma> xa) \<Longrightarrow> lastWr (write_trans t ba (xa, b) v \<sigma> ts') xa =  lastWr  \<sigma> xa "
  apply(simp add: visible_writes_def valid_fresh_ts_def)
  apply(elim conjE)
  apply(subgoal_tac "b <  Max (tst ` writes_on \<sigma> xa)")
   defer
  apply(unfold wfs_def , clarsimp)
   apply (metis Max_ge finite_imageI image_eqI le_neq_trans snd_conv)
  apply(subgoal_tac "tst (lastWr \<sigma> xa) = Max (tst ` writes_on \<sigma> xa)")
   defer
   apply (simp add: lastWr_def)
  apply (simp add: lastWr_def)
  apply(subgoal_tac "ts' <  Max (tst ` writes_on \<sigma> xa)")
   defer
   apply simp
  apply (metis (mono_tags, lifting) Max_in empty_iff finite_imageI image_iff) 
  by (smt Max_ge Max_in empty_iff finite_imageI finite_insert image_is_empty insert_iff le_neq_trans less_imp_not_less) 



lemma last_w_not_last_upd: "wfs \<sigma> \<Longrightarrow> (xa, b) \<in> visible_writes \<sigma> t xa \<Longrightarrow> valid_fresh_ts \<sigma> (xa,b) ts'  \<Longrightarrow> b \<noteq> Max (tst ` writes_on \<sigma> xa) \<Longrightarrow> lastWr (update_trans t (xa, b) v \<sigma> ts') xa =  lastWr  \<sigma> xa "
  apply(simp add: visible_writes_def valid_fresh_ts_def)
  apply(elim conjE)
  apply(subgoal_tac "b <  Max (tst ` writes_on \<sigma> xa)")
   defer
  apply(unfold wfs_def, clarsimp)
   apply (metis Max_ge finite_imageI image_eqI le_neq_trans snd_conv)
  apply(subgoal_tac "tst (lastWr \<sigma> xa) = Max (tst ` writes_on \<sigma> xa)")
  apply (simp add: lastWr_def)
  apply(subgoal_tac "ts' <  Max (tst ` writes_on \<sigma> xa)")
   apply (smt Max_ge Max_in dual_order.antisym empty_iff finite_imageI finite_insert image_is_empty insert_iff leD)
  apply (metis (mono_tags, lifting) Max_in empty_iff finite_imageI image_iff)
  by (simp add: lastWr_def)

lemma lastWr_w: "wfs \<sigma> \<Longrightarrow> (xa, Max (tst ` writes_on \<sigma> xa)) \<in> visible_writes \<sigma> t xa \<Longrightarrow> valid_fresh_ts \<sigma> ((xa, Max (tst ` writes_on \<sigma> xa))) ts' \<Longrightarrow>
    lastWr (write_trans t ba ((xa, Max (tst ` writes_on \<sigma> xa)))  v \<sigma> ts') xa = (xa, ts')"
  apply(unfold wfs_def)
  apply clarsimp
  apply(simp add: valid_fresh_ts_def)
  apply(elim conjE)
  apply(simp add: lastWr_def)
  by (meson Max_ge Max_insert2 dual_order.strict_implies_order dual_order.trans finite_imageI)


lemma lastWr_upd: "wfs \<sigma> \<Longrightarrow> (xa, Max (tst ` writes_on \<sigma> xa)) \<in> visible_writes \<sigma> t xa \<Longrightarrow> valid_fresh_ts \<sigma> ((xa, Max (tst ` writes_on \<sigma> xa))) ts' \<Longrightarrow>
    lastWr (update_trans t ((xa, Max (tst ` writes_on \<sigma> xa)))  v \<sigma> ts') xa = (xa, ts')"
  apply(unfold wfs_def)
  apply clarsimp
  apply(simp add: valid_fresh_ts_def)
  apply(elim conjE)
  apply(simp add: lastWr_def)
  by (meson Max_ge Max_insert2 dual_order.strict_implies_order dual_order.trans finite_imageI)

(*
lemmas lastWrdefs [simp] = lastWr_def 

lemma finite_writes: 
  assumes "aa \<noteq> xa" 
    and "finite{w. var w = xa \<and> w \<in> surrey_state.writes \<sigma>}" 
  shows
    "finite{w. var w = xa \<and>
              w \<in> surrey_state.writes (write_trans t ba (aa, b) v \<sigma> ts')}"
 using assms apply auto 
  by (smt Collect_cong fst_conv) 

lemma wfs_preserved:
  assumes "wfs \<sigma>"
      and "step t a \<sigma> \<sigma>'"
    shows "wfs \<sigma>'"
  using assms(1) apply(unfold wfs_def)
  apply (rule step_cases[OF assms(2)]) 
  apply safe apply clarsimp
  unfolding writes_on_def apply (simp add: read_trans_def rev_app_def Let_def)
  apply (intro conjI impI)
  apply (simp add: ts_oride_def update_thrView_def)
  apply (simp add: ts_oride_def update_thrView_def)
  apply clarsimp 
  apply (meson in_mono visible_writes_in_writes)
  apply (simp add: ts_oride_def update_thrView_def)
  apply (simp add: ts_oride_def update_thrView_def)
  apply (meson in_mono visible_writes_in_writes)
  apply auto[4]
  unfolding writes_on_def apply (simp add: update_modView_def update_thrView_def update_wa_def update_mods_def write_trans_def rev_app_def Let_def)
  unfolding writes_on_def apply (simp add: update_modView_def update_thrView_def update_wa_def update_mods_def write_trans_def rev_app_def Let_def)
  unfolding writes_on_def apply (simp add: visible_writes_def valid_fresh_ts_def update_modView_def update_thrView_def update_wa_def update_mods_def write_trans_def rev_app_def Let_def)
         apply(case_tac "xa = aa") 
          prefer 2 apply (erule_tac x = "xa" in allE)+ apply auto [1] using finite_writes 
  apply (smt Collect_cong fst_conv) 
  apply (unfold writes_on_def) apply auto [1] 
  sledgehammer
  sorry
*)

lemma wfs_preserved:
  assumes "wfs \<sigma>"
      and "step t a \<sigma> \<sigma>'"
    shows "wfs \<sigma>'"
  apply(unfold wfs_def)
  apply rule defer apply rule defer apply rule defer defer
    apply clarsimp defer
    apply clarsimp
     apply (rule step_cases[OF assms(2)]) apply simp_all
  using assms(1) wfs_def apply auto[1]
  apply(case_tac "var w = aa")
       apply(case_tac "(aa, b) = (x, ts')") apply simp
  apply simp 
       apply(case_tac "b = ts'") apply simp using assms(1) wfs_def apply blast
   apply simp apply(case_tac "var w = x") apply simp
  using assms(1) wfs_def apply blast  apply simp
  using assms(1) wfs_def apply blast
   apply simp apply(case_tac "var w = x") apply simp 
  using assms(1) wfs_def apply blast apply simp
  using assms(1) wfs_def apply blast
     apply(case_tac "var w = aa") (*********)
  apply(case_tac "releasing \<sigma> w")
      apply(case_tac "(aa, b) = (x, ts')")
        apply simp apply (metis assms(1) fun_upd_same ts_oride_def wfs_def)
       apply(case_tac "b = ts'") apply(case_tac "var w = x") apply simp
        apply simp apply(rule ts_oride_split) using assms(1) apply simp
          using assms(1) apply simp
          apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
               apply simp using assms(1) wfs_def apply blast
              apply(case_tac "(aa, b) = (x, ts')") apply simp
          apply simp apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
          apply(case_tac "b = ts'")apply simp using assms(1) wfs_def apply blast
         apply simp using assms(1) wfs_def apply blast
          apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
             apply simp using assms(1) wfs_def apply blast
          apply clarsimp apply (rule step_cases[OF assms(2)]) apply simp_all
          using assms(1) wfs_def apply blast
             apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
             apply simp using assms(1) wfs_def apply blast
             apply(case_tac "var w = x") apply simp using assms(1) wfs_def apply blast
            apply simp using assms(1) wfs_def apply blast
           defer
          apply (rule step_cases[OF assms(2)])
            apply(case_tac "ta = t") apply(case_tac "syncing \<sigma> w b")
               apply simp apply(rule ts_oride_split) 
          apply (metis assms(1) fun_upd_apply subsetCE visible_writes_in_writes wfs_def)
  using assms(1) wfs_def apply blast apply simp 
     apply (metis assms(1) subsetCE visible_writes_in_writes wfs_def)
    apply simp using assms(1) wfs_def apply blast
            apply(case_tac "ta = t") apply simp
  using assms(1) wfs_def apply blast
  apply simp apply(case_tac "var w = x") apply simp
  using assms(1) wfs_def apply blast
   apply simp using assms(1) wfs_def apply blast
  apply(case_tac "ta = t") apply simp apply(case_tac "releasing \<sigma> w") apply simp
  apply(case_tac "var w = x") apply simp 
     apply (metis assms(1) fun_upd_same ts_oride_def wfs_def)
  apply simp apply(rule ts_oride_split)
  using assms(1) apply auto[1] 
  using assms(1) wfs_def apply blast
  apply simp  
  using assms(1) wfs_def apply blast
  apply simp apply(case_tac "var w = x") apply simp
  using assms(1) wfs_def apply blast apply simp
  using assms(1) wfs_def apply blast
           apply (rule step_cases[OF assms(2)]) apply simp
          using assms(1)
             apply(unfold wfs_def read_trans_def)
          apply(simp add: rev_app_def Let_def syncing_def)
             apply(simp add: update_wa_def update_mods_def update_modView_def update_thrView_def ts_oride_def)
          apply(simp add: lastWr_def)
             apply(unfold writes_on_def, simp)
            apply(elim conjE)
            apply(intro conjI)
             apply(intro allI impI)
          apply simp
          apply (smt fun_upd_def rev_app_def surrey_state.select_convs(3) surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) update_modView_def update_mods_def update_thrView_def update_wa_def visible_var write_trans_def)
          (**)  apply(intro allI impI)
          apply clarsimp
             apply(case_tac "aa \<noteq> x")
          apply(unfold  visible_writes_def writes_on_def)
             apply simp
            apply clarsimp
            apply(case_tac "x \<noteq> xa")
          using assms(1)
             apply(simp add: wr_other_pres_last lastWr_def)
            apply simp
            apply(case_tac "b \<noteq>  Max (tst ` writes_on \<sigma> xa)")
          using assms(1) 
             apply simp
          apply(subgoal_tac "(xa, b) \<in> visible_writes \<sigma> t xa")
              apply (simp add: last_w_not_last)
              apply(simp add: write_trans_def rev_app_def)
          apply (simp add:  update_modView_def update_mods_def update_thrView_def update_wa_def)
          apply(simp add: visible_writes_def)

          apply (metis wfs_def)
            apply simp    
          apply(subgoal_tac "lastWr (write_trans t ba (xa, Max (tst ` writes_on \<sigma> xa)) v \<sigma> ts') xa = (xa, ts')")
             apply simp   
          using assms(1)
          apply(unfold wfs_def)
          apply clarsimp
          apply(simp add: valid_fresh_ts_def)
          apply(elim conjE)
          apply(simp add: lastWr_def)
            apply (meson Max_ge Max_insert2 dual_order.strict_implies_order dual_order.trans finite_imageI)

           apply(elim conjE)
            apply(intro conjI)
             apply(intro allI impI)
          apply simp
            apply (simp add:  rev_app_def Let_def  update_modView_def update_mods_def update_thrView_def update_wa_def  update_trans_def)
            apply(intro conjI impI)
          apply(simp add: ts_oride_def)
          apply (metis assms(1) less_le_not_le own_ModView valid_fresh_ts_def)
                    apply blast
          apply blast
             apply(intro allI impI)
           apply clarsimp
           apply(case_tac "aa \<noteq> xa")
          
          using assms(1)  
            apply simp
            apply(simp add:  upd_other_pres_last lastWr_def)
           apply clarsimp
            apply(case_tac "b \<noteq>  Max (tst ` writes_on \<sigma> xa)")
          using assms(1) 
             apply simp
          apply(subgoal_tac "(xa, b) \<in> visible_writes \<sigma> t xa")
              apply (simp add: last_w_not_last_upd)
              apply(simp add: update_trans_def rev_app_def)
          apply (simp add:  update_modView_def update_mods_def update_thrView_def update_wa_def Let_def)
          apply(simp add: visible_writes_def)
          
          apply (simp add: lastWr_def)

            apply (simp add: lastWr_def visible_writes_def)
          apply clarsimp
          apply (metis wfs_def)
          using assms(1)
          apply(unfold wfs_def)
          apply clarsimp
          apply(simp add: valid_fresh_ts_def)
          apply(elim conjE)
            apply(simp add: lastWr_def)
            apply (elim conjE)
            apply clarsimp
              apply(simp add: update_trans_def rev_app_def)
          apply (simp add:  update_modView_def update_mods_def update_thrView_def update_wa_def Let_def)
          apply(intro impI conjI)
          
          apply (metis (no_types, lifting) Max.coboundedI finite.insertI finite_imageI insertI1 sup.absorb2 sup.strict_order_iff)
          using assms(1)
           by simp      

  


lemma [simp]: "var(lastWr \<sigma> x) = x" by(simp add: lastWr_def)

lemma last_write_max: "wfs \<sigma> \<Longrightarrow> w \<in> writes_on \<sigma> x \<Longrightarrow> tst w \<le> tst (lastWr \<sigma> x)"
  by(simp add: lastWr_def)

lemma last_write_write_on [simp]: "wfs \<sigma> \<Longrightarrow>  lastWr \<sigma> x \<in> writes_on \<sigma> x"
  apply(simp add: lastWr_def )
  apply(case_tac "Max (tst`(writes_on \<sigma> x)) \<in> tst`(writes_on \<sigma> x)")
   defer apply simp
  using writes_on_var by fastforce

lemma lastWr_visible:
    "wfs \<sigma> \<Longrightarrow> lastWr \<sigma> x \<in> visible_writes \<sigma> t x"
  by (metis (no_types, lifting) CollectI last_write_max last_write_write_on visible_writes_def wfs_def)

lemma lastWr_read_pres: "lastWr (read_trans t b w \<sigma>) x = lastWr \<sigma> x"
  by(simp add: lastWr_def)

lemma write_to_different_var [simp]: "wfs \<sigma> \<Longrightarrow> var w \<noteq> x \<Longrightarrow> lastWr (write_trans t b w v \<sigma> ts') x = lastWr \<sigma> x"
  by(simp add: lastWr_def)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> w = (lastWr \<sigma> x) \<Longrightarrow> valid_fresh_ts \<sigma> w ts' \<Longrightarrow>
                    lastWr (write_trans t b w v \<sigma> ts') x = (x, ts')"
  apply (simp add: valid_fresh_ts_def)
  by (simp add: lastWr_def max.strict_order_iff)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> w \<noteq> lastWr \<sigma> x \<Longrightarrow> w \<in> writes_on \<sigma> x \<Longrightarrow> valid_fresh_ts \<sigma> w ts' \<Longrightarrow>
                    lastWr (write_trans t b w v \<sigma> ts') x = lastWr \<sigma> x"
  apply (subst lastWr_def) apply(case_tac "var w = x") apply simp_all defer
   apply (simp add: lastWr_def)
 apply (simp add: valid_fresh_ts_def)
  by (metis dual_order.order_iff_strict lastWr_def last_write_max last_write_write_on max.absorb2 prod.exhaust_sel sndI writes_on_var)

lemma [simp]: " wfs \<sigma> \<Longrightarrow> var w \<noteq> x \<Longrightarrow> value (write_trans t b w v \<sigma> ts')(lastWr \<sigma> x) = value \<sigma> (lastWr \<sigma> x)"
 by(simp add: value_def)
  

lemma [simp]: "wfs \<sigma> \<Longrightarrow> w = lastWr \<sigma> x \<Longrightarrow> valid_fresh_ts \<sigma> w ts' \<Longrightarrow>lastWr (update_trans t w v' \<sigma> ts') x = (x, ts')"
  apply (subst lastWr_def) apply simp
  by (simp add: lastWr_def less_eq_rat_def max.absorb1 valid_fresh_ts_def)

lemma [simp]: "wfs \<sigma> \<Longrightarrow> w \<noteq> lastWr \<sigma> x \<Longrightarrow> w \<in> writes_on \<sigma> x \<Longrightarrow> valid_fresh_ts \<sigma> w ts' \<Longrightarrow>
                    lastWr (update_trans t w v' \<sigma> ts') x = lastWr \<sigma> x"
  apply (subst lastWr_def) apply(case_tac "var w = x") apply simp_all
  by (metis lastWr_def last_write_max last_write_write_on less_eq_rat_def max_def prod.collapse snd_conv valid_fresh_ts_def writes_on_var)

lemma modView_lte_last: "wfs \<sigma> \<Longrightarrow> tst(modView \<sigma> w x) \<le> tst(lastWr \<sigma> x)"
  using last_write_max wfs_def by blast

  

definition "p_obs \<sigma> t x u \<equiv> \<exists> w. w \<in> visible_writes \<sigma> t x \<and> u = value \<sigma> w" 

definition "d_obs \<sigma> view x u \<equiv> view x = lastWr \<sigma> x \<and> value \<sigma> (lastWr \<sigma> x) = u"

definition "d_obs_t \<sigma> t x u \<equiv> d_obs \<sigma> (thrView \<sigma> t) x u"

definition "c_obs \<sigma> x u t y v \<equiv> 
              \<forall> w \<in> visible_writes \<sigma> t x. value \<sigma> w = u \<longrightarrow>
                         d_obs \<sigma> (modView \<sigma> w) y v \<and>
                         releasing \<sigma> w"

abbreviation p_obs_abbr:: "nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[_ \<approx>\<^sub>_ _] _" [100, 100, 100, 100])
  where "[x \<approx>\<^sub>t u] \<sigma> \<equiv> p_obs \<sigma> t x u"

abbreviation d_obs_abbr:: "nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> surrey_state \<Rightarrow> bool" ("[_ =\<^sub>_ _] _" [100, 100, 100, 100])
  where "[x =\<^sub>t u] \<sigma> \<equiv> d_obs_t \<sigma> t x u"

abbreviation c_obs_abbr:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> surrey_state \<Rightarrow> bool" ("[_ = _]\<lparr>_ =\<^sub>_ _ \<rparr> _" [100, 100, 100, 100, 100, 100])
  where "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma> \<equiv> c_obs \<sigma> x u t y v"





definition "covered \<sigma> x \<equiv> \<forall> w .  w \<in> writes_on \<sigma> x \<and> write_available \<sigma> w \<longrightarrow> w = lastWr \<sigma> x"

definition "covered_v \<sigma> x v \<equiv> \<forall> w .  w \<in> writes_on \<sigma> x \<and> write_available \<sigma> w \<longrightarrow> w = lastWr \<sigma> x \<and> value \<sigma> w = v"

abbreviation covered_v_abbr:: "L \<Rightarrow> V  \<Rightarrow> surrey_state \<Rightarrow> bool" ("cvd[_, _] _" [100, 100,100])
  where "cvd[x, u] \<sigma> \<equiv> covered_v \<sigma> x u"




definition "mo w w'\<equiv> var(w) = var(w') \<and> tst(w) < tst(w')" 

definition "enc \<sigma> view x u \<equiv> \<exists> w . w \<in> writes_on \<sigma> x \<and> tst(w) \<le> tst(view x) \<and> value \<sigma> w = u"

definition "enc_t \<sigma> t x u \<equiv>  enc \<sigma> (thrView \<sigma> t) x u"

definition "p_vorder \<sigma> u x v \<equiv> \<exists> w w'.  w \<in> writes_on \<sigma> x  \<and>  w' \<in> writes_on \<sigma> x \<and>
                                        value \<sigma> w = u \<and> value \<sigma> w' = v \<and>
                                        mo w w' "

definition "d_vorder \<sigma> u x v \<equiv> (\<forall> w w'.  w \<in> writes_on \<sigma> x  \<and>  w' \<in> writes_on \<sigma> x \<and>
                                        value \<sigma> w = u \<and> value \<sigma> w' = v \<longrightarrow>
                                        mo w w') \<and> p_vorder \<sigma> u x v"

definition "init_val \<sigma> x v \<equiv> 
  \<exists> w . w \<in> writes_on \<sigma> x \<and> 
        (\<forall>w'\<in> writes_on \<sigma> x .  w \<noteq> w' \<longrightarrow>  mo w w') \<and> 
        value \<sigma> w = v"

definition "amo \<sigma> x u \<equiv> \<not> p_vorder \<sigma> u x u"

definition "no_val \<sigma> x i u \<equiv> init_val \<sigma> x i \<and> \<not> p_vorder \<sigma> i x u"

definition "last_val \<sigma> x u i \<equiv> 
                init_val \<sigma> x i \<and> p_vorder \<sigma> i x u 
                \<and> (\<forall> w. w \<noteq> u \<longrightarrow> \<not> p_vorder \<sigma> u x w)"



abbreviation p_vorder_abbr:: "V  \<Rightarrow> L \<Rightarrow> V \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[_ \<leadsto>\<^sub>_ _] _" [100,100,100,100])
  where "[u \<leadsto>\<^sub>x v] \<sigma> \<equiv> p_vorder \<sigma> u x v"

abbreviation d_vorder_abbr:: "V  \<Rightarrow> L \<Rightarrow> V \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[_ \<hookrightarrow>\<^sub>_ _] _" [100,100,100,100])
  where "[u \<hookrightarrow>\<^sub>x v] \<sigma> \<equiv> d_vorder \<sigma> u x v"

abbreviation amo_abbr:: "L \<Rightarrow> V \<Rightarrow>  surrey_state \<Rightarrow> bool" ("[\<one>\<^sub>_ _] _" [100,100,100])
  where "[\<one>\<^sub>x u] \<sigma> \<equiv> amo \<sigma> x u"

abbreviation no_abbr:: "L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> surrey_state \<Rightarrow> bool" ("[\<zero>\<^sub>_ _]\<^sub>_ _" [100,100,100,100])
  where "[\<zero>\<^sub>x u]\<^sub>i \<sigma> \<equiv> no_val \<sigma> x i u"

abbreviation enc_abbr:: "L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("[en _ _]\<^sub>_ _" [100,100,100,100])
  where "[en x u]\<^sub>t \<sigma> \<equiv> enc_t \<sigma> t x u"

abbreviation last_abbr:: "L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool" ("[last _ _ _]\<^sub>_ _" [100, 100,100,100,100])
  where "[last x i u]\<^sub>t \<sigma> \<equiv> last_val \<sigma> x u i"

abbreviation init_abbr:: "L \<Rightarrow> V  \<Rightarrow> surrey_state \<Rightarrow> bool" ("[init _ _] _" [100, 100,100])
  where "[init x v] \<sigma> \<equiv> init_val \<sigma> x v"


lemma d_obs_lastWr_visible: 
  "wfs \<sigma> \<Longrightarrow> [x =\<^sub>t u] \<sigma> \<Longrightarrow> w \<in> visible_writes \<sigma> t x \<Longrightarrow> w = lastWr \<sigma> x"
  apply (simp add: d_obs_def d_obs_t_def lastWr_def visible_writes_def, auto)
  by (metis dual_order.antisym lastWr_def last_write_max last_write_write_on prod.collapse writes_on_var)



lemma d_obs_implies_p_obs: 
  "wfs \<sigma> \<Longrightarrow> [x =\<^sub>t u] \<sigma> \<Longrightarrow> [x \<approx>\<^sub>t u] \<sigma>"
  apply(simp add: d_obs_t_def d_obs_def p_obs_def) using lastWr_visible
  by (metis lastWr_def)


lemma d_obs_p_obs_agree: "wfs \<sigma> \<Longrightarrow> [x =\<^sub>t u] \<sigma> \<Longrightarrow> [x \<approx>\<^sub>t v] \<sigma> \<Longrightarrow> u = v"
  apply(unfold p_obs_def d_obs_t_def d_obs_def visible_writes_def)apply clarsimp
  by (metis eq_snd_iff fst_conv lastWr_def last_write_max leD order.not_eq_order_implies_strict writes_on_var)

lemma not_p_obs_implies_c_obs: "\<not> [x \<approx>\<^sub>t u] \<sigma> \<Longrightarrow> [x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
  by(auto simp add: p_obs_def c_obs_def)

lemma "[x =\<^sub>t n] \<sigma> \<Longrightarrow> [x =\<^sub>t' m] \<sigma> \<Longrightarrow> m = n"
  by (simp add: d_obs_def d_obs_t_def)




end