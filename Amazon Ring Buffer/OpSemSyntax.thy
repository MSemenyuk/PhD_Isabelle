theory OpSemSyntax 
  imports Main OpSem_New "HOL-Hoare_Parallel.OG_Syntax"
begin 



fun WrX :: "surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state " where
"WrX  \<sigma> x a t = (let w = (getVWNC \<sigma> t x) ; ts' = getTS \<sigma> w in  write_trans t False w a \<sigma> ts')"

fun WrR :: "surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state" where
"WrR  \<sigma> x a t = (let w = (getVWNC \<sigma> t x) ; ts' = getTS \<sigma> w in write_trans t True w a \<sigma> ts')"


fun Upd :: "surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state" where
  "Upd  \<sigma> x a t = (let w = (getVWNC \<sigma> t x) ; ts' = getTS \<sigma> w; v = value \<sigma> w in update_trans t w a \<sigma> ts')"

fun RdXV ::  "surrey_state \<Rightarrow> L  \<Rightarrow> T \<Rightarrow> (surrey_state \<times>V)" where
"RdXV  \<sigma> x t = (let w = (getVW \<sigma> t x); v = value \<sigma> w in (read_trans t False w \<sigma>, v))"

fun RdAV ::  "surrey_state \<Rightarrow> L  \<Rightarrow> T \<Rightarrow> (surrey_state\<times>V)" where
"RdAV  \<sigma> x t = (let w = (getVW \<sigma> t x); v = value \<sigma> w  in (read_trans t True w \<sigma>, v))"

syntax 

  "_AnnAssignRX"    :: "'a assn \<Rightarrow> L  \<Rightarrow>  T \<Rightarrow> V  \<Rightarrow> surrey_state \<Rightarrow> 'a com" ("(_ <_ :=\<^sub>_ _ \<acute>_>)"  [90, 75,70,65] 61)
  "_AssignRX"       :: "L \<Rightarrow> T \<Rightarrow> V \<Rightarrow>  surrey_state \<Rightarrow> 'a com"            ("(<_ :=\<^sub>_ _ \<acute>_>)"  [90, 70,65] 61)

  "_AnnAssignR"    :: "'a assn \<Rightarrow> L \<Rightarrow> T \<Rightarrow> V \<Rightarrow> surrey_state \<Rightarrow> 'a com" ("(_ <_  :=\<^sup>R\<^sub>_ _ \<acute>_>)"  [90, 75,70,65] 61)
  "_AssignR"    :: "L \<Rightarrow> T \<Rightarrow> V \<Rightarrow> surrey_state \<Rightarrow> 'a com"               ("(<_ :=\<^sup>R\<^sub>_ _ \<acute>_>)"  [90,70,65] 61)
 

  "_AnnReadRX"    :: "'a assn \<Rightarrow> idt \<Rightarrow> T \<Rightarrow> L \<Rightarrow> surrey_state \<Rightarrow> 'a com" ("(_ <\<acute>_  \<leftarrow>\<^sub>_  _ \<acute>_>)"  [90, 75,70,65] 61)
  "_ReadRX"    :: " idt \<Rightarrow>  T \<Rightarrow> L \<Rightarrow> surrey_state \<Rightarrow> 'a com"              ("(<\<acute>_  \<leftarrow>\<^sub>_  _ \<acute>_>)"  [90, 75,70] 61)

  "_AnnReadA"    :: "'a assn \<Rightarrow> idt \<Rightarrow>  T \<Rightarrow> L \<Rightarrow> surrey_state \<Rightarrow> 'a com" ("(_ <\<acute>_  \<leftarrow>\<^sup>A\<^sub>_  _ \<acute>_>)"  [90, 75,70,65] 61)
  "_ReadA"    :: " idt \<Rightarrow>  T \<Rightarrow> L \<Rightarrow> surrey_state \<Rightarrow> 'a com"              ("(<\<acute>_  \<leftarrow>\<^sup>A\<^sub>_  _ \<acute>_>)"  [90, 75,70] 61)
  
  "_AnnSwap" :: "'a assn \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> 'a com " ("(_ <SWAP[_,_]\<^sub>_ \<acute>_>)"  [90,0,0,0,0] 61)
  "_Swap" :: "L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> 'a com "              ("(<SWAP[_,_]\<^sub>_ \<acute>_>)"  [90,0,0,0] 61)

  "_Until"    :: "'a ann_com  \<Rightarrow>'a bexp  \<Rightarrow> 'a assn \<Rightarrow> 'a com"
                    ("//DO _ //UNTIL _ //INV _ //OD"  [0,0,0] 61)
 

translations

  "r <x :=\<^sub>t a \<acute>s>" \<rightharpoonup> "CONST AnnBasic r (\<guillemotleft>\<acute>(_update_name s (\<lambda>_ .CONST WrX \<acute>s x a t))\<guillemotright>)"
  "<x :=\<^sub>t a \<acute>s>" \<rightharpoonup> "CONST Basic (\<guillemotleft>\<acute>(_update_name s (\<lambda>_ . CONST WrX \<acute>s x a t))\<guillemotright>)"
 
  "r <x :=\<^sup>R\<^sub>t a \<acute>s>" \<rightharpoonup> "CONST AnnBasic r \<guillemotleft>\<acute>(_update_name s (\<lambda>_ .CONST WrR \<acute>s x a t))\<guillemotright>"
  "<x :=\<^sup>R\<^sub>t a \<acute>s>" \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name s (\<lambda>_ . CONST WrR \<acute>s x a t))\<guillemotright>"
  
  "r <\<acute>x \<leftarrow>\<^sub>t y \<acute>s>" \<rightharpoonup>  "CONST AnnAwait r \<lbrace>CONST True\<rbrace> 
                        (CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_ . CONST snd(CONST RdXV \<acute>s y t)))\<guillemotright>,, 
                         CONST Basic \<guillemotleft>\<acute>(_update_name s (\<lambda>_ . CONST fst(CONST RdXV \<acute>s y t)))\<guillemotright>)"


 "<\<acute>x \<leftarrow>\<^sub>t y \<acute>s>" \<rightharpoonup>  "CONST AnnAwait \<lbrace>CONST True\<rbrace>  
                        (CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_ . CONST snd(CONST RdXV \<acute>s y t)))\<guillemotright>,, 
                         CONST Basic \<guillemotleft>\<acute>(_update_name s (\<lambda>_ . CONST fst(CONST RdXV \<acute>s y t)))\<guillemotright>)"

  "r <\<acute>x \<leftarrow>\<^sup>A\<^sub>t y \<acute>s>" \<rightharpoonup>  "CONST AnnAwait r \<lbrace>CONST True\<rbrace> 
                          (CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_ . CONST snd(CONST RdAV \<acute>s y t)))\<guillemotright>,, 
                           CONST Basic \<guillemotleft>\<acute>(_update_name s (\<lambda>_ . CONST fst(CONST RdAV \<acute>s y t)))\<guillemotright>)"

  "<\<acute>x \<leftarrow>\<^sup>A\<^sub>t y \<acute>s>" \<rightharpoonup>  "CONST AnnAwait \<lbrace>CONST True\<rbrace>  
                        (CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_ . CONST snd(CONST RdAV \<acute>s y t)))\<guillemotright>,, 
                         CONST Basic \<guillemotleft>\<acute>(_update_name s (\<lambda>_ . CONST fst(CONST RdAV \<acute>s y t)))\<guillemotright>)"

  "r <SWAP[x, a]\<^sub>t \<acute>s>" \<rightharpoonup> "CONST AnnBasic r (\<guillemotleft>\<acute>(_update_name s (\<lambda>_ .(CONST Upd \<acute>s x a t)))\<guillemotright>)"
  "<SWAP[x, a]\<^sub>t \<acute>s>" \<rightharpoonup> "CONST Basic (\<guillemotleft>\<acute>(_update_name s (\<lambda>_ .(CONST Upd \<acute>s x a t)))\<guillemotright>)"

  "DO c UNTIL b INV i OD" \<rightharpoonup>   "CONST AnnSeq c (CONST AnnWhile i \<lbrace>\<not>b\<rbrace> i c)"



end