theory PSem 
imports Main 
begin 

datatype object_type = pointer | variable     (*object types to be added, specifically variable?*)

type_synonym address = nat
type_synonym id = nat

record posem = 
  A :: "id \<Rightarrow> (nat \<times> object_type) option"
  alloc_addrs :: "nat set"  (*locations in ran(A ps)*)



definition "newran loc ps \<equiv> \<exists>b. (loc, b)\<in>ran(A ps)"

definition "isfree_addr a ps \<equiv> a\<notin>(alloc_addrs ps) "

definition "constant_alloc_ass ps \<equiv> \<forall>loc. (loc \<in> alloc_addrs ps \<longleftrightarrow> newran loc ps)"

definition "Unique_allocs ps \<equiv> \<forall>prov . prov\<in> dom(A ps) 
\<longrightarrow> (\<nexists>prov'. prov'\<noteq>prov \<and> prov'\<in> dom(A ps) \<and> fst(the(A ps prov')) = fst(the(A ps prov)))"

definition "psem_rules ps \<equiv> Unique_allocs ps \<and> constant_alloc_ass ps"
                                                           

lemmas alloc_general_lemmas [simp] = newran_def isfree_addr_def constant_alloc_ass_def
                                      Unique_allocs_def psem_rules_def



definition "allocate_object ps loc prov ps' typ \<equiv> isfree_addr loc ps \<and> prov \<notin> dom(A ps)
 \<and> ps' = ps\<lparr>A := (A ps) (prov:=Some (loc, typ)),
            alloc_addrs := (alloc_addrs ps \<union> {loc})\<rparr>"

definition "kill ps prov ps' \<equiv>  prov \<in> dom(A ps) 
\<and> ps' = ps \<lparr> A:= (A ps) (prov:= None),
            alloc_addrs := (alloc_addrs ps - {fst(the(A ps prov))})\<rparr>"


lemmas alloc_operation_lemmas [simp] = allocate_object_def kill_def





(*------------might be useful in other proofs----------------*)
lemma in_dom_notNone :
  "prov\<in>dom(A ps) \<Longrightarrow> \<exists>loc b. A ps prov = Some (loc,b)"
  by auto

lemma "prov\<in>dom(A ps) \<Longrightarrow> constant_alloc_ass ps \<Longrightarrow> fst(the(A ps prov)) \<in> alloc_addrs ps"
  apply(simp) 
  by (metis fst_conv in_dom_notNone option.sel ranI)

lemma set_alloc_addr_lem1:
  "allocate_object ps loc prov ps' typ
  \<Longrightarrow> prov \<notin> dom(A ps)"
  by auto

lemma set_alloc_addr_lem2:
  "allocate_object ps loc prov ps' typ
  \<Longrightarrow> prov \<in> dom(A ps')"
  by auto

lemma pssimp : "kill ps prov ps' \<Longrightarrow>
  A ps' prov = None \<and> alloc_addrs ps' = alloc_addrs ps - {fst(the(A ps prov))}"
  by(simp)

lemma uniqueness_lemma1:
  "constant_alloc_ass ps \<Longrightarrow> 
 psem_rules ps \<Longrightarrow> 
 locb \<in> alloc_addrs ps \<Longrightarrow> 
 prova=provb \<Longrightarrow> fst(the(A ps prova)) = loca \<Longrightarrow> fst(the(A ps provb)) = locb \<Longrightarrow> loca=locb"
  by (simp)

lemma uniqueness_lemma2:
  "constant_alloc_ass ps \<Longrightarrow> Unique_allocs ps \<Longrightarrow>
 \<not>isfree_addr loca ps \<Longrightarrow> 
 \<not>isfree_addr locb ps \<Longrightarrow>  
 prova=provb \<Longrightarrow> fst(the(A ps prova)) = loca \<Longrightarrow> fst(the(A ps provb)) = locb \<Longrightarrow> loca=locb"
  by (simp)

lemma uniqueness_lemma3:
  "constant_alloc_ass ps \<Longrightarrow>
 isfree_addr loca ps \<Longrightarrow> 
 \<nexists>prova b. A ps prova = Some (loca,b)"
  apply simp
  by (metis ranI)

lemma alloc_step_1:
  assumes "prov \<notin> dom(A ps)"
  and "isfree_addr loc ps"
  and "allocate_object ps loc prov ps' typ"
shows "prov \<in> dom(A ps')"
  using assms by simp 

lemma alloc_step_2:
  assumes "prov \<notin> dom(A ps)"
  and "isfree_addr loc ps"
  and "allocate_object ps loc prov ps' typ"
shows "\<not>(isfree_addr loc ps')"
  using assms by simp 

lemma alloc_step_3:
  assumes "prov \<notin> dom(A ps)"
  and "isfree_addr loc ps"
  and "allocate_object ps loc prov ps' typ"
shows "\<not>(isfree_addr loc ps')"
  using assms by simp 

lemma kill_preserves_structure_1:
  assumes "constant_alloc_ass ps"
  and "kill ps prov ps'"
  and "\<exists>b. A ps prov = Some(loc, b)"
shows "isfree_addr loc ps'"
  using assms apply simp
  apply clarify
  by auto
 
lemma kill_preserves_structure_2:
  assumes "constant_alloc_ass ps"
  and "kill ps prov ps'"
  and "Unique_allocs ps"
  and "\<exists>b. A ps prov = Some(loc, b)"
shows "\<not>newran loc ps'"
  using assms apply simp
  apply clarify apply auto 
  by (metis ComplD domI fstI insertCI option.sel ran_restrictD restrict_complement_singleton_eq)



   
  
(*-----------------penultimate--------------------*)

lemma testingthisone:
  "(loc,b)\<in>ran(A ps) \<Longrightarrow> (\<exists>prov. (prov\<in>dom(A ps) \<and> the(A ps prov) = (loc,b)))"
  by (smt (verit) domI mem_Collect_eq option.sel ran_def)

lemma allocation_preserves_structure:
  assumes "psem_rules ps"
  and "allocate_object ps loc prov ps' typ"
shows "constant_alloc_ass ps'"
  using assms apply simp 
  apply clarify 
  by (metis Domain_iff Domain_insert insertCI insertE option.exhaust_sel ran_map_upd)


lemma kill_preserves_structure:
  assumes "psem_rules ps"
  and "kill ps prov ps'"
shows " constant_alloc_ass ps'"
  using assms apply simp
  apply auto
  apply (metis domIff fun_upd_apply old.prod.inject option.collapse ranI testingthisone)
  apply (metis ranI ran_restrictD restrict_complement_singleton_eq)
  by (metis ComplD domI fst_eqD insertCI option.sel ran_restrictD restrict_complement_singleton_eq)
  
lemma allocation_preserves_uniqueness:
  assumes "psem_rules ps"
  and "allocate_object ps loc prov ps' typ"
shows "Unique_allocs ps'"
  using assms apply simp
  apply clarify apply safe 
  apply (metis fst_conv option.sel ranI) 
  by (metis fst_conv option.sel ranI)
  

lemma kill_preserves_uniqueness:
  assumes "psem_rules ps"
  and "kill ps prov ps'"
shows "Unique_allocs ps'"
  using assms by simp






(*-----------------summary--------------------*)

lemma psem_rules_preserved_alloc:
"psem_rules ps \<Longrightarrow> allocate_object ps loc prov ps' typ \<Longrightarrow> psem_rules ps'"
  unfolding psem_rules_def apply(intro conjI impI) 
  using allocation_preserves_uniqueness psem_rules_def apply blast
  using allocation_preserves_structure psem_rules_def by blast
  

lemma psem_rules_preserved_kill:
"psem_rules ps \<Longrightarrow>  kill ps i ps' \<Longrightarrow> psem_rules ps'"
  unfolding psem_rules_def apply(intro conjI impI)
  using kill_preserves_uniqueness psem_rules_def apply blast
  using kill_preserves_structure psem_rules_def by blast
  

end