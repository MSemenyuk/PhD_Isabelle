theory PSem 
imports Main OpSem_Proof_Rules
begin 

datatype object_type = pointer | variable     (*object types to be added, specifically variable?*)

type_synonym address = nat
type_synonym id = nat

record posem = 
  A :: "id \<Rightarrow> (L \<times> object_type) option"
  alloc_addrs :: "L set"  (* allocation *)
  obj_ctr :: "nat"            (*always increasing with \<forall>i.i\<ge>obj_ctr s \<longrightarrow> A(i) = None*)
                              (* have old pointers *s point to 0, if freed/detached or current value of C - in critical*)


definition "codomain_of_A ps \<equiv> \<Union>{{fst(alloc)} | alloc. alloc \<in> ran(A ps)}"

definition "isfree_addr a ps \<equiv> a\<notin>(alloc_addrs ps) "

definition "constant_alloc_ass ps \<equiv> \<forall>loc. (loc \<in> alloc_addrs ps \<longleftrightarrow> loc \<in> codomain_of_A ps)
                                         \<and>(loc \<notin> alloc_addrs ps \<longleftrightarrow> loc \<notin> codomain_of_A ps)"

definition "Unique_allocs ps \<equiv> \<forall>prov alloc b. (A ps prov) = Some (alloc,b) \<longrightarrow> (\<nexists>prov' b'. 
                                        prov\<noteq>prov' \<and> (A ps prov') = Some (alloc,b'))"

definition "psem_rules ps \<equiv> Unique_allocs ps \<and> constant_alloc_ass ps"
                                                           



lemmas alloc_general_lemmas [simp] = codomain_of_A_def isfree_addr_def constant_alloc_ass_def
                                      Unique_allocs_def psem_rules_def

lemma " psem_rules ps \<Longrightarrow> isfree_addr loc ps \<Longrightarrow> loc\<notin> codomain_of_A ps"
  using alloc_general_lemmas isfree_addr_def by blast


definition "allocate_object ps loc prov ps' typ \<equiv> isfree_addr loc ps \<and> prov \<notin> dom(A ps)
 \<and> ps' = ps\<lparr>A := (A ps) (prov:=Some (loc, typ)),
            alloc_addrs := (alloc_addrs ps \<union> {loc})\<rparr>"

definition "kill ps prov ps' \<equiv> \<exists>x. (prov \<in> dom(A ps) \<and> Some x = A ps prov 
\<and> ps' = ps \<lparr> A:= (A ps) (prov:= None),
            alloc_addrs := (alloc_addrs ps - {fst(x)})\<rparr>)"

lemmas alloc_operation_lemmas [simp] = allocate_object_def kill_def


lemma set_alloc_addr_lem1:
  "allocate_object ps loc prov ps' typ
  \<Longrightarrow> prov \<notin> dom(A ps)"
  by auto

lemma set_alloc_addr_lem2:
  "allocate_object ps loc prov ps' typ
  \<Longrightarrow> prov \<in> dom(A ps')"
  by auto
  
lemma temp_lemma1:
  "constant_alloc_ass ps \<Longrightarrow> loc \<in> alloc_addrs ps \<Longrightarrow> loc \<in> codomain_of_A ps"
  by (simp)
lemma temp_lemma2:
  "constant_alloc_ass ps \<Longrightarrow> loc \<in> codomain_of_A ps \<Longrightarrow> loc \<in> alloc_addrs ps"
  by (simp)
lemma temp_lemma3:
  "constant_alloc_ass ps \<Longrightarrow> loc \<notin> alloc_addrs ps \<Longrightarrow> loc \<notin> codomain_of_A ps"
  by (simp)
lemma temp_lemma4:
  "constant_alloc_ass ps \<Longrightarrow> loc \<notin> codomain_of_A ps \<Longrightarrow> loc \<notin> alloc_addrs ps"
  by (simp)


lemma uniqueness_lemma1:
  "constant_alloc_ass ps \<Longrightarrow> Unique_allocs ps \<Longrightarrow>
 loca \<in> codomain_of_A ps \<Longrightarrow> 
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
 loca \<notin> codomain_of_A ps"
  by simp
lemma uniqueness_lemma4:
  "constant_alloc_ass ps \<Longrightarrow>
 isfree_addr loca ps \<Longrightarrow> 
 \<nexists>prova b. A ps prova = Some (loca,b)"
  apply simp
  by (metis insertI1 ranI)

lemma uniqueness_lemma5:
  "constant_alloc_ass ps \<Longrightarrow>
 isfree_addr loca ps \<Longrightarrow> 
A ps 1 = Some (1, pointer) \<Longrightarrow>
A ps 2 = Some (1, variable)
\<Longrightarrow>
\<not> Unique_allocs ps "
  apply simp 
  by (metis n_not_Suc_n numeral_2_eq_2)
  






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
shows "loc \<notin> codomain_of_A ps'"
  using assms apply simp
  apply clarify apply auto 
  by (metis ComplD insertCI ran_restrictD restrict_complement_singleton_eq)
  
lemma kill_preserves_structure_3:
  assumes "constant_alloc_ass ps"
  and "kill ps prov ps'"
  and "Unique_allocs ps"
  and "\<exists>b. A ps prov = Some(loc, b)"
shows "\<nexists>prov b. A ps' prov = Some(loc, b)"
  using assms apply simp
  apply clarify apply auto 
  by (metis option.discI)

lemma allocation_preserves_structure:
  assumes "prov \<notin> dom(A ps)"
  and "constant_alloc_ass ps"
  and "isfree_addr loc ps"
  and "allocate_object ps loc prov ps' typ"
shows "constant_alloc_ass ps'"
  using assms apply simp 
  apply clarify
  by (smt (z3) assms(1) domIff insert_iff old.prod.inject ran_map_upd singletonD)

lemma kill_preserves_structure:
  assumes "constant_alloc_ass ps"
  and "kill ps prov ps'"
  and "Unique_allocs ps"
  and "\<exists>b. A ps prov = Some(loc, b)"
shows "constant_alloc_ass ps'"
  using assms apply simp
  apply clarify apply auto
  apply (smt (z3) Compl_insert Diff_insert_absorb Pair_inject empty_iff fun_upd_same fun_upd_triv fun_upd_upd insertE insert_Diff insert_absorb insert_absorb insert_compr insert_ident insert_iff insert_iff mk_disjoint_insert ranI ran_map_upd restrict_complement_singleton_eq singletonI)
  apply (metis (no_types, lifting) insert_iff ranI ran_restrictD restrict_complement_singleton_eq)
  apply (metis ComplD insertCI option.sel ran_restrictD restrict_complement_singleton_eq)
  apply (metis (no_types, lifting) insert_iff ranI ran_restrictD restrict_complement_singleton_eq)
  apply (metis ComplD insertCI option.sel ran_restrictD restrict_complement_singleton_eq) 
  by (smt (z3) Compl_insert Diff_insert_absorb Pair_inject empty_iff fun_upd_same fun_upd_triv fun_upd_upd insertE insert_Diff insert_absorb insert_absorb insert_compr insert_ident insert_iff insert_iff mk_disjoint_insert ranI ran_map_upd restrict_complement_singleton_eq singletonI)


lemma allocation_preserves_uniqueness_sup_1:
  assumes "prov \<notin> dom(A ps)"
  and "constant_alloc_ass ps"
  and "Unique_allocs ps"
  and "isfree_addr loc ps"
  and "allocate_object ps loc prov ps' typ"
shows "constant_alloc_ass ps'"
  using assms allocation_preserves_structure [where ps = ps and ps'=ps'] 
  by blast

lemma allocation_preserves_uniqueness:
  assumes "prov \<notin> dom(A ps)"
  and "constant_alloc_ass ps"
  and "Unique_allocs ps"
  and "isfree_addr loc ps"
  and "allocate_object ps loc prov ps' typ"
shows "Unique_allocs ps'"
  using assms apply simp
  apply clarify apply auto prefer 2
  apply (metis (no_types) insertI1 ranI)
  by (metis (no_types) insertI1 ranI)

lemma kill_preserves_uniqueness:
  assumes "constant_alloc_ass ps"
  and "kill ps prov ps'"
  and "Unique_allocs ps"
  and "\<exists>b. A ps prov = Some(loc, b)"
shows "Unique_allocs ps'"
  using assms apply simp
  apply clarify apply auto 
  by (metis option.discI)
  



end