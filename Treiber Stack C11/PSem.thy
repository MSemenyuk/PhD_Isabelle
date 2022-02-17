theory PSem 
imports Main OpSem
begin 

datatype object_type = pointer | variable     (*object types to be added, specifically variable?*)

type_synonym address = nat
type_synonym id = nat

record posem = 
  A :: "id \<Rightarrow> (L \<times> object_type) option"
  alloc_addrs :: "L set"  (* allocation *)
  obj_ctr :: "nat"            (*always increasing with \<forall>i.i\<ge>obj_ctr s \<longrightarrow> A(i) = None*)
                              (* have old pointers *s point to 0, if freed/detached or current value of C - in critical*)

definition "isfree_addr a ps \<equiv> a\<notin>(alloc_addrs ps)"

definition "allocate_object ps loc prov ps' \<equiv> isfree_addr loc ps \<and> prov\<notin>dom(A ps)
 \<and> ps' = ps\<lparr>A := (A ps) (prov:=Some (loc, pointer)),
            alloc_addrs := (alloc_addrs ps \<union> {loc})\<rparr>"

definition "kill ps prov ps' \<equiv> \<exists>x. (prov \<in> dom(A ps) \<and> Some x = A ps prov 
\<and> ps' = ps \<lparr> A:= (A ps) (prov:= None),
            alloc_addrs := (alloc_addrs ps - {fst(x)})\<rparr>)"

lemmas posem_lemmas [simp] = isfree_addr_def allocate_object_def kill_def
end