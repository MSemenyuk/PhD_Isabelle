theory AllocSem
imports Main
begin 

datatype object_type = pointer | variable     (*object types to be added, specifically variable?*)


record alloc_map = 
  object :: "nat \<Rightarrow> (nat \<times> object_type) option"
  object_ctr :: "nat"


end
  