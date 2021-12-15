theory temp

imports Main

begin


datatype 'a tree = Tip 
  | Node "'a tree" 'a "'a tree"


primrec revtree :: "'a tree \<Rightarrow> 'a tree"
  where 
"revtree Tip = Tip" |
"revtree (Node xs x ys) = (Node (revtree ys) x (revtree xs))"

lemma reverse:
  shows "revtree(revtree(t)) = t"
  apply (induct_tac t)
  by auto



lemma reverse2:
  shows "revtree(revtree(revtree(t))) = revtree(t)"
  using reverse apply auto



(*
     a
   /    \
atree   atree

*)