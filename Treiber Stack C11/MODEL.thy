(*load stores value to a location in weak memory
s=C \<longrightarrow> s.next = C.next
v=*s \<longrightarrow> v = s.next.val
n_star <--_t fst(A(n ms t))
n_star =_t v+1
n*=v+1 \<longrightarrow> n.next.val = v+1

memory model:   ____________C____s____n________old__new_____________n2________________
             ...|___||___||x52||x54||x56||___||x78||x80||___||___||x90||___||___||___|
                |___||___||x78||x78||x80||___||_0_||_x_||___||___||___||___||___||___| ...
                ____________C____s____n1_______old__new_____________n2________________
             ...|___||___||_C_||_s_||_n1||___||x78||x80||___||___||x90||___||___||___|
                |___||___||x80||___||x80||___||Nul||_1_||___||___||___||___||___||___| ...
 

[(s ms t) :=  C] 
[v <-_t (s ms t)]
[fst(A(n ms t)) :=_t v+1]


    ____                          ______
    |__|  <-- Location            |0x52|
C=  |__|  <-- C.next    (C.val)   |0x78|    <-- old.loc
    ____                          ______
    |__|  <-- Location            |0x54|
s=  |__|  <-- s.next    (s.val)   |0x80|
    ____                          ______
    |__|  <-- Location = s.next   |0x80| 
v=  |__|  <-- v.val               |__2_|
    ____                          ______
    |__|  <-- Location            |0x56|
n=  |__|  <-- n.next    (n.val)   |0x80|



rd_cap(i) \<noteq> {} \<longrightarrow> A(i) --\\<longrightarrow> none
wr_cap(i) \<noteq> {} \<longrightarrow> A(i) --\\<longrightarrow> none
wr_cap(i) \<noteq> {} \<longrightarrow> cannot acquire rd_cap(i)



*)