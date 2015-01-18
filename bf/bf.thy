theory bf
imports "~/git/Iptables_Semantics/Bitmagic/autocorres-0.98/autocorres/AutoCorres"
begin

install_C_file "bf.c"


autocorres [
  heap_abs_syntax,
  no_heap_abs=init,
  (*no_signed_word_abs=init,*)
  unsigned_word_abs=init] "bf.c"

term hrs_mem_update
term t_hrs_'_update
term heap_update_list
term globals.a_'
term globals.a_'
thm globals.a_'_def
term ptr_val
term Arrays.update
find_consts "'a['b]"

fun aupda :: "8 word['b::finite] \<Rightarrow> nat \<Rightarrow> 8 word['b]" where
  "aupda a 0 = Arrays.update a 0 0" |
  "aupda a (Suc i) = aupda (Arrays.update a (Suc i) 0) i"

lemma "i \<ge> CARD('b) \<Longrightarrow> aupda s i = Arrays.FCP (\<lambda>_. 0)"
  apply(induction s i rule: aupda.induct)
   apply(simp add: FCP_def Arrays.update_def)
   
  apply(simp)
  apply(case_tac "i = 255")
   apply(simp_all)
  
  oops
  


fun gaupda :: "globals \<Rightarrow> nat \<Rightarrow> globals" where
  "gaupda s 0 = s\<lparr>globals.a_' := Arrays.update (globals.a_' s) 0 0\<rparr>" |
  "gaupda s (Suc i) = gaupda (s\<lparr>globals.a_' := Arrays.update (globals.a_' s) i 0\<rparr>) i"


lemma "i \<ge> CARD(256) \<Longrightarrow> gaupda s i = s\<lparr>globals.a_' := Arrays.FCP (\<lambda>_. 0)\<rparr>"
  apply(induction s i rule: gaupda.induct)
   apply(simp)
  apply(simp)
  apply(case_tac "i = 255")
   apply(simp_all)
  
  oops
  

lemma (in bf) init:
  "\<forall>s\<^sub>0. \<lbrace> \<lambda>s.  s = s\<^sub>0 \<rbrace>
      init'
        \<lbrace> \<lambda>rs s. s = s\<^sub>0\<lparr>globals.a_' := Arrays.FCP (\<lambda>_. 0)\<rparr>  \<rbrace>!"
(*\<lbrace> \<lambda>rs s. s = t_hrs_'_update (hrs_mem_update (heap_update_list (addr) (replicate 255 0))) s\<^sub>0  \<rbrace>!*)
  unfolding init'_def
  apply(rule allI)
  apply (subst whileLoop_add_inv[where I="\<lambda>i s. i \<le> 256 \<and> i \<ge> 0 \<and> s = gaupda s\<^sub>0 ((unat (of_int i)))" and M="\<lambda>(i, _). nat (256 - i)"])
  apply(wp)
  apply(simp_all)
  apply(simp add: INT_MAX_def)
  
  apply(clarsimp)
  apply (clarsimp simp: FCP_def)
  
  oops
  

end
