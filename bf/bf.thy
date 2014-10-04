theory bf
imports "~/git/Iptables_Semantics/Bitmagic/autocorres-0.98/autocorres/AutoCorres"
begin

install_C_file "bf.c"


autocorres [
  heap_abs_syntax,
  no_heap_abs=init,
  (*no_signed_word_abs=init,*)
  unsigned_word_abs=init] "bf.c"

lemma (in bf) init:
  "\<forall>s\<^sub>0. \<lbrace> \<lambda>s.  s = s\<^sub>0 \<rbrace>
      init'
        \<lbrace> \<lambda>rs s. s = t_hrs_'_update (hrs_mem_update (
          heap_update_list (ptr_val p) (replicate 256 0))) s\<^sub>0  \<rbrace>!"
  unfolding init'_def
  apply(rule allI)
  apply (subst whileLoop_add_inv[where I="\<lambda>i s. i \<le> 256 \<and> i \<ge> 0" and M="\<lambda>(i, _). nat (256 - i)"])
  apply(wp)
  apply(simp_all)
  apply(simp add: INT_MAX_def)
  oops
  

end
