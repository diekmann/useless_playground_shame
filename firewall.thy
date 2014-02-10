theory firewall
imports Main
begin

section{*Modeling Firewalls*}

subsection{*Syntax*}
  (*The action a firewall can do to a packet*)
  datatype action = 
        Allow  (*accept packet*)
      | Deny   (*drop packet*)
      | Pass   (*apply next rule*)
  
  (*We say a packet is of arbitrary type 'p*)
  
  (*We define the type 'p rule as synonym for a total function from packets to actions*)
  type_synonym 'p rule = "'p \<Rightarrow> action"
  
  
  (*A firewall ruleset is a default rule (allow or deny) or a rule followed by the rest of the ruleset*)
  datatype 'p ruleset =
        DefaultAllow
      | DefaultDeny
      | Rule "'p rule" "'p ruleset" (infixr "\<section>" 65)
  
  
  value "Rule (\<lambda>p. Allow) (Rule (\<lambda>p. Deny) DefaultAllow)"
  value "(\<lambda>p. Allow) \<section> (\<lambda>p. Deny) \<section> DefaultAllow"
  
  
  lemma "Rule (\<lambda>p. Allow) (Rule (\<lambda>p. Deny) DefaultAllow) = (\<lambda>p. Allow) \<section> (\<lambda>p. Deny) \<section> DefaultAllow" by simp

  subsubsection{*Example*}
    datatype protocol = TCP | UDP
    record packet = src_addr :: string
                    dst_addr :: string
                    proto :: protocol
                    src_port :: nat
                    dst_port ::nat

    definition DNS_query :: packet where
      "DNS_query \<equiv> \<lparr> src_addr = ''1.2.3.4'', dst_addr = ''8.8.8.8'', proto = UDP, src_port = 38724, dst_port = 53\<rparr>"
    definition HTTP_query :: packet where
      "HTTP_query \<equiv> \<lparr> src_addr = ''1.2.3.4'', dst_addr = ''google.de'', proto = TCP, src_port = 38724, dst_port = 80\<rparr>"

    definition allow_DNS :: "packet \<Rightarrow> action" where
      "allow_DNS p \<equiv> if proto p = UDP \<and> dst_port p = 53 then Allow else Pass"

    definition allow_HTTP :: "packet \<Rightarrow> action" where
      "allow_HTTP p \<equiv> if proto p = TCP \<and> dst_port p = 80 then Allow else Pass"

    definition allow_only_DNS_ruleset :: "packet ruleset" where
      "allow_only_DNS_ruleset \<equiv> allow_DNS \<section> DefaultDeny"

    definition allow_only_HTTP_ruleset :: "packet ruleset" where
      "allow_only_HTTP_ruleset \<equiv> allow_HTTP \<section> DefaultDeny"


subsection{*Semantics*}
  fun firewall :: "'p ruleset \<Rightarrow> 'p \<Rightarrow> action" where
      "firewall DefaultAllow _ = Allow"
    |  "firewall DefaultDeny _ = Deny"
    | "firewall (rule \<section> next_rules) p = (case rule p of 
            Allow \<Rightarrow> Allow
          | Deny \<Rightarrow> Deny
          | Next \<Rightarrow> firewall next_rules p
          )"

  text{*Example*}
    value "firewall allow_only_DNS_ruleset DNS_query"
    lemma "firewall allow_only_DNS_ruleset DNS_query = Allow" by eval

    value "firewall allow_only_HTTP_ruleset DNS_query"
    lemma "firewall allow_only_HTTP_ruleset DNS_query = Deny" by eval

  text{*A firewall always makes an Allow or Deny decision, it cannot return Next*}
  lemma "firewall r p = Allow \<or> firewall r p = Deny"
    apply(induction r)
    apply(simp only: firewall.simps(1))
    apply(simp)
    apply(simp)
    apply(case_tac "fun p")
    apply(simp_all)
    done
    


end
