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
          | Pass \<Rightarrow> firewall next_rules p
          )"

  text{*Example*}
    value "firewall allow_only_DNS_ruleset DNS_query"
    lemma "firewall allow_only_DNS_ruleset DNS_query = Allow" by eval

    value "firewall allow_only_HTTP_ruleset DNS_query"
    lemma "firewall allow_only_HTTP_ruleset DNS_query = Deny" by eval

    value "firewall (allow_DNS \<section> allow_HTTP \<section> DefaultDeny) DNS_query" (*allow DNS*)
    value "firewall (allow_DNS \<section> allow_HTTP \<section> DefaultDeny) HTTP_query" (*allow HTTP*)
    value "firewall (allow_DNS \<section> allow_HTTP \<section> DefaultDeny) \<lparr> src_addr = ''1.2.3.4'', dst_addr = ''8.8.8.8'', proto = UDP, src_port = 38724, dst_port = 22\<rparr>" (*deny ssh*)
  

  text{*A firewall always makes an Allow or Deny decision, it cannot return Pass*}
  lemma "firewall r p = Allow \<or> firewall r p = Deny"
    proof(induction r)
      case DefaultAllow
        have "firewall DefaultAllow p = Allow" by simp
        from this show "firewall DefaultAllow p = Allow \<or> firewall DefaultAllow p = Deny" by simp
      next
      case DefaultDeny
        show "firewall DefaultDeny p = Allow \<or> firewall DefaultDeny p = Deny" by simp
      next
      case(Rule rule next_rules)
        assume IH: "firewall next_rules p = Allow \<or> firewall next_rules p = Deny"
        show "firewall (rule \<section> next_rules) p = Allow \<or> firewall (rule \<section> next_rules) p = Deny"
          proof(cases "rule p")
            case Allow
              hence "firewall (rule \<section> next_rules) p = Allow" by simp
              from this show "firewall (rule \<section> next_rules) p = Allow \<or> firewall (rule \<section> next_rules) p = Deny" by simp
            next
            case Deny
              thus "firewall (rule \<section> next_rules) p = Allow \<or> firewall (rule \<section> next_rules) p = Deny" by simp
            next
            case Pass
              hence "firewall (rule \<section> next_rules) p = firewall next_rules p" by simp
              also have "firewall next_rules p = Allow \<or> firewall next_rules p = Deny" using IH by simp
              finally show "firewall (rule \<section> next_rules) p = Allow \<or> firewall (rule \<section> next_rules) p = Deny" by simp
          qed
    qed

subsection{*Analyzing rulesets*}
  (*the ruleset ONLY accepts DNS and HTTP*)
  lemma "firewall (allow_DNS \<section> allow_HTTP \<section> DefaultDeny) p = Allow \<longleftrightarrow> (proto p = UDP \<and> dst_port p = 53) \<or> (proto p = TCP \<and> dst_port p = 80)"
    by(simp add: allow_DNS_def allow_HTTP_def)


  definition deny_UDP :: "packet \<Rightarrow> action" where "deny_UDP p \<equiv> if proto p = UDP then Deny else Pass"

  value "firewall (deny_UDP \<section> allow_DNS \<section> allow_HTTP \<section> DefaultDeny) DNS_query" (*deny DNS traffic because it is UDP*)

  (*The firewall can be simplified because allow_DNS is shadowed by deny_UDP*)
  (*for all packets p, the two rule sets are identical*)
  lemma "firewall (deny_UDP \<section> allow_DNS \<section> allow_HTTP \<section> DefaultDeny) = firewall (deny_UDP \<section> allow_HTTP \<section> DefaultDeny)"
    apply(simp only: fun_eq_iff)
    apply(clarify, rename_tac p)
    by(simp add: allow_DNS_def allow_HTTP_def deny_UDP_def)

  (*we can even rorder*)
  lemma "firewall (deny_UDP \<section> allow_DNS \<section> allow_HTTP \<section> DefaultDeny) = firewall (allow_HTTP \<section> deny_UDP \<section> DefaultDeny)"
    by(simp add: fun_eq_iff allow_DNS_def allow_HTTP_def deny_UDP_def)

  (*but not arbitrarily*)
  lemma "firewall (deny_UDP \<section> allow_DNS \<section> allow_HTTP \<section> DefaultDeny) \<noteq> firewall (allow_DNS \<section> deny_UDP \<section> allow_HTTP \<section> DefaultDeny)"
    apply(simp add: allow_DNS_def allow_HTTP_def deny_UDP_def fun_eq_iff)
    apply(rule_tac x="DNS_query" in exI)
    by(simp add: DNS_query_def)
    


end
