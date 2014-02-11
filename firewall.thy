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



section{*Firewalls are lists of rules*}
  (*a list*)
  value "[1::int, 2, 3, 4]"

  (*reversing a list*)
  value "rev [1::int, 2, 3, 4]"

  value "rev (rev [1::int, 2, 3, 4])"

  lemma "rev (rev l) = l" by simp

  (*list construction by # *)
  lemma "1#[2,3,4] = [1,2,3,4]" by simp

  value "[allow_DNS, allow_HTTP] :: packet rule list"

  fun firewall_list_defaultDeny :: "'p rule list \<Rightarrow> 'p \<Rightarrow> action" where
    "firewall_list_defaultDeny [] _ = Deny"
  | "firewall_list_defaultDeny (rule # next_rules) p = (case rule p of 
          Allow \<Rightarrow> Allow
        | Deny \<Rightarrow> Deny
        | Pass \<Rightarrow> firewall_list_defaultDeny next_rules p
        )"

  (*we will now relate the firewall and firewall_list_defaultDeny semantics*)

section{*Translations*}
  (*for our firewall_list_defaultDeny firewall*)
  fun ruleset_to_rulelist :: "'p ruleset \<Rightarrow> 'p rule list" where
      "ruleset_to_rulelist DefaultDeny = []"
    | "ruleset_to_rulelist DefaultAllow = [(\<lambda>p. Allow)]"
    | "ruleset_to_rulelist (r \<section> rs) = r # (ruleset_to_rulelist rs)"


  (*example: translating a ruleset to a rule list*)
  lemma "ruleset_to_rulelist (allow_DNS \<section> allow_HTTP \<section> DefaultDeny) = [allow_DNS, allow_HTTP]" by(simp)

  (*the firewall and firewall_list_defaultDeny are qeual for this case!*)
  lemma "firewall (allow_DNS \<section> allow_HTTP \<section> DefaultDeny) = firewall_list_defaultDeny [allow_DNS, allow_HTTP]"
    by(simp add: allow_DNS_def allow_HTTP_def fun_eq_iff)

  (*Let's show the general case*)

  (*does a ruleset end with a default deny rule?*)
  fun is_defaultDeny_ruleset :: "'p ruleset \<Rightarrow> bool" where
      "is_defaultDeny_ruleset DefaultDeny = True"
    | "is_defaultDeny_ruleset DefaultAllow = False"
    | "is_defaultDeny_ruleset (_ \<section> next_rules) = is_defaultDeny_ruleset next_rules"

  lemma "is_defaultDeny_ruleset (deny_UDP \<section> allow_DNS \<section> allow_HTTP \<section> DefaultDeny)" by simp
  lemma "\<not> is_defaultDeny_ruleset (deny_UDP \<section> allow_DNS \<section> allow_HTTP \<section> DefaultAllow)" by simp


  lemma fw_eq_fwlist: 
    "is_defaultDeny_ruleset r \<Longrightarrow> firewall r = firewall_list_defaultDeny (ruleset_to_rulelist r)"
    proof(simp add: fun_eq_iff, clarify)
    fix p
    show "is_defaultDeny_ruleset r \<Longrightarrow> firewall r p = firewall_list_defaultDeny (ruleset_to_rulelist r) p"
    proof(induction r)
     case DefaultAllow
      show "firewall DefaultAllow p = firewall_list_defaultDeny (ruleset_to_rulelist DefaultAllow) p" by simp
     next
     case DefaultDeny
      have 1: "firewall DefaultDeny p = Deny" by simp

      have "ruleset_to_rulelist DefaultDeny = []" by simp
      hence "firewall_list_defaultDeny (ruleset_to_rulelist DefaultDeny) p = firewall_list_defaultDeny [] p" by simp
      also have "firewall_list_defaultDeny [] p = Deny" by simp
      finally have 2: "firewall_list_defaultDeny (ruleset_to_rulelist DefaultDeny) p = Deny" by simp

      from 1 2 show "firewall DefaultDeny p = firewall_list_defaultDeny (ruleset_to_rulelist DefaultDeny) p" by simp
     next
     case (Rule rule next_rules)
      assume defaultDeny: "is_defaultDeny_ruleset (rule \<section> next_rules)"
      and IH: "is_defaultDeny_ruleset next_rules \<Longrightarrow> firewall next_rules p = firewall_list_defaultDeny (ruleset_to_rulelist next_rules) p" (*induction hypothesis*)
  
      from IH defaultDeny have IH_simplified: "firewall next_rules p = firewall_list_defaultDeny (ruleset_to_rulelist next_rules) p" by simp
  
      have rule_list: "ruleset_to_rulelist (rule \<section> next_rules) = rule # ruleset_to_rulelist next_rules" by simp
  
      show  "firewall (rule \<section> next_rules) p = firewall_list_defaultDeny (ruleset_to_rulelist (rule \<section> next_rules)) p"
        proof(cases "rule p") (*does rule match on p*)
          case Allow
            assume Allow: "rule p = Allow"
            from Allow have 1: "firewall (rule \<section> next_rules) p = Allow" by simp
            from Allow have "firewall_list_defaultDeny (rule # (ruleset_to_rulelist next_rules)) p = Allow" by simp
            from this rule_list have 2: "firewall_list_defaultDeny (ruleset_to_rulelist (rule \<section> next_rules)) p = Allow" by simp
            from 1 2 show "firewall (rule \<section> next_rules) p = firewall_list_defaultDeny (ruleset_to_rulelist (rule \<section> next_rules)) p" by simp
          next
          case Deny
            assume Deny: "rule p = Deny"
            thus "firewall (rule \<section> next_rules) p = firewall_list_defaultDeny (ruleset_to_rulelist (rule \<section> next_rules)) p" by simp
          next
          case Pass
            assume Pass: "rule p = Pass"
            from Pass have 1: "firewall (rule \<section> next_rules) p = firewall next_rules p" by simp
            from Pass have 2: "firewall_list_defaultDeny (ruleset_to_rulelist (rule \<section> next_rules)) p = firewall_list_defaultDeny (ruleset_to_rulelist next_rules) p" by simp
            from 1 2 IH_simplified show "firewall (rule \<section> next_rules) p = firewall_list_defaultDeny (ruleset_to_rulelist (rule \<section> next_rules)) p" by simp
          qed
    qed
   qed
    


  (*translating back*)
  fun rulelist_to_ruleset :: "'p rule list \<Rightarrow> 'p ruleset" where
      "rulelist_to_ruleset [] = DefaultDeny"
    | "rulelist_to_ruleset (rule#next_rules) = (rule \<section> rulelist_to_ruleset next_rules)"

  (*the identity*)
  lemma translation_id1: "ruleset_to_rulelist (rulelist_to_ruleset r) = r"
    by(induction r, simp_all)

  (*the identity*)
  lemma translation_id2: "is_defaultDeny_ruleset r \<Longrightarrow> rulelist_to_ruleset (ruleset_to_rulelist r) = r"
    by(induction r, simp_all)
  (*what happens if we don't require is_defaultDeny_ruleset???*)


  (*corollary: we can state something like fw_eq_fwlist now in reverse*)

  lemma "is_defaultDeny_ruleset (rulelist_to_ruleset r) 
    \<Longrightarrow> firewall (rulelist_to_ruleset r) = firewall_list_defaultDeny r"
  (*try0*)
  (*sledgehammer!!!*)
  by (metis fw_eq_fwlist translation_id1)


end
