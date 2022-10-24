(*
 * SPDX-License-Identifier
 * Copyright (C) 2021-2022 Simon Fraser University (www.sfu.ca)
 *)
(*
 * Tobias Nipkow and Gerwin Klein --- Concrete Semantics (concrete-semantics.org)
 *)

section \<open>Example\<close>

theory Overview_Demo0 \<comment> \<open>Analogous to \<^file>\<open>../Demos/Overview_Demo.thy\<close>\<close>
imports Main \<comment> \<open>\<^verbatim>\<open>Main\<close> is a kind of synonym to load Higher-Order Logic (HOL) libraries\<close>
begin

subsubsection \<open>Semantics of \<^theory_text>\<open>term\<close>: mainly used for syntax and type checking\<close>

text \<open>\<^cancel>\<open>term "> << 432432 dd"\<close>\<close>


subsubsection \<open>Scope of \<^emph>\<open>free\<close> variables: different commands lead to different type inference context\<close>

text \<open>\<^cancel>\<open>definition "var1 = (5 :: nat)"\<close>\<close>
term "[1,2,3::nat, 4, var1, var2]"
term "[False, True, var1, var2]"


subsubsection \<open>Overloading of numbers and list operations\<close>

term "nth [1,2,3333] 55"


subsubsection \<open>Evaluation of polymorphic value with \<^theory_text>\<open>value\<close>: the system should be able to evaluate ground types (i.e. instantiated types).\<close>

text \<open>No annotations, still polymorphic:\<close>
text \<open>\<^cancel>\<open>value "nth [1,2,3333] (1::nat)"\<close> \<comment> \<open>Error raised while preparing to evaluate the term\<close>\<close>

text \<open>Explicit instantiation:\<close>
value "nth [1,2,3333::nat] 1" \<comment> \<open>Full evaluation returning the computed value\<close>

text \<open>Explicit instantiation:\<close>
text \<open>\<^cancel>\<open>value "nth [1,2,3333::nat] 5"\<close> \<comment> \<open>Full evaluation raising an exception\<close>\<close>


subsubsection \<open>Semantics of \<^theory_text>\<open>definition\<close>: local scope inside a \<^theory_text>\<open>locale\<close> vs. globally declared\<close>

locale Z1
begin
definition "var1 = (5 :: nat)"
end

locale Z2
begin
definition "var1 = Z1.var1"
end

term "Z1.var1"
term "Z2.var1"
term "var1"


subsubsection \<open>Semantics of commands: proof mode\<close>

lemma "nth [1,2,3333] 55 = 555"
  \<comment> \<open>\<^theory_text>\<open>command1\<close>\<close>
  \<comment> \<open>\<^theory_text>\<open>command2\<close>\<close>
  \<comment> \<open>\<^theory_text>\<open>command3\<close>\<close>
  \<comment> \<open>\<^theory_text>\<open>command4\<close>\<close>
oops


subsubsection \<open>Semantics of \<^theory_text>\<open>definition\<close>: simulating mutability through \<^theory_text>\<open>consts\<close>\<close>

text \<open>Problem:\<close>

definition "five = (5 :: nat)"
lemma "five + 2 = 7"
  \<comment> \<open>Imagining this to be a very long proof to compute\<close>
  oops


text \<open>Question: now, how can we declare ``\<^theory_text>\<open>definition five = 22\<close>''?\<close>


text \<open>A possible solution:\<close>

consts maybe_five :: nat

lemma "maybe_five + 2 = 7"
  \<comment> \<open>Imagining this to be a very long proof to compute\<close>
  oops

text \<open>
\<^item> Problem: now, how can we instantiate \<^term>\<open>maybe_five\<close> to be the value we want?
\<^item> A possible solution: using \<^theory_text>\<open>overloading\<close>!
\<close>

subsubsection \<open>Semantics of \<^theory_text>\<open>consts\<close> and \<^theory_text>\<open>overloading\<close>\<close>

consts unknown_val :: 'a

overloading \<comment> \<open>This is the instantiation part\<close>
  n \<equiv> "unknown_val :: nat"
  b \<equiv> "unknown_val :: bool"
begin
  definition "n = (2 :: nat)"
  definition "b = (True :: bool)"
end

lemma "unknown_val = True"
  oops

lemma "unknown_val = (2 :: nat)"
  oops


subsubsection \<open>Semantics of \<^theory_text>\<open>consts\<close>: weakening of the type-system, i.e. bad programming practice\<close>

consts magic :: "'a \<Rightarrow> 'b" \<comment> \<open>e.g. \<^verbatim>\<open>Obj.magic\<close> in OCaml or \<^verbatim>\<open>unsafeCoerce\<close> in Haskell\<close>

text \<open>\<^cancel>\<open>term "True + False"\<close>\<close>
term "(magic True) + (magic False)"

end
