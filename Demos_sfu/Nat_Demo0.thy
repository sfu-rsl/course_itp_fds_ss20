(*
 * SPDX-License-Identifier
 * Copyright (C) 2021-2022 Simon Fraser University (www.sfu.ca)
 *)

section \<open>Example\<close>

theory Nat_Demo0
  imports Main \<comment> \<open>Besides \<^verbatim>\<open>Main\<close>, \<^verbatim>\<open>Pure\<close> is the minimal theory that can be imported.\<close>
begin

subsection \<open>Semantics of object-logics: Pure\<close>

text \<open>For instance, importing \<^verbatim>\<open>Pure\<close> does not provide the type \<^typ>\<open>nat\<close>.\<close>
term "0 + 5"
term "1 :: nat"


subsection \<open>Semantics of \<^theory_text>\<open>datatype\<close>\<close>

subsubsection \<open>\<^theory_text>\<open>datatype\<close>\<close>

term Zero \<comment> \<open>The term \<^theory_text>\<open>Zero\<close> is free before the declaration\<close>

datatype natural = Zero ("10")
                 | One ("20")
                 | Successor natural ("S _" [81] 80)

term Zero \<comment> \<open>The term \<^theory_text>\<open>Zero\<close> is a constant after the declaration\<close>

term "10" \<comment> \<open>Warning: abbreviation masking, this is \<^theory_text>\<open>Zero\<close>!\<close>

term "Zero :: natural"
term "Successor Zero :: natural"
term "Successor (Successor Zero) :: natural"
term "Successor (Successor (Successor Zero)) :: natural"

subsubsection \<open>In comparison with \<^theory_text>\<open>definition\<close>\<close>

term Zero' \<comment> \<open>The term \<^theory_text>\<open>Zero'\<close> is free before the declaration\<close>
definition "Zero' = 555"
term Zero' \<comment> \<open>The term \<^theory_text>\<open>Zero'\<close> is a constant after the declaration\<close>


subsection \<open>Semantics of \<^theory_text>\<open>fun\<close>\<close>

term "add 87 44" \<comment> \<open>The term \<^theory_text>\<open>add\<close> is free before the declaration\<close>
term "add () 44" \<comment> \<open>The term \<^theory_text>\<open>add\<close> is free before the declaration\<close>
term "add z two" \<comment> \<open>The term \<^theory_text>\<open>add\<close> is free before the declaration\<close>
term "add 1 2 False" \<comment> \<open>The term \<^theory_text>\<open>add\<close> is free before the declaration\<close>

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0       n = n" |
"add m (Suc n) = Suc (add m n)"

term "add :: nat \<Rightarrow> nat \<Rightarrow> nat" \<comment> \<open>The term \<^theory_text>\<open>add\<close> is a constant after the declaration\<close>
term "add 123 :: nat \<Rightarrow> nat" \<comment> \<open>Example of partial application\<close>

text \<open>
Note: the equation
\<^term>\<open>add (Suc m) n = Suc (add m n)\<close> was missing in
the definition of \<^const>\<open>add\<close>, making this evaluation
fails: \<^cancel>\<open>value "add 2 3"\<close>.
\<close>

end
