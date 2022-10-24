(*
 * SPDX-License-Identifier
 * Copyright (C) 2021-2022 Simon Fraser University (www.sfu.ca)
 *)
(*
 * Tobias Nipkow and Gerwin Klein --- Concrete Semantics (concrete-semantics.org)
 *)

section \<open>Example\<close>

theory List_Demo0 \<comment> \<open>Analogous to \<^file>\<open>../Demos/List_Demo.thy\<close> \<^file>\<open>../Demos/Complete/List_Demo.thy\<close>\<close>
imports Main
begin

datatype 'a list = Nil | Cons "'a" "'a list"

(**)

term "Nil"

declare [[names_short]] \<comment> \<open>to shorten the printing of names\<close>

term "Nil"

(**)

find_theorems \<comment> \<open>found 22076 theorem(s)\<close>

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

find_theorems \<comment> \<open>found 22086 theorem(s)\<close>

(**)

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

(**)

value "rev(Cons True (Cons False Nil))"
value "rev(Cons a (Cons b Nil))"

term "[1,2]"
term "Cons 2 (Cons 1 Nil)"
value "app (Cons (2::nat) (Cons 1 Nil)) (Cons 4 (Cons 3 Nil))"

(**)

lemma app_Nil20[simp]: "xs = app xs Nil"
  apply (induction xs)
  \<comment> \<open>\<^theory_text>\<open>sledgehammer\<close>\<close>
  apply simp
apply auto
done

lemma app_Nil2: "app xs Nil = xs"
apply (induction xs)
apply auto
done

lemma app_Nil2': "app (rev xs) Nil = rev xs"
  apply(induction xs)
  oops

lemma app_assoc[simp]: "app (app xs ys) zs = app xs (app ys zs)"
apply (induction xs)
apply auto
done

lemma rev_app[simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  thm app_Nil20[symmetric]
      app_Nil20
  apply(auto)
done

theorem rev_rev[simp]: "rev (rev xs) = xs"
  apply (induction xs)
  term "rev (rev xs) = xs"
    \<comment> \<open>\<^theory_text>\<open>apply (simp add: rev_app)\<close>\<close>
    \<comment> \<open>\<^theory_text>\<open>apply (auto simp add: rev_app)\<close>\<close>
   apply auto
  done

end
