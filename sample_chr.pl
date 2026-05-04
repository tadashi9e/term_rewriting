% -*- mode: prolog; coding: utf-8-unix -*-
/**
 * SWI-Prolog の CHR モジュールを使った例。
 *
 * 使用方法:
 *    このファイルを consult した状態で以下のクエリを投入し、
 *    それぞれ解が得られることを確認する。
 *
 * a → b, b → c, c → d.
 * A → B, B → C, C → D.
 * (a ∨ b) ∧ (¬a ∨ c) ∧ (¬b ∨ c) ∧ ¬c.
 * (A ∨ B) ∧ (¬A ∨ C) ∧ (¬B ∨ C) ∧ ¬C.
 * (a → b) ∧ (b → c) ∧ (c → d) ∧ a ∧ ¬d.
 * (A → B) ∧ (B → C) ∧ (C → D) ∧ A ∧ ¬D.
 * (a ∨ b ∨ c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ ¬c.
 * (A ∨ B ∨ C) ∧ (¬A ∨ B) ∧ (¬B ∨ C) ∧ ¬C.
 * (p ∨ q) ∧ (¬p ∨ r) ∧ (¬q ∨ r) ∧ ¬r.
 * (P ∨ Q) ∧ (¬P ∨ R) ∧ (¬Q ∨ R) ∧ ¬R.
 * (p ∨ q) ∧ (¬ p ∨ q) ∧ (p ∨ ¬ q) ∧ (¬ p ∨ ¬ q).
 * (P ∨ Q) ∧ (¬ P ∨ Q) ∧ (P ∨ ¬ Q) ∧ (¬ P ∨ ¬ Q).
 * (p ∨ q) ∧ (¬ p ∨ ¬ q).
 * (P ∨ Q) ∧ (¬ P ∨ ¬ Q).
 */

:- use_module(library(chr)).

%:- op(1200, xfx, '@').
%:- op(1180, xfx, '<=>').
%:- op(1180, xfx, '==>').
:- op(1000, xfy, '⊢').
:- op(900, xfy, '→').
:- op(900, xfy, '⇔').
:- op(550, yfx, '∨').
:- op(550, yfx, '∧').
:- op(150, fy, '¬').

:- chr_constraint (⊥)/1.
:- chr_constraint (→)/2.
:- chr_constraint (∨)/2.
:- chr_constraint (∧)/2.
:- chr_constraint (¬)/1.
:- chr_constraint assume/1.

ド_モルガンの法則_de_morgan_law @ ¬(P ∨ Q) <=> ¬ P ∧ ¬ Q.
ド_モルガンの法則_de_morgan_law @ ¬(P ∧ Q) <=> ¬ P ∨ ¬ Q.

remove_assume @ assume(P) <=> compound(P) | P.

分配 @
P ∨ (Q ∧ R) <=> \+ P = Q | P ∨ Q, P ∨ R.

吸収 @
P ∨ (P ∧ _) <=> assume(P).

'前件肯定_modus_ponens' @
assume(P), (P → Q) <=> assume(Q).

%後件否定_modus_tollens @
%¬ Q, (P → Q) <=> ¬ Q, ¬ P.

後件否定_modus_tollens @
¬ Q \ (P → Q) <=> ¬ P.

否定導入_not @
P → ⊥ <=> ¬ P.

否定導入_not @
P → ⊥(_) <=> ¬ P.

二重否定の除去_double_negative_elimination @
¬ ¬ P <=> assume(P).

選言三段論法_disjunctive_syllogism @
¬ P \ (P ∨ Q) <=> assume(Q).
選言三段論法_disjunctive_syllogism2 @
¬ P \ (Q ∨ P) <=> assume(Q).

仮言三段論法_hypothetical_syllogism @
(P → Q), (Q → R) <=> (P → R).

論理和の消去_disjunction_elimination @
(P → Q), (R → Q), (P ∨ R) <=> assume(Q).

論理和の消去_disjunction_elimination @
(P ∨ P) <=> assume(P).

論理積の消去_conjunction_elimination @
(P ∧ Q) <=> assume(P), assume(Q).

論理積の消去_conjunction_elimination @
assume(P), assume(P) <=> assume(P).

矛盾律_contradiction @
assume(A), ¬ A <=> ⊥(A).

導出_resolution @
L ∨ P, ¬ L ∨ Q <=>
        L \= P, L \= ¬ P, ¬ L \= P, L \= Q, L \= ¬ Q, ¬ L \= Q |
        P ∨ Q.
