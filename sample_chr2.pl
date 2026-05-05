% -*- mode: prolog; coding: utf-8-unix -*-
/**
 * SWI-Prolog の CHR モジュールを使った積と和の計算。
 *
 * 使用方法:
 *    このファイルを consult した状態で以下のクエリを投入し、
 *    それぞれ解が得られることを確認する。
 *
 * x := 1.
 *   → x equals 1.
 * x := (1 + 2) * 3.
 *   → x equals 9.
 * x := (2+3)*(4+5).
 *   → x equals 45.
 */
:- use_module(library(chr)).

:- chr_constraint (:=)/2.  % 数式処理の指示
:- chr_constraint equals/2.  % 数式処理結果

:- op(700, xfx, ':=').  % 数式処理の指示
:- op(700, xfx, equals).  % 数式処理結果

'計算開始' @
X := A <=>
     \+ A =.. [plus|_] |
X := plus([A]).

'計算完了' @
X := plus([N]) <=>
     integer(N) |
X equals N.

'分解' @
X := plus([A+B|Y]) <=>
X := plus([A,B|Y]).

'足し算(数値)' @
X := plus([N,M|Y]) <=>
     integer(N), integer(M), sum([N,M|Y], SumAndRest) |
X := plus(SumAndRest).

% ユーティリティ述語
sum([N,M|In], Out) :-
    integer(N), integer(M), !,
    NM is N + M, sum([NM|In], Out).
sum(N, N).

'掛け算(*0)' @
X := plus([_*0|Y]) <=>
X := plus(Y).

'掛け算(*1)' @
X := plus([A*1|Y]) <=>
X := plus([A|Y]).

'掛け算(交換)' @
X := plus([N*A|Y]) <=>
     integer(N), \+ integer(A) |
X := plus([A*N|Y]).

'掛け算(帰納法)' @
X := plus([A*N|Y]) <=>
     integer(N), N > 0, N1 is N - 1 |
X := plus([A*N1,A|Y]).

'分配法則' @
X := plus([A*(B+C)|Y]) <=>
X := plus([A*B,A*C|Y]).

'分配法則' @
X := plus([(A+B)*C|Y]) <=>
X := plus([A*C,B*C|Y]).

'回転' @
X := plus([N,M|Y]) <=>
     integer(N), \+ integer(M), append(Y, [N], YandN) |
X := plus([M|YandN]).

'回転(アトムを後ろに)' @
X := plus([A,B|Y]) <=>
     atom(A), \+ integer(B), append(Y, [A], YandA) |
X := plus([B|YandA]).

'結合' @
X := plus([(A+B)|Y]) <=>
X := plus([A,B|Y]).

'結合(掛け算左寄せ)' @
X := plus([A*(B*C)|Y]) <=>
X := plus([(A*B)*C|Y]).
