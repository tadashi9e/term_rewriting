% -*- mode: prolog; coding: utf-8-unix -*-

:- module(trs, [
              trs_load_rules/1,
              trs_dump_all_rules/0,
              trs_abolish_all_rules/0,
              trs_resolve/2,
              trs_resolve/4,
              trs_loop/4,
              trs_dump_history/2,
              max_depth_of_terms/2,
              op(1200, xfx, '@'),
              op(1180, xfx, '<=>'),
              op(1180, xfx, '==>'),
              op(1105, xfy, '|'),
              op(1000, xfy, '⊢'),
              op(900, xfy, '→'),
              op(900, xfy, '⇔'),
              op(550, yfx, '∨'),
              op(550, yfx, '∧'),
              op(150, fy, '¬')
          ]).

% ----------------------------------------------------------------------
% 項書換えルール設定
% ----------------------------------------------------------------------

:- dynamic trs_rules/1.

/**
 * ルールファイルの内容を読み込む。
 * @param 読み込み対象のルールファイル
 * @throw io_error ファイルが開けない場合
 * @example trs_load_rules('rules/propositional.rule').
 * @see trs_abolish_all_rules/0
 */
trs_load_rules(File) :-
    ( \+ exists_file(File)
    -> format(user_error, 'error: ルールファイルが見つかりません: ~w~n', [File]),
       !, fail
    ; true
    ),
    open(File, read, Stream, [encoding(utf8)]),
    read_all_rules(Stream, Rules),
    close(Stream), !,
    assert_rules(Rules).

read_all_rules(Stream, Rules) :-
    read_term(Stream, Rule,
              [variable_names(Vars),
               singletons(Singletons)]),
    report_singletons(Rule, Vars, Singletons),
    ( Rule = end_of_file -> Rules = []
    ; debug(trs, ':~p', Rule),
      parse_rule(Rule, Vars, ParsedRule),
      (ParsedRule = [] -> Rules2 = Rules
      ; Rules = [ParsedRule | Rules2]),
      read_all_rules(Stream, Rules2) ).

report_singletons(_, _, []) :- !.
report_singletons(Term, Vars,
                  Singletons) :-
    Singletons = [Name=_ | RestSingletons],
    atom_chars(Name, SCs),
    ( SCs = ['_'|_] -> true
    ; term_string(Term, Str, [variable_names(Vars)]),
      format(user_error, 'warning: Singleton ~w in ~s.~n',
             [Name, Str]) ),
    report_singletons(Term, Vars, RestSingletons).

parse_rule((RuleName @ From <=> Guards | To), Vars, ParsedRule) :-
    tuple_to_list(From, FromList),
    tuple_to_list(To, ToList),
    ParsedRule = rule(RuleName, FromList, ToList, Guards, Vars).
parse_rule(RuleName @ From <=> To, Vars, ParsedRule) :-
    tuple_to_list(From, FromList),
    tuple_to_list(To, ToList),
    ParsedRule = rule(RuleName, FromList, ToList, true, Vars).
parse_rule(abolish(P), _, []) :-
    abolish(P), !.
parse_rule(assert(P), _, []) :-
    assertz(P), !.
parse_rule(Rule, Vars, []) :-
    term_string(Rule, Str, [variable_names(Vars)]),
    format(user_error, 'failed to parse (ignored): ~s~n', [Str]).

tuple_to_list(A, [A]) :- var(A).
tuple_to_list((A,B), [A|Rest]) :-
    !,
    tuple_to_list(B, Rest).
tuple_to_list(A, [A]).

assert_rules([]) :- !.
assert_rules([Rule|Rules]) :-
    assertz(trs_rules(Rule)),
    assert_rules(Rules).

/**
 * 読み込み済みの全てのルールをダンプする。
 */
trs_dump_all_rules :-
    findall(Rule, trs_rules(Rule), RuleBag),
    dump_all_rules(RuleBag).
dump_all_rules([]).
dump_all_rules([rule(RuleName, FromList, ToList, Guard, Vars)|RuleBag]) :-
    term_string((RuleName @ FromList <=> Guard | ToList), Str,
                [variable_names(Vars)]),
    writeln(Str),
    dump_all_rules(RuleBag).

/**
* 読み込み済みの全てのルールを消去する。
 */
trs_abolish_all_rules :-
    abolish(trs_rules/1).

% ----------------------------------------------------------------------
% 項書換えエンジン
% ----------------------------------------------------------------------
/**
 * 項書換えルールを適用して、項リストを解決する。
 * @param InTerms 書換え前の項リスト
 * @param OutTerms 書換え後の項リスト
 * @param Rules 適用したルールのリスト
 */
trs_loop(InTerms, OutTerms, Rules, MaxSteps) :-
    ( trs_rules(_) ;
      format(user_error, 'error: ルールを読み込んでいません~n', []),
      !, fail ), !,
    sort(InTerms, InTerms2),
    trs_loop_aux(InTerms2, OutTerms, Rules, MaxSteps).
trs_loop_aux(InTerms, OutTerms, Rules, MaxSteps) :-
    trs_loop_aux(InTerms, OutTerms, Rules, [], [], 0, MaxSteps).
trs_loop_aux(InTerms, [⊥], Rules, _, RA, _, _) :-  % ⊥(_) が出現したら停止
    contains_bottom(InTerms),
    Rules = RA.
trs_loop_aux(InTerms, OutTerms, Rules, Seen, RA, _, _) :-
    member(InTerms, Seen),  % 無限ループ回避
    OutTerms = InTerms,
    Rules = RA.
trs_loop_aux(InTerms, OutTerms, Rules, Seen, RA, Steps, MaxSteps) :-
    Steps < MaxSteps,
    find_rule_and_apply(InTerms, InTerms2, Rule),
    sort(InTerms2, InTerms3),
    Steps1 is Steps + 1,
    trs_loop_aux(InTerms3, OutTerms, Rules,
                 [InTerms|Seen], [Rule|RA], Steps1, MaxSteps).
trs_loop_aux(InTerms, OutTerms, Rules, _, RA, _, _) :-
    OutTerms = InTerms, Rules = RA.

/**
 * Terms に ⊥(_) が含まれているかチェックする。
 */
contains_bottom(Terms) :-
    member(⊥(_), Terms).

/**
 * 与えられた項リストにマッチする規則を探して、
 * 適用した結果リストと適用したルール名を返す。
 */
find_rule_and_apply(InTerms, OutTerms, Rule) :-
    trs_rules(rule(RuleName, From, To, Guards, Vars)),
    apply_rule(InTerms, OutTerms, From, Guards, To),
    debug(trs, ':~p', (RuleName, From, To)),
    term_string(From, FromStr, [variable_names(Vars)]),
    term_string(To, ToStr, [variable_names(Vars)]),
    Rule =.. [RuleName, FromStr, ToStr, OutTerms].

/**
 * 与えられた規則にマッチする項がリストにあれば、置き換える。
 */
apply_rule(InTerms, OutTerms, FromRule, Guards, ToRule) :-
    replace_list(FromRule, InTerms, AppliedTerms),
    check_guard(Guards),
    append(AppliedTerms, ToRule, RawOutTerms),
    %\+ tautology_clause(RawOutTerms),  % トートロジー除去
    normalize_terms(RawOutTerms, OutTerms).
normalize_terms(Terms, Normalized) :-
    sort(Terms, Normalized).  % 重複除去

/**
 * トートロジー
 */
tautology_clause(Clause) :-
    member(L, Clause),
    neg(L, NL),
    member(NL, Clause).
neg(¬A, A).
neg(A, ¬A).

/**
 * 与えられた規則にマッチする項があれば単一化した上でリストから除去する
 */
replace_list([], Terms, Terms).
replace_list([M|Ms], InTerms, OutTerms) :-
    ( select(M, InTerms, Ts)
    ; commutative_law(M, W), select(W, InTerms, Ts)),
    replace_list(Ms, Ts, OutTerms).

% 交換法則
commutative_law(A ∨ B, B ∨ A).
commutative_law(A ∧ B, B ∧ A).
commutative_law(A ⇔ B, B ⇔ A).

check_guard(Guards) :- call(Guards).

print_terms([]).
print_terms([Term|Terms]) :- print_terms(Term, Terms).
print_terms(Term, Terms) :-
    ( Terms = [] -> write(Term)
    ; write(Term), write(', '), print_terms(Terms)
    ).

/**
 * 項書換え履歴を表示する。
 * @param InTerms 項書換え開始前の項リスト
 * @param Rules 適用したルールのリスト
 */
trs_dump_history(InTerms, Rules) :-
    print_terms(InTerms), nl,
    reverse(Rules, RevRules),
    dump_rules(RevRules).
dump_rules([]).
dump_rules([Rule|Rules]) :-
    Rule =.. [RuleName, From, To, OutTerms],
    write('---------------- '), write(RuleName), write(' ( '),
    write(From), write(' ⊢ '), write(To), write(' )'), nl,
    print_terms(OutTerms), nl,
    dump_rules(Rules).

depth_of_term(T, D) :-
    ( compound(T)
    -> T =.. [_|Args],
       maplist(depth_of_term, Args, DepthList),
       max_list(DepthList, Max),
       D is Max + 1
    ; D = 1 ).
max_depth_of_terms(Terms, Depth) :-
    max_depth_of_terms(Terms, Depth, 0).
max_depth_of_terms([], Depth, Depth).
max_depth_of_terms([Term|Terms], Depth, Ac) :-
    depth_of_term(Term, D),
    ( D < Ac -> max_depth_of_terms(Terms, Depth, Ac)
    ; max_depth_of_terms(Terms, Depth, D)
    ).

/**
 * 項書換えルールを適用して、項リストを解決する。
 * @param InTerms 書換え前の項リスト
 * @param OutTerms 書換え後の項リスト
 * @param MaxSteps 書換え繰り返し最大回数 (デフォルトは 100)
 * @param MaxDepth 書換え後の項の最大深さ (デフォルトは 2)
 */
trs_resolve(InTerms, OutTerms) :-
    trs_resolve(InTerms, OutTerms, 100, 2).
trs_resolve(InTerms, OutTerms, MaxSteps, MaxDepth) :-
    trs_loop(InTerms, OutTerms, Rules, MaxSteps),
    max_depth_of_terms(OutTerms, Depth),
    Depth =< MaxDepth,
    !,
    trs_dump_history(InTerms, Rules), nl.
