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
              op(1100, xfx, '\\'),
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

parse_rule((RuleName @ Rule), Vars, ParsedRule) :-
    parse_rule_aux(RuleName, Rule, Vars, ParsedRule).
parse_rule(abolish(P), _, []) :-
    abolish(P), !.
parse_rule(assert(P), _, []) :-
    assertz(P), !.
parse_rule(Rule, Vars, ParsedRule) :-
    parse_rule_aux('', Rule, Vars, ParsedRule).
parse_rule_aux(RuleName, (From1 \ From2 <=> Guards | To),
               Vars, ParsedRule) :-
    !,
    tuple_to_list(From1, From1List),
    tuple_to_list(From2, From2List),
    tuple_to_list(To, ToList),
    ParsedRule = rule(RuleName, From1List, From2List, ToList, Guards, Vars).
parse_rule_aux(RuleName, (From <=> Guards | To), Vars, ParsedRule) :-
    tuple_to_list(From, FromList),
    tuple_to_list(To, ToList),
    !,
    ParsedRule = rule(RuleName, [], FromList, ToList, Guards, Vars).
parse_rule_aux(RuleName, (From1 \ From2 <=> To), Vars, ParsedRule) :-
    tuple_to_list(From1, From1List),
    tuple_to_list(From2, From2List),
    tuple_to_list(To, ToList),
    !,
    ParsedRule = rule(RuleName, From1List, From2List, ToList, true, Vars).
parse_rule_aux(RuleName, (From <=> To), Vars, ParsedRule) :-
    tuple_to_list(From, FromList),
    tuple_to_list(To, ToList),
    !,
    ParsedRule = rule(RuleName, [], FromList, ToList, true, Vars).
parse_rule_aux(RuleName, Rule, Vars, _) :-
    term_string(Rule, Str, [variable_names(Vars)]),
    format(user_error, 'failed to parse (ignored): ~s ~s~n',
           [RuleName, Str]).

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
dump_all_rules(
    [rule(RuleName, FromList1, FromList2, ToList, Guard, Vars)|RuleBag]) :-
    ( FromList1 = []
    -> term_string((RuleName @ FromList2 <=> Guard | ToList),
                   Str, [variable_names(Vars)])
    ; term_string((RuleName @ FromList1 \ FromList2 <=> Guard | ToList),
                  Str, [variable_names(Vars)]) ),
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
    trs_rules(rule(RuleName, From1, From2, To, Guards, Vars)),
    apply_rule(InTerms, OutTerms, From1, From2, Guards, To),
    debug(trs, ':~p', (RuleName, From1, From2, To)),
    term_string(From1, From1Str, [variable_names(Vars)]),
    term_string(From2, From2Str, [variable_names(Vars)]),
    term_string(To, ToStr, [variable_names(Vars)]),
    Rule =.. [RuleName, From1Str, From2Str, ToStr, OutTerms].

/**
 * 与えられた規則にマッチする項がリストにあれば、置き換える。
 */
apply_rule(InTerms, OutTerms, FromRule1, FromRule2, Guards, ToRule) :-
    match_list(FromRule1, InTerms),
    replace_list(FromRule2, InTerms, AppliedTerms),
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
 * 条件リストの各項が入力項リストに含まれているかチェックする。
 * （CHRの条件チェック。項は消費されない）
 */
match_list([], _).
match_list([M|Ms], Terms) :-
    member(M, Terms),
    match_list(Ms, Terms).

/**
 * 与えられた規則にマッチする項を単一化した上でリストから除去する。
 * （CHRの削除。書き換え前の各項を順に削除）
 */
replace_list([], Terms, Terms).
replace_list([M|Ms], InTerms, OutTerms) :-
    select(M, InTerms, Ts),
    replace_list(Ms, Ts, OutTerms).

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
    %print_terms(InTerms), nl,
    reverse(Rules, RevRules),
    dump_rules(InTerms, RevRules).
dump_rules(InTerms, []) :-
    print_terms(InTerms), nl.
dump_rules(InTerms, [Rule|Rules]) :-
    Rule =.. [RuleName, From1, From2, To, OutTerms],
    ( RuleName = ''
    ; print_terms(InTerms), nl,
      write('---------------- '), write(RuleName), write(' ( '),
      ( From1 = "[]"
      -> write(From2)
      ; write(From1), write(' \\ '), write(From2) ),
      write(' ⊢ '), write(To), write(' )'), nl ),
    dump_rules(OutTerms, Rules).

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
