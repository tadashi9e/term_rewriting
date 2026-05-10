% -*- mode: prolog; coding: utf-8-unix -*-

:- module(trs, [
              trs_load_rules/1,
              trs_dump_all_rules/0,
              trs_abolish_all_rules/0,
              trs_resolve/2,
              trs_resolve/4,
              trs_resolve/5,
              trs_loop/4,
              trs_loop/5,
              trs_dump_history/1,
              max_depth_of_terms/2,
              op(1200, xfx, '@'),
              op(1180, xfx, '<=>'),
              op(1180, xfx, '==>'),
              op(1105, xfy, '|'),
              op(1100, xfx, '\\'),
              op(1000, xfy, '⊢'),
              op(900, xfy, '→'),
              op(900, xfy, '⇔'),
              op(700, xfx, ':='),  % 数式処理の指示
              op(700, xfx, equals),  % 数式処理結果
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
    -> format(user_error,
              'error: ルールファイルが見つかりません: ~w~n', [File]),
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
    ; debug(trs, '~p: ~p', [read_all_rules/2, Rule]),
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
 * @param History 適用したルールのリスト
 * @param Vars ダンプ時に用いる変数名と変数のマッピング（「名前-変数」のリスト）
 */
trs_loop(InTerms, OutTerms, History, MaxSteps) :-
    trs_loop(InTerms, OutTerms, History, MaxSteps, []).
trs_loop(InTerms, OutTerms, History, MaxSteps, Vars) :-
    ( trs_rules(_) ;
      format(user_error, 'error: ルールを読み込んでいません~n', []),
      !, fail ), !,
    term_variables(InTerms, InVariables),
    % InTerms に含まれる変数を内部表現に書き換えた InTerms2 を得る
    msort(InTerms, InTerms1),
    create_variable_mapping(InVariables, InVariablesMapping),
    copy_term([InTerms1, InVariablesMapping, Vars],
              [InTerms2, InVariablesMapping2, Vars2]),
    apply_variable_mapping(InVariablesMapping2, InVariablesMapping, Vars2),
    trs_loop_aux(InTerms2, OutTerms2, History, MaxSteps, Vars),
    % OutTerms に含まれる内部表現変数を元の変数に戻す
    back_variables(OutTerms2, OutTerms).

trs_loop_aux(InTerms, OutTerms, History, MaxSteps, Vars) :-
    trs_loop_aux(InTerms, OutTerms, History, [], [], 0, MaxSteps, Vars).
trs_loop_aux(InTerms, [⊥], History, _, RA, _, _, _) :-  % ⊥(_) が出現したら停止
    contains_bottom(InTerms),
    History = RA.
trs_loop_aux(InTerms, OutTerms, History, Seen, RA, _, _, _) :-
    member(InTerms, Seen),  % 無限ループ回避
    OutTerms = InTerms,
    History = RA.
trs_loop_aux(InTerms, OutTerms, History, Seen, RA, Steps, MaxSteps, Vars) :-
    Steps < MaxSteps,
    find_rule_and_apply(InTerms, InTerms2, AppliedRule, Vars),
    msort(InTerms2, InTerms3),
    Steps1 is Steps + 1,
    trs_loop_aux(InTerms3, OutTerms, History,
                 [InTerms|Seen], [AppliedRule|RA], Steps1, MaxSteps, Vars).
trs_loop_aux(InTerms, OutTerms, History, _, RA, _, _, _) :-
    OutTerms = InTerms, History = RA.

/**
 * 内部変数管理表を作る。「変数-番号」のリスト。
 */
create_variable_mapping(InVariables, InVariablesMapping) :-
    create_variable_mapping_aux(InVariables, InVariablesMapping, 0).
create_variable_mapping_aux([], [], _).
create_variable_mapping_aux([V|Vs], [V-N|Ms], N) :-
    N1 is N + 1,
    create_variable_mapping_aux(Vs, Ms, N1).

/**
 * 内部変数管理表上の変数を、'$__trs_var__'(内部管理番号, 変数名, 変数) に変換する。
 * 変数名が与えられていない場合には、空文字列を用いる。
 */
apply_variable_mapping([], _, _).
apply_variable_mapping([V-N|Ms], [OrigV-_|OrigMs], Vars) :-
    find_var_name(Vars, V, Name),
    debug(trs, '~p: ~p',
          [apply_variable_mapping/3, '$__trs_var__'(N, Name, OrigV)]),
    V = '$__trs_var__'(N, Name, OrigV),
    apply_variable_mapping(Ms, OrigMs, Vars).

/**
 * 「変数名=変数」のリストに従って、変数に対応する名称を得る。
 */
find_var_name([], _, '').  % not found
find_var_name([Name=Var|_], V, Name) :- Var == V, !.
find_var_name([_|Vars], Var, Name) :- find_var_name(Vars, Var, Name).

/**
 * '$__trs_var__'(内部管理番号, 変数名) に変換された変数を、元の変数に戻す。
 */
back_variables(V, V2) :-
    var(V), !, V2 = V.
back_variables([T|Ts], [T2|Ts2]) :-
    !,
    back_variables(T, T2),
    back_variables(Ts, Ts2).
back_variables('$__trs_var__'(_, _, V), V) :-
    !.
back_variables(T, T2) :-
    atomic(T), T2 = T.
back_variables(T, T2) :-
    T =.. [F|Args],
    !,
    length(Args, Arity), length(Args2, Arity),
    T2 =.. [F|Args2],
    back_variables(Args, Args2).

trs_terms_to_string([], "", _) :- !.
trs_terms_to_string([T|Ts], Str, Vars) :-
    trs_term_to_string(T, S1, Vars),
    trs_terms_to_string_aux(Ts, Str, Vars, S1), !.
trs_terms_to_string(Terms, Str, Vars) :-
    format(user_error, 'failed to execute ~p~n',
           [trs_terms_to_string(Terms, Str, Vars)]).

trs_terms_to_string_aux([], Str, _, Str).
trs_terms_to_string_aux([T|Ts], Str, Vars, Ac) :-
    trs_term_to_string(T, S1, Vars),
    format(string(Ac2), '~s, ~s', [Ac, S1]),
    trs_terms_to_string_aux(Ts, Str, Vars, Ac2).
trs_terms_to_string_aux(Term, Str, Vars, Str) :-
    format(user_error, 'failed to execute ~p~n',
           [trs_terms_to_string_aux(Term, Str, Vars, Str)]).

trs_term_to_string(Term, Str, Vars) :-
    copy_term([Term, Vars], [Term2, Vars3]),
    back_variables(Term2, Term3),
    format(string(Str), '~W', [Term3, [variable_names(Vars3)]]), !.
trs_term_to_string(Term, Str, Vars) :-
    format(user_error, 'failed to execute ~p~n',
           [trs_term_to_string(Term, Str, Vars)]).

/**
 * Terms に ⊥(_) が含まれているかチェックする。
 */
contains_bottom(Terms) :-
    member(⊥(_), Terms).

/**
 * 与えられた項リストにマッチする規則を探して、
 * 適用した結果リストと適用したルール名を返す。
 */
find_rule_and_apply(InTerms, OutTerms, AppliedRule, GivenVars) :-
    trs_terms_to_string(InTerms, InStr, GivenVars),
    trs_rules(rule(RuleName, From1, From2, To, Guards, Vars)),
    apply_rule(InTerms, OutTerms, From1, From2, Guards, To),
    debug(trs, '~p: ~p',
          [find_rule_and_apply/3, (RuleName, From1, From2, To)]),
    append(GivenVars, Vars, Vars2),
    trs_term_to_string(From1, From1Str, Vars2),
    trs_term_to_string(From2, From2Str, Vars2),
    trs_term_to_string(To, ToStr, Vars2),
    trs_terms_to_string(OutTerms, OutStr, Vars2),
    AppliedRule =.. [RuleName, InStr, From1Str, From2Str, ToStr, OutStr].

/**
 * 与えられた規則にマッチする項がリストにあれば、置き換える。
 * 1. まずルールに基づくパターンマッチを行い、
 * 2. パターンが合致すれば単一化を試みる。
 * 3. 単一化に成功すればガードチェックを行い、
 * 4. 成功すればルール適用として記録する。
 */
apply_rule(InTerms, OutTerms, FromRule1, FromRule2, Guards, ToTerms) :-
    % パターンマッチ
    match_rules(FromRule1, InTerms, AppliedTerms1, RestTerms1, Unifiers1-[]),
    match_rules(FromRule2, RestTerms1, _, RestTerms2, Unifiers2-Unifiers1),
    debug(trs, '~p: ~p~n',
          [apply_rule/6,
           ['InTerms'=InTerms,
            'FromRule1'=FromRule1, 'FromRule2'=FromRule2,
            'Unifiers2'=Unifiers2]]),
    % 単一化
    execute_unify(Unifiers2),
    % ガードチェック
    check_guard(Guards),
    % 結果収集
    append(AppliedTerms1, RestTerms2, Ts),
    append(Ts, ToTerms, RawOutTerms),
    normalize_terms(RawOutTerms, OutTerms).
normalize_terms(Terms, Normalized) :-
    sort(Terms, Normalized).  % 重複除去

/**
 * 条件リストの要素が入力項リストの項にマッチするかチェックする。
 * マッチする入力項は MatchedTerms に返す。
 * マッチしなかった入力項は RestTerms に返す。
 * マッチした条件と項のペアについてリストを返し、後続処理で単一化を遅延実行する。
 */
match_rules([], Terms, [], Terms, Unifiers-Unifiers).
match_rules([P|Ps], InTerms, MatchedTerms, RestTerms, Unifiers-Unifiers0) :-
    match_rule(P, InTerms, MatchedTerm, RestTerms1, Unifiers1-Unifiers0),
    MatchedTerms = [MatchedTerm|MatchedTerms2],
    match_rules(Ps, RestTerms1, MatchedTerms2, RestTerms, Unifiers-Unifiers1).

/**
 * パターン Pattern にマッチする項が Terms にあるか調べ、あるなら
 * 候補として MatchedTerm に返す。候補以外の項は RestTerms に返す。
 * 実際の単一化は Unifier を実行するまで遅延させる。
 */
match_rule(Pattern, Terms, MatchedTerm, RestTerms, Unifiers-Unifiers0) :-
    select(MatchedTerm, Terms, RestTerms),
    pattern_match(Pattern, MatchedTerm, Unifiers-Unifiers0).
/**
 * 項 Term がパターン Pattern にマッチするか調べる。
 * Pattern と Term の内容がそれぞれ書き変わるのを防ぐため、
 * ここでは単一化を実行せず、マッチするかどうかだけをチェックする。
 */
pattern_match(Pattern, Term, Unifiers-Unifiers) :-
    atomic(Pattern), atomic(Term), !, Pattern = Term.
pattern_match(Pattern, Term, Unifiers-Unifiers0) :-
    var(Pattern), !, Unifiers = [point_to(Pattern, Term)|Unifiers0].
pattern_match(Pattern, Term, Unifiers-Unifiers0) :-
    nonvar(Pattern), nonvar(Term),
    Pattern =.. [F|Ps], Term =.. [F|Ts],
    pattern_match_aux(Ps, Ts, Unifiers-Unifiers0).

pattern_match_aux([], [], Unifiers-Unifiers).
pattern_match_aux([P|Ps], [T|Ts], Unifiers-Unifiers0) :-
    pattern_match(P, T, Unifiers1-Unifiers0),
    pattern_match_aux(Ps, Ts, Unifiers-Unifiers1).

/**
 * ルールに現れる変数 P を入力項に現れる値 T に結びつける。
 */
point_to(P, T) :- var(P), !, unify_with_occurs_check(P, T).
point_to(P, T) :- nonvar(P), !, P == T.

/**
 * パターンマッチ後の単一化処理。
 */
execute_unify(Unifiers) :- maplist(call, Unifiers).

/**
 * 単一化後のガードチェック。
 */
check_guard(Guards) :- call(Guards).

print_terms([], _).
print_terms([Term|Terms], Vars) :- print_terms(Term, Terms, Vars).
print_terms(Term, Terms, Vars) :-
    ( Terms = []
    -> format('~W', [Term, [variable_names(Vars)]])
    ; format('~W, ', [Term, [variable_names(Vars)]]),
      print_terms(Terms, Vars) ).

/**
 * 項書換え履歴を表示する。
 * @param Rules 適用したルールのリスト
 */
trs_dump_history(Rules) :-
    reverse(Rules, RevRules),
    dump_rules(RevRules).
dump_rules([]).
dump_rules([Rule|Rules]) :-
    Rule =.. [RuleName, InStr, From1Str, From2Str, ToStr, OutStr],
    ( RuleName = ''
    ; writeln(InStr),
      write('---------------- '),
      ( From1Str = "[]"
      -> format('~s ( ~s ⊢ ~s )~n',
                [RuleName, From2Str, ToStr])
      ; format('~s ( ~s \\ ~s ⊢ ~s )~n',
               [RuleName, From1Str, From2Str, ToStr]) ) ),
    ( Rules = [] -> writeln(OutStr)
    ; dump_rules(Rules) ).

depth_of_term(T, D) :-
    ( compound(T)
    -> T =.. [_|Args],
       maplist(depth_of_term, Args, DepthList),
       max_list(DepthList, Max),
       D is Max + 1
    ; D = 1 ).
max_depth_of_terms([], 0).
max_depth_of_terms([Term|Terms], Depth) :-
    depth_of_term(Term, D),
    max_depth_of_terms(Terms, RestDepth),
    Depth is max(D, RestDepth).

/**
 * 項書換えルールを適用して、項リストを解決する。
 * @param InTerms 書換え前の項リスト
 * @param OutTerms 書換え後の項リスト
 * @param MaxSteps 書換え繰り返し最大回数 (デフォルトは 100)
 * @param MaxDepth 書換え後の項の最大深さ (デフォルトは 2)
 * @param Vars ダンプ時に用いる変数名と変数のマッピング（「名前-変数」のリスト）
 */
trs_resolve(InTerms, OutTerms) :-
    trs_resolve(InTerms, OutTerms, 100, 2, []).
trs_resolve(InTerms, OutTerms, MaxSteps, MaxDepth) :-
    trs_resolve(InTerms, OutTerms, MaxSteps, MaxDepth, []).
trs_resolve(InTerms, OutTerms, MaxSteps, MaxDepth, Vars) :-
    trs_loop(InTerms, OutTerms, History, MaxSteps, Vars),
    max_depth_of_terms(OutTerms, Depth),
    Depth =< MaxDepth,
    !,
    trs_dump_history(History), nl.
