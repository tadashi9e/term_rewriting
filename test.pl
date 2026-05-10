% -*- mode: prolog; coding: utf-8-unix -*-

:- use_module(trs).

setup :-
    trs_abolish_all_rules,
    trs_load_rules('rules/propositional.rule'),
    trs_load_rules('rules/de_morgan.rule'),
    trs_load_rules('rules/calc.rule'),
    trs_dump_all_rules.

test :-
    Tests = [test1, test2, test3, test4, test5, test6, test7, test8, test9,
             test11, test12, test13, test14, test15,
             test16, test17, test18, test19,
             test_calc1, test_calc2, test_calc3, test_calc4, test_calc5,
             test_calc6, test_calc7, test_calc8,test_calc9, test_calc10,
             test_calc11],
    foldl(run_test, Tests, ok_ng(0,0), ok_ng(OK,NG)),
    length(Tests, Total),
    writeln('############################################################'),
    format('#    Total: ~w, OK: ~w, NG: ~w~n', [Total, OK, NG]),
    writeln('############################################################').

run_test(Test, ok_ng(OK0,NG0), ok_ng(OK,NG)) :-
    writeln('############################################################'),
    format('#    ~w~n', Test),
    writeln('############################################################'),
    (   call(Test)
    ->  OK is OK0 + 1,
        NG = NG0,
        writeln('OK')
    ;   OK = OK0,
        NG is NG0 + 1,
        writeln('NG')
    ).

test1 :-
    trs_resolve([a → b, b → c, c → d], OutTerms), !,
    writeln(OutTerms),
    OutTerms == [a→d].
test11 :-
    Vars = ['A'=A, 'B'=B, 'C'=C, 'D'=D],
    trs_resolve([A → B, B → C, C → D], OutTerms, 100, 10, Vars), !,
    format('~W~n', [OutTerms, [variable_names(Vars)]]),
    OutTerms == [A→D].
test2 :-
    trs_resolve([ (a ∨ b)
                  ∧ (¬a ∨ c)
                  ∧ (¬b ∨ c)
                  ∧ (¬c) ], OutTerms), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test12 :-
    Vars = ['A'=A, 'B'=B, 'C'=C],
    trs_resolve([ (A ∨ B)
                  ∧ (¬A ∨ C)
                  ∧ (¬B ∨ C)
                  ∧ (¬C) ], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test3 :-
    trs_resolve([ (a → b)
                  ∧ (b → c)
                  ∧ (c → d)
                  ∧ a
                  ∧ (¬d) ], OutTerms), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test13 :-
    Vars = ['A'=A, 'B'=B, 'C'=C, 'D'=D],
    trs_resolve([ (A → B)
                  ∧ (B → C)
                  ∧ (C → D)
                  ∧ A
                  ∧ (¬D) ], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test4 :-
    trs_resolve([ (a ∨ b)
                  ∧ (¬a ∨ b)
                  ∧ (a ∨ ¬b)
                  ∧ (¬a ∨ ¬b) ], OutTerms), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test14 :-
    Vars = ['A'=A, 'B'=B],
    trs_resolve([ (A ∨ B)
                  ∧ (¬A ∨ B)
                  ∧ (A ∨ ¬B)
                  ∧ (¬A ∨ ¬B) ], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test5 :-
    trs_resolve([ (a ∨ b ∨ c)
                  ∧ (¬a ∨ b)
                  ∧ (¬b ∨ c)
                  ∧ (¬c) ], OutTerms), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test15 :-
    Vars = ['A'=A, 'B'=B, 'C'=C],
    trs_resolve([ (A ∨ B ∨ C)
                  ∧ (¬A ∨ B)
                  ∧ (¬B ∨ C)
                  ∧ (¬C) ], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test6 :-
    trs_resolve([p ∨ q,
                 ¬p ∨ r,
                 ¬q ∨ r,
                 ¬r], OutTerms), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test16 :-
    Vars = ['P'=P, 'Q'=Q, 'R'=R],
    trs_resolve([P ∨ Q,
                 ¬P ∨ R,
                 ¬Q ∨ R,
                 ¬R], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test7 :-
    trs_resolve([p ∨ q,
                 ¬ p ∨ q,
                 p ∨ ¬ q,
                 ¬ p ∨ ¬ q], OutTerms), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test17 :-
    Vars = ['P'=P, 'Q'=Q],
    trs_resolve([P ∨ Q,
                 ¬ P ∨ Q,
                 P ∨ ¬ Q,
                 ¬ P ∨ ¬ Q], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [⊥].
test8 :-
    trs_resolve([p ∨ q,
                 ¬ p ∨ r,
                 ¬ q ∨ s,
                 ¬ r ∨ ¬ s], OutTerms, 5, 5), !,
    writeln(OutTerms),
    OutTerms == [s ∨ ¬ s].
test18 :-
    Vars = ['P'=P, 'Q'=Q, 'R'=R, 'S'=S],
    trs_resolve([P ∨ Q,
                 ¬ P ∨ R,
                 ¬ Q ∨ S,
                 ¬ R ∨ ¬ S], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [S ∨ ¬ S].
test9 :-
    trs_resolve([ p ∨ q,
                  ¬ p ∨ ¬ q ], OutTerms, 5, 5), !,
    writeln(OutTerms),
    OutTerms == [q∨ ¬q].
test19 :-
    Vars = ['P'=P, 'Q'=Q],
    trs_resolve([ P ∨ Q,
                  ¬ P ∨ ¬ Q ], OutTerms, 100, 10, Vars), !,
    writeln(OutTerms),
    OutTerms == [Q∨ ¬Q].

test_calc1 :-
    trs_resolve([x := 1], OutTerms), !,
    OutTerms == [x equals 1].
test_calc2 :-
    trs_resolve([x := 1+2], OutTerms), !,
    OutTerms == [x equals 3].
test_calc3 :-
    trs_resolve([x := 1+2+3], OutTerms), !,
    OutTerms == [x equals 6].
test_calc4 :-
    trs_resolve([x := 2*3*4], OutTerms), !,
    OutTerms == [x equals 24].
test_calc5 :-
    trs_resolve([x := 2*(3*2)], OutTerms), !,
    OutTerms == [x equals 12].
test_calc6 :-
    trs_resolve([x := 2*(2*(2*2))], OutTerms), !,
    OutTerms == [x equals 16].
test_calc7 :-
    trs_resolve([x := 2*(3+4)], OutTerms), !,
    OutTerms == [x equals 14].
test_calc8 :-
    trs_resolve([x := (3+4*2)*2], OutTerms), !,
    OutTerms == [x equals 22].
test_calc9 :-
    trs_resolve([x := 2*(3+4*2)], OutTerms), !,
    OutTerms == [x equals 22].
test_calc10 :-
    trs_resolve([x := (2+3)*(4+5)], OutTerms), !,
    OutTerms == [x equals 45].
test_calc11 :-
    trs_resolve([x := 3*4*5], OutTerms), !,
    OutTerms == [x equals 60].
