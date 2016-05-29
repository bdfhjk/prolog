% Marek Bardoński
:- ensure_loaded(library(lists)).

% State = [C, VT, V, AT, A] - counters, variables, variables_names_list,
%                             arrays, arrays_names_list
% Each one is a one-dimension list except A which is a two-dimension list.

% ------------------- [UTILS] -----------------

% fill(L, E, N) - Create a list n elements equal E
fill([], _, 0).
fill([H|T], X, N) :-
  N2 is N - 1,
  H = X,
  fill(T, X, N2).

fill([H], X, 1) :- X = H.

% increase_nth(Id, L_in, L_out) - Increase id'th element in the list.
increase_nth(0, [H|T], [H2|T2]) :-
  H2 is H + 1,
  T = T2.

increase_nth(0, [H], [H2]) :-
  H2 is H + 1.

increase_nth(Id, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  increase_nth(Id2, T, T2).

% set nth element in list
set_nth(0, E, [_|T], [H2|T2]) :-
  H2 = E,
  T = T2.

set_nth(0, E, [_], [H2]) :-
  H2 = E.

set_nth(Id, E, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  set_nth(Id2, E, T, T2).

% set 2dim nth element in list
set_nth_2(0, NN, E, [H|T], [H2|T2]) :-
  set_nth(NN, E, H, H2),
  T = T2.

set_nth_2(0, NN, E, [H], [H2]) :-
  set_nth(NN, E, H, H2).

set_nth_2(Id, NN, E, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  set_nth_2(Id2, NN, E, T, T2).

% get nth element in list
get_nth(0, E, [H|_]) :-
  E = H.

get_nth(0, E, [H]) :-
  E = H.

get_nth(Id, E, [_|T]) :-
  Id2 is Id - 1,
  get_nth(Id2, E, T).

% set 2dim nth element in list
get_nth_2(0, NN, E, [H|_]) :-
  get_nth(NN, E, H).

get_nth_2(0, NN, E, [H]) :-
  get_nth(NN, E, H).

get_nth_2(Id, NN, E, [_|T]) :-
  Id2 is Id - 1,
  get_nth_2(Id2, NN, E, T).

% ------------------- [MAIN CODE] -------------------

verify(N, File) :-
  set_prolog_flag(fileerrors, off),
  see(File),
  !,                    % czerwone odcięcie (tu dozwolone)
  read(Vars),
  read(Arrays),
  read(Program),
  seen,
  initState(Program, N, Vars, Arrays, StanP),
  (not(wrong(N, Program, StanP, Przeplot)) ->
      format("Program jest poprawny (bezpieczny)");
      %proper_length(Przeplot, L),
      L = 1,
      format("Program jest niepoprawny: stan nr ~d nie jest bezpieczny. ~n
        Niepoprawny przeplot: ~n
        Proces 1: 1 ~n
        Proces 0: 1 ~n
        Procesy w sekcji: 1, 0. ~n", [L])).
/*
  write(StanP),
  nl,
  step(Program, StanP, 0, X),
  write(X),
  nl,
  step(Program, X, 0, X2),
  write(X2),
  nl,
  step(Program, X2, 0, X3),
  write(X3),
  nl,
  step(Program, X3, 0, X4),
  write(X4).
*/

verify(_, File) :-
  format('Error: niepoprawna nazwa pliku - ~p.~n', [File]).

initState(_, N, Vars, Arrays, StanP) :-
  VT = Vars,
  AT = Arrays,
  fill(C, 0, N),
  fill(V, 0, N),
  fill(A, C, N),
  StanP = [C, VT, V, AT, A].

  % Iterate every possible step to find an unsafe state.
  % verification(N, Program, StanP).

  % verification(_,_,_) :- format('Program jest poprawny (bezpieczny)').

wrong(_, Program, StanP, Wynik, Wynik) :-
  %write(StanP),
  %nl,
  unsafe_state(Program, StanP).

wrong(N, Program, StanP, Przeplot, Wynik) :-
  %nextStep = step(Program, StanP, _, Stan2),
  step(Program, StanP, _, Stan2),
  not(member(Stan2, Przeplot)),
  wrong(N, Program, Stan2, [Stan2|Przeplot], Wynik).

wrong(N, Program, StanP, Przeplot) :-
  wrong(N, Program, StanP, [StanP], Przeplot).

%evalL -Wyr, -Stan, -PrId

evalL(A < B, S, PrId) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  EA < EB.

evalL(=(A,B), S, PrId) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  EA == EB.

evalL(<>(A, B), S, PrId) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  not(EA == EB).

%eval - -Wyr, -Stan, -PrId, +Num,

eval(A + B, S, PrId, N) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  N is EA + EB.

eval(A - B, S, PrId, N) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  N is EA - EB.

eval(A * B, S, PrId, N) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  N is EA * EB.

eval(A / B, S, PrId, N) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  N is EA / EB.

eval(pid, _, PrId, N) :- N = PrId.

eval(arr(IDN, X), [C, VT, V, AT, A], PrId, N) :-
  AT = arrays(ATL),
  nth0(NVAR, ATL, IDN),
  eval(X, [C, VT, V, AT, A], PrId, EX),
  get_nth_2(NVAR, EX, N, A).

eval(VAR, [_, VT, V, _, _], _, N) :-
  VT = vars(VTL),
  not(integer(VAR)),
  nth0(NVAR, VTL, VAR),
  get_nth(NVAR, N, V).

eval(NM, _, _, N)  :-
  integer(NM),
  N = NM.

%step - Program, Stan wejściowy, id procesu, Stan wyjściowy

step(Program, [C, VT, V, AT, A], PrId, [C2, VT, V2, AT, A2]) :-
  nth0(PrId, C, InsNum),
  Program = program(ProgramList),
  AT = arrays(ATL),
  nth0(InsNum, ProgramList, assign(arr(X, Y), Z)),
  eval(Y, [C, VT, V, AT, A], PrId, EY),
  eval(Z, [C, VT, V, AT, A], PrId, EZ),
  nth0(NX, ATL, X),
  set_nth_2(NX, EY, EZ, A, A2),
  increase_nth(PrId, C, C2),
  V2=V.

step(Program, [C, VT, V, AT, A], PrId, [C2, VT, V2, AT, A2]) :-
  nth0(PrId, C, InsNum),
  Program = program(ProgramList),
  VT = vars(VTL),
  nth0(InsNum, ProgramList, assign(X, Y)),
  eval(Y, [C, VT, V, AT, A], PrId, EY),
  nth0(NX, VTL, X),
  set_nth(NX, EY, V, V2),
  increase_nth(PrId, C, C2),
  A2=A.

step(Program, [C, VT, V, AT, A], PrId, [C2, VT, V2, AT, A2]) :-
  nth0(PrId, C, InsNum),
  Program = program(ProgramList),
  nth0(InsNum, ProgramList, sekcja),
  increase_nth(PrId, C, C2),
  V2=V,
  A2=A.

step(Program, [C, VT, V, AT, A], PrId, [C2, VT, V2, AT, A2]) :-
  nth0(PrId, C, InsNum),
  Program = program(ProgramList),
  nth0(InsNum, ProgramList, goto(X)),
  EX is X - 1,
  set_nth(PrId, EX, C, C2),
  V2=V,
  A2=A.

step(Program, [C, VT, V, AT, A], PrId, [C2, VT, V2, AT, A2]) :-
  nth0(PrId, C, InsNum),
  Program = program(ProgramList),
  nth0(InsNum, ProgramList, condGoto(CE, X)),
  evalL(CE, [C, VT, V, AT, A], PrId),
  EX is X - 1,
  set_nth(PrId, EX, C, C2),
  V2=V,
  A2=A.

step(Program, [C, VT, V, AT, A], PrId, [C2, VT, V2, AT, A2]) :-
  nth0(PrId, C, InsNum),
  Program = program(ProgramList),
  nth0(InsNum, ProgramList, condGoto(_, _)),
  increase_nth(PrId, C, C2),
  V2=V,
  A2=A.

unsafe_state(Program, [C, _, _, _, _]) :-
  unsafe_state(Program, C, X),
  X > 1.

unsafe_state(Program, [H|T], X) :-
  unsafe_state(Program, T, Y),
  (is_sekcja(Program, H) -> X is Y+1; X=Y).

unsafe_state(Program, [H], X) :-
  (is_sekcja(Program, H) -> X is 1; X is 0).

is_sekcja(Program, H) :-
  Program = program(ProgramList),
  nth0(H, ProgramList, sekcja).
