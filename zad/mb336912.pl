% Marek Bardoński 2016
% mb336912

% State = [C, VT, V, AT, A], where
% C = Instruction counters for each process.
% VT = Names of variables in the order of representation in V. (Environment)
% V = Variables vaules according to the VT order.
% AT = Names of arrays in the order of representation in A. (Environment)
% A = Arrays values.
% Each elemet is an one-dimension list except A which is a two-dimension list.

:- ensure_loaded(library(lists)).

% ---------------------------------------------------------------------------
% ------------------------------- [UTILS] -----------------------------------
% ---------------------------------------------------------------------------

% fill(List, Element, Number_of_elements)
% Create a list with n elements equal E.
fill([], _, 0).

fill([H|T], X, N) :-
  N2 is N - 1,
  H = X,
  fill(T, X, N2).

fill([H], X, 1) :- X = H.

% increase_nth(Id, List_in, List_out)
% increase id'th element in the integer list by one.
increase_nth(0, [H|T], [H2|T2]) :-
  H2 is H + 1,
  T = T2.

increase_nth(0, [H], [H2]) :-
  H2 is H + 1.

increase_nth(Id, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  increase_nth(Id2, T, T2).

% set_nth(Id, Element, List_in, List_out)
% set n-th element in a zero-based integer list to Element.
set_nth(0, E, [_|T], [H2|T2]) :-
  H2 = E,
  T = T2.

set_nth(0, E, [_], [H2]) :-
  H2 = E.

set_nth(Id, E, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  set_nth(Id2, E, T, T2).

% set_nth(Id-1dim, Id-2dim, Element, List_in, List_out)
% set [Id-1dim, Id-2dim] th element in 2 dimensional list to Element.
set_nth_2(0, NN, E, [H|T], [H2|T2]) :-
  set_nth(NN, E, H, H2),
  T = T2.

set_nth_2(0, NN, E, [H], [H2]) :-
  set_nth(NN, E, H, H2).

set_nth_2(Id, NN, E, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  set_nth_2(Id2, NN, E, T, T2).

% get_nth_2(Id-1dim, Id-2dim, Element, List)
% get [Id-1dim, Id-2dim] th element from 2 dimensional list and save to Element.
get_nth_2(0, NN, E, [H|_]) :-
  nth0(NN, H, E).

get_nth_2(0, NN, E, [H]) :-
  nth0(NN, H, E).

get_nth_2(Id, NN, E, [_|T]) :-
  Id2 is Id - 1,
  get_nth_2(Id2, NN, E, T).


% ---------------------------------------------------------------------------
% ----------------------------- [MAIN CODE] ---------------------------------
% ---------------------------------------------------------------------------

write_processes_number([H]) :-
  format("~d.~n", H).

write_processes_number([H|T]) :-
  format("~d, ", H),
  write_processes_number(T).

write_processes_number([]) :-
  format("~n").

write_processes([H|T], A) :-
  format("    Proces ~d : ~d ~n", [A, H]),
  B is A + 1,
  write_processes(T, B).

write_processes([], _).

write_process_state() :-
  b_getval(uncorrect_state, [C, _, _, _, _]),
  write_processes(C, 0),
  write("Procesy w sekcji: "),
  b_getval(unsafe_processes, X),
  write_processes_number(X).

verify(N, File) :-
  N > 0,
  set_prolog_flag(fileerrors, off),
  see(File),
  !,                    % czerwone odcięcie (tu dozwolone)
  read(Vars),
  read(Arrays),
  read(Program),
  seen,
  initState(Program, N, Vars, Arrays, StanP),
  (not(wrong(N, Program, StanP, _)) ->
      format("Program jest poprawny (bezpieczny)");
      b_getval(stan_number, L),
      format(
"Program jest niepoprawny: stan nr ~d nie jest bezpieczny. ~n
Niepoprawny przeplot: ~n", [L]),
      write_process_state()).

verify(N, File) :-
  N > 0,
  format('Error: niepoprawna nazwa pliku - ~p.~n', [File]).

verify(_, _) :-
  format("Error: parametr 0 powinien byc liczba > 0").

initState(_, N, Vars, Arrays, StanP) :-
  VT = Vars,
  AT = Arrays,
  VT = vars(VTL),
  AT = arrays(ATL),
  proper_length(VTL, VTS),
  proper_length(ATL, ATS),
  fill(C, 0, N),
  fill(V, 0, VTS),
  fill(AN, 0, N),
  fill(A, AN, ATS),
  nb_setval(visited, []),
  nb_setval(stan_number, 0),
  StanP = [C, VT, V, AT, A].

wrong(_, Program, StanP, Wynik, Wynik) :-
  unsafe_state(Program, StanP),
  nb_setval(uncorrect_state, StanP).

wrong(N, Program, StanP, Przeplot, Wynik) :-
  %nextStep = step(Program, StanP, _, Stan2),
  step(Program, StanP, _, Stan2),
  %write(StanP), write(' -> '), write(Stan2), nl,
  b_getval(visited, X),
  b_getval(stan_number, Y),
  not(memberchk(Stan2, X)),
  X2 = [Stan2|X],
  Y2 is Y + 1,
  nb_setval(stan_number, Y2),
  nb_setval(visited, X2),
  wrong(N, Program, Stan2, [Stan2|Przeplot], Wynik).

wrong(N, Program, StanP, Przeplot) :-
  wrong(N, Program, StanP, [StanP], Przeplot).


unsafe_state(Program, [C, _, _, _, _]) :-
  nb_setval(unsafe_processes, []),
  unsafe_state(Program, C, X, 0),
  X > 1.

  unsafe_state(Program, [H|T], X, A) :-
    B is A + 1,
    unsafe_state(Program, T, Y, B),
    (is_sekcja(Program, H) ->
       b_getval(unsafe_processes, L),
       nb_setval(unsafe_processes, [A|L]),
       X is Y+1;
     X=Y).

unsafe_state(Program, [H], X, A) :-
  (is_sekcja(Program, H) ->
    b_getval(unsafe_processes, L),
    nb_setval(unsafe_processes, [A|L]),
    X is 1;
    X is 0).

  is_sekcja(Program, H) :-
    Program = program(ProgramList),
    nth0(H, ProgramList, sekcja).

%evalL -Wyr, -Stan, -PrId

% ---------------------------------------------------------------------------
% --------------------- [LOGIC EXPRESSION EVALUATION] -----------------------
% ---------------------------------------------------------------------------

% evalL(W, S, PrId)
% Evaluate expression W according to state S and process id PrId.
evalL(A < B, S, PrId) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  EA < EB.

evalL(=(A,B), S, PrId) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  EA =:= EB.

evalL(<>(A, B), S, PrId) :-
  eval(A, S, PrId, EA),
  eval(B, S, PrId, EB),
  not(EA =:= EB).

% ---------------------------------------------------------------------------
% --------------------- [ARITHMETIC EXPRESSION EVALUATION] ------------------
% ---------------------------------------------------------------------------

% eval(W, S, PrId, Num)
% Evaluate expression W according to state S and process id PrId to Num.
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
  nth0(NVAR, V, N).

eval(NM, _, _, N)  :-
  integer(NM),
  N = NM.


% ---------------------------------------------------------------------------
% ----------------------- [INSTRUCTIONS EVALUATION] -------------------------
% ---------------------------------------------------------------------------

% step(Program, S_in, IdPr, S_out)
% Perform a single step of Program in process IdPr from state S_in to S_out

% After reaching the end of the program, return to the start.
step(Program, [C, VT, V, AT, A], PrId, [C2, VT, V2, AT, A2]) :-
  nth0(PrId, C, InsNum),
  Program = program(ProgramList),
  proper_length(ProgramList, L),
  InsNum >= L,
  set_nth(PrId, 0, C, C2),
  V2=V,
  A2=A.

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
  (evalL(CE, [C, VT, V, AT, A], PrId) ->
    EX is X - 1,
    set_nth(PrId, EX, C, C2);
    increase_nth(PrId, C, C2)),
  V2=V,
  A2=A.
