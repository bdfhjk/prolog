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

% Define operatior <> for the purpose of the syntax parsing.
:- op(700,xfx,[<>]).

% fill_increasing(List, N)
% Create a list with N elements equal 0,1,...,N-1.
fill_increasing([], 0).

fill_increasing([H|T], N) :-
  N > 0,
  N2 is N - 1,
  H is N - 1,
  fill_increasing(T, N2).

% fill(List, Element, Number_of_elements)
% Create a list with n elements equal E.
fill([], _, 0).

fill([H|T], X, N) :-
  N2 is N - 1,
  H = X,
  fill(T, X, N2).

% increase_nth(Id, List_in, List_out)
% increase id'th element in the integer list by one.
increase_nth(0, [H|T], [H2|T2]) :-
  H2 is H + 1,
  T = T2.

increase_nth(Id, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  increase_nth(Id2, T, T2).

% set_nth(Id, Element, List_in, List_out)
% set n-th element in a zero-based integer list to Element.
set_nth(0, E, [_|T], [H2|T2]) :-
  H2 = E,
  T = T2.

set_nth(Id, E, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  set_nth(Id2, E, T, T2).

% set_nth(Id-1dim, Id-2dim, Element, List_in, List_out)
% set [Id-1dim, Id-2dim] th element in 2 dimensional list to Element.
set_nth_2(0, NN, E, [H|T], [H2|T2]) :-
  set_nth(NN, E, H, H2),
  T = T2.

set_nth_2(Id, NN, E, [H|T], [H2|T2]) :-
  H = H2,
  Id2 is Id - 1,
  set_nth_2(Id2, NN, E, T, T2).

% get_nth_2(Id-1dim, Id-2dim, Element, List)
% get [Id-1dim, Id-2dim] th element from 2 dimensional list and save to Element.
get_nth_2(0, NN, E, [H|_]) :-
  nth0(NN, H, E).

get_nth_2(Id, NN, E, [_|T]) :-
  Id2 is Id - 1,
  get_nth_2(Id2, NN, E, T).


% ---------------------------------------------------------------------------
% ----------------------------- [PRINTING UTILS] ----------------------------
% ---------------------------------------------------------------------------


% write_processes(IdentificatorsList, InstructionList)
% write processes state according to the task specification
write_processes([],[]).

write_processes([H|T], [H2|T2]) :-
  format("    Proces ~d : ~d ~n", [H, H2]),
  write_processes(T, T2).

% write_in_section(ProcessesList)
% write processes in section numbers according to the task specification.
write_in_section([H]) :-
  format("~d.~n", [H]).

write_in_section([H|T]) :-
  format("~d, ", [H]),
  write_in_section(T).

% ---------------------------------------------------------------------------
% ----------------------------- [MAIN CODE] ---------------------------------
% ---------------------------------------------------------------------------

% ide(N, Program, Numer, Odwiedzone,
%     Kolejka, StanW, NumerW, ListaId, ListaNum, WSekcji)
% N - number of processes.
% Program - the analyzed program.
% Numer - Number of a current state.
% Odwiedzone - visited states ListaId.
% Kolejka - queue with not processed states.
% StanW - found unsafe states.
% ListaId - processes numbers in unsafe state.
% ListaNum - processes status counters in unsafe state.
% WSekcji - numbers of processes in critical section.
% BFS-like traversing all of the possible states with an unstructured order.
% This function is getting the first state from the queue,
% checking if it's an unsafe state and calling the pojde function to add all
% non visited neighbors to the queue.
ide(N, Program, Numer, _, [Stan|_], Stan, Numer, ListaId, ListaNum, WSekcji) :-
  wrong(N, Program, Stan, Numer, ListaId, ListaNum, WSekcji).

ide(N, Program, Numer, Odwiedzone, Kolejka, StanW, NumerW,
    ListaId, ListaNum, WSekcji) :-
  fill_increasing(ListaP, N),
  pojde(N, Program, Numer, Odwiedzone, Kolejka, StanW, NumerW,
   ListaId, ListaNum, WSekcji, ListaP).

% pojde(N, Program, Numer, Odwiedzone,
%     Kolejka, StanW, NumerW, ListaId, ListaNum, WSekcjil, ProcessesToProces)
% ProcessesToProces - numbers of processes to be analyzed.
% A helper function to ide. It's getting all unvisited neighbors
% of a current state and putting them into the queue.
pojde(N, Program, Numer, Odwiedzone, [Stan|T], StanW, NumerW,
   ListaId, ListaNum, WSekcji,  [Id|T2]) :-
  step(Program, Stan, Id, StanN),
  !,      % Cut -> we don't want to analyze any different path to StanN.
  (member(StanN, Odwiedzone) ->
    pojde(N, Program, Numer, Odwiedzone, [Stan|T], StanW, NumerW,
      ListaId, ListaNum, WSekcji, T2);
    pojde(N, Program, Numer, [StanN|Odwiedzone], [Stan,StanN|T],
      StanW, NumerW, ListaId, ListaNum, WSekcji, T2)).

pojde(N, Program, Numer, Odwiedzone, [_|T], StanW, NumerW,
 ListaId, ListaNum, WSekcji, []) :-
   Numer2 is Numer + 1,
   ide(N, Program, Numer2, Odwiedzone, T, StanW, NumerW, ListaId,
    ListaNum, WSekcji).

% Verificate if N processes of a program stored in file can produce an unsafe
% state.
verify(N, File) :-
  N > 0,
  set_prolog_flag(fileerrors, off),
  see(File),
  !, % Cut -> we don't want to process alternatives if we can open the file.
  read(Vars),
  read(Arrays),
  read(Program),
  seen,
  initState(Program, N, Vars, Arrays, StanP),
  (ide(N, Program, 1, [StanP], [StanP], _, NumerW, ListaId,
    ListaNum, WSekcji) ->
    format("Program jest niepoprawny: stan nr ~d nie jest bezpieczny.
Nieporawny przeplot: ~n", [NumerW]),
    write_processes(ListaId, ListaNum),
    format("Procesy w sekcji: "),
    write_in_section(WSekcji),
    !;
    format("Program jest poprawny (bezpieczny).~n")),
    !.

verify(N, File) :-
  N > 0,
  format('Error: niepoprawna nazwa pliku - ~p.~n', [File]).

verify(_, _) :-
  format("Error: parametr 0 powinien byc liczba > 0").

% Initial state creation
% initState(Program, N, Vars, Arrays, StanP)
% Program - the list of instructions in the program
% N - number of exisitng processes
% Vars - list of variables
% Arrays - list of arrays
% StanP - output state created from above variables.
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
  StanP = [C, VT, V, AT, A].

% wrong(N, Program, Stan, _, ListaId, ListaNum, WSekcji)
% Arguments have the same meaning as in ide(...)
% The function return true and fill ListaId, ListaNum, WSekcji, if
% Stan is an unsafe state.
wrong(N, Program, Stan, _, ListaId, ListaNum, WSekcji) :-
  fill_increasing(ListaP, N),
  wrong(N, Program, Stan, Num, ListaId, ListaNum, WSekcji, ListaP),
  Num > 1.    % Return true only if we have more than two processes in section.

% The wrong/8 paradigm is a helper function
% similiar to wrong/7, the last argument is the list of processes to check.
wrong(_, _, _, 0, [], [], [], []).

wrong(N, Program, [C, VT, V, AT, A], Num2, ListaId, ListaNum, WSekcji,
  [H|T]) :-
  nth0(H, C, InsNum),
  ListaId  = [H|ListaIdR],
  ListaNum = [InsNum|ListaNumR],
  (is_sekcja(Program, InsNum) ->
    wrong(N, Program, [C, VT, V, AT, A], Num, ListaIdR, ListaNumR,
      WSekcjiR, T),
    Num2 is Num + 1,
    WSekcji = [H|WSekcjiR];
    wrong(N, Program, [C, VT, V, AT, A], Num2, ListaIdR,
      ListaNumR, WSekcji, T)).

% is_sekcja(Program, H)
% Program - program to be analyzed
% H - number of instruction in program.
% return true if H-th instruction of Program is sekcja.
is_sekcja(Program, H) :-
  Program = program(ProgramList),
  nth0(H, ProgramList, sekcja).

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
