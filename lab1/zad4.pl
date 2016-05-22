lista([]).
lista([_|_]).

pierwszy(E, L) :- L = [E|_].

ostatni(E, [E|[]]).
ostatni(E, [_|T]) :- ostatni(E, T).

element(E, [E|_]).
element(E, [_|T]) :- element(E, T).

scal([], L, L).
scal([H|T], L, [H2|T2]) :- H = H2,
                           scal(T, L, T2).

intersect([H|_], [H2|_]) :- H = H2.
intersect([H|T], [H2|T2]) :- intersect(T, [H2|T2]);
                             intersect([H|T], T2).

podziel([],[],[]).
podziel([H|T], [H2|T2], L) :- H = H2,
                              podziel(T, L, T2).

podlistaStart([], _).
podlistaStart([H|T], [H2|T2]) :-
  H = H2,
  podlistaStart(T, T2).

podlista(A, B) :- podlistaStart(A, B).
podlista(L, [_|T]) :- podlista(L, T).

podciag([], _).
podciag([H|T], [H2|T2]) :- H=H2, podciag(T, T2).
podciag(L, [_|T]) :- podciag(L, T).

wypisz([]) :- write(".").
wypisz([H|T]) :- T=[], write(H), write(".").
wypisz([H|T]) :- write(H), write(","), wypisz(T).

insert([], E, [E]).
insert([H|T], E, [H2|T2]) :- H < E, H2=H, insert(T, E, T2).
insert([H|T], E, [E|[H|T]]) :- E < H ; E = H.

insertionSort([], []).
insertionSort([H|T], P) :- insertionSort(T, W),
                           insert(W, H, P).

rowne([],[]).
rowne([_|T], [_|T2]) :- rowne(T, T2).  
srodek(L, E, [H|T]) :- H=E, rowne(L, T).
srodek(L, E, [H|T]) :- srodek([H|L], E, T).
srodek(E, L) :- srodek([], E, L).
