% dziecko(Dziecko, Matka, Ojciec)
dziecko(jasio, ewa, jan).
dziecko(stasio, ewa, jan).
dziecko(basia, anna, piotr).
dziecko(jan, ela, jakub).

ojciec(X,Y) :- dziecko(X,_,Y).
matka(X,Y) :- dziecko(_,X,Y).
rodzic(X,Y) :- ojciec(X,Y); matka(X,Y).
babcia(X,Y) :- matka(Z,Y), matka(X,Z).
babcia(X,Y) :- ojciec(Z,Y), matka(X,Z).
wnuk(X,Y) :- rodzic(Y,Z), rodzic(Z, X).
przodek(X,Y) :- rodzic(X,Y); wnuk(X,Y).
