% dziecko(Dziecko, Matka, Ojciec, płeć)
dziecko(jasio, ewa, jan, ch).
dziecko(stasio, ewa, jan, ch).
dziecko(basia, anna, piotr, dz).
dziecko(jan, ela, jakub, ch).

syn(Dziecko, Matka, Ojciec) :- dziecko(Dziecko, Matka, Ojciec, ch).
corka(Dziecko, Matka, Ojciec) :- dziecko(Dziecko, Matka, Ojciec, dz).
dziecko(Dziecko, Matka, Ojciec) :- dziecko(Dziecko, Matka, Ojciec, _).
rodzic(Dziecko, Osoba) :- dziecko(Dziecko, Osoba, _); dziecko(Dziecko, _, Osoba).
wnuk(Dziecko, Osoba) :- rodzic(Dziecko, Osoba2),
                        rodzic(Osoba2, Osoba),
                        dziecko(Dziecko, _, _, ch).
