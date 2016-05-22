
nat(0).
nat(X) :- Y is X-1,
          nat(Y).
minus(X, Y, Z)  :- Z is X - Y.
plus(X, Y, Z) :- Z is X + Y.
fib(1,1).
fib(1,2).
fib(X,K) :- K > 1,
            A is K-1,
            B is K-2,
            fib(C,A),
            fib(D,B),
            X is C + D.
