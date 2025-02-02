% Definicion de las operaciones lógicas
:- op(1, fx, neg).
:- op(2, xfx, or).
:- op(2, xfx, and).
:- op(2, xfx, implies).
:- op(2, xfx, dimplies).
:- op(1, fx, para_todos).
:- op(1, fx, existe).
% Definicion de operadores de programa
:- op(1, fx, if).
:- op(1, fx, else).
:- op(1, fx, for).
:- op(1, fx, rv).

% Predicado principal para calculo de las trayectorias basicas




trayectorias_basicas([if C | Tail], R) :-
    acceso_elemento(C, 0, E1),
    write(E1),
    inserta_final(E1, [], L1),
    inserta_final(neg(E1),[], L2),
    nl,
    trayectorias_basicas([L1|Tail],[]),
    trayectorias_basicas([L2|Tail],[]).

trayectorias_basicas([for C | Tail], R) :-
    nl,
    acceso_elemento(C, 0, E1),
    inserta_final(E1, [], L),
    acceso_elemento(C, 1, E2),
    acceso_elemento(C, 2, E3),
    inserta_final(E2, L, L1),
    inserta_final(neg(E2), L, L2),
    %inserta_final(E3,L1, L1),
    %inserta_final(E3,L, L2),
    nl,
    trayectorias_basicas([L1|Tail],[]),
    trayectorias_basicas([L2|Tail],[]).

trayectorias_basicas([rv C | Tail], R) :-
    write(C),
    nl,
    inserta_final(C, [], L),
    write(Tail).

trayectorias_basicas([Head|Tail],R) :-
    nl,
    write(Head),
    inserta_final(Head, R, L),
    trayectorias_basicas(Tail,L),
    nl.

inicia_calculo_trayectorias(P,R) :-
    write('Recibo programa:'),
    nl,
    write(P),
    nl,
    write('Las trayectorias basicas son:'),
    nl,
    trayectorias_basicas(P,R).
    %write(R).


% Predicados auxiliares
inserta_principio(X, L, [X|L]).

inserta_final(X, [], [X]).
inserta_final(X, [Head|Tail], [Head|Rest]) :- 
    inserta_final(X, Tail, Rest).

acceso_elemento([Head|_], 0, Head).  
acceso_elemento([_|Tail], I, E) :- 
    I > 0, 
    NI is I - 1, 
    acceso_elemento(Tail, NI, E).

remover_elemento(X, [X|Tail], Tail).
remover_elemento(X, [Head|Tail], [Head|Rest]) :- 
    remover_elemento(X, Tail, Rest).


%inicia_calculo_trayectorias([(0=<l) and (u<a),m:=8,a>b,for([i=l,i=<u, rv(true)]),rv(false),pos],[]).
%inicia_calculo_trayectorias([(0=<l) and (u<a),m:=8,a>b,for([i=l,i=<u, rv(true)]),rv(false),if([a=e,rv(true)]),pos],[]).
%inicia_calculo_trayectorias([(0=<l) and (u<a),m:=8,a>b,for([i=l,i=<u,if([a=e,rv(true)])],rv(false)),rv() dimplies (aj := e)],[]).
%inicia_calculo_trayectorias([true,if([(x > 0) and (y>0),rv(x+y)]),rv(0),rv(x+y)],[]).

