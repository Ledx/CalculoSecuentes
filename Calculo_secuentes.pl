% Definicion de las operaciones lógicas
:- op(1, fx, neg).
:- op(2, xfx, or).
:- op(2, xfx, and).
:- op(2, xfx, implies).
:- op(2, xfx, dimplies).


% Reglas de transformación
trans(P,P) :- atom(P).
trans(neg F, neg R) :-
    trans(F,R).
trans(F1 or F2, R1 or R2) :-
    trans(F1,R1),
    trans(F2,R2).

trans(F1 and F2, neg(neg(R1) or neg(R2))) :-
    trans(F1,R1),
    trans(F2,R2).

trans(F1 implies F2, (neg(R1) or R2)) :-
    trans(F1,R1),
    trans(F2,R2).

trans(F1 dimplies F2, R) :-
    trans((F1 implies F2) and (F2 implies F1), R).

%%%%% Secuente inicial
secuentes([F],[F]) :-
    nl,
    write([F]),
    write(' ⊢ '),
    write([F]).

%%%%% Reglas estructurales

%%% Izquierda

% Debilitamiento
 

% Contraccion
secuentes([F1 , F2 | Gamma], Delta) :-
	union([F1 , F2], Gamma,X),    
    secuentes([X | Gamma],Delta),
    nl,
    write([F1, F2 | Gamma]),
    write(' ⊢ '),
	write([F1 | Delta]).
 
% Intercambio


%%% Derecha

% Debilitamiento
% Contraccion
secuentes(Gamma, [F1 , F2 | Delta]) :-
	union([F1 , F2], Delta,X),    
    secuentes(Gamma,[X | Delta]),
    nl,
    write([F1| Gamma]),
    write(' ⊢ '),
	write([F1, F2 | Delta]).

% Intercambio

%%%%% Reglas lógicas

%%% Izquierda

% Negacion
secuentes([neg F|Gamma],Delta) :-
    secuentes(Gamma, [F | Delta]),
    nl,
    write([neg F | Gamma]),
    write(' ⊢ '),
    write(Delta).

% Disyunción
secuentes([F1 or F2 | Gamma], Delta) :-
    secuentes([F1 | Gamma],Delta),
    secuentes([F2 | Gamma],Delta),
    nl, nl,
    write([F1 or F2 | Gamma]),
    write(' ⊢ '),
	write(Delta).

% Conjuncion
secuentes(Gamma, [F1 and F2 | Delta]) :-
    union([F1 , F2], Delta,X),
    secuentes(Gamma,X),
    nl,
    write(Gamma),
    write(' ⊢ '),
	write(F1 and F2 | Delta).


% Implicacion
secuentes([F1 implies F2 | Gamma], Delta) :-
    secuentes([F1 | Gamma],Delta),
    secuentes([F2 | Gamma],Delta),
    nl, nl,
    write([F1 implies F2 | Gamma]),
    write(' ⊢ '),
	write(Delta).
 
% Doble implicacion
secuentes([F1 dimplies F2 | Gamma], Delta) :-
    union([F1 , F2], Gamma,X),
    union([F1 , F2], Delta,Y),
    secuentes([X | Gamma],Delta),
    secuentes([Y | Gamma],Delta),
    nl, nl,
    write([F1 dimplies F2 | Gamma]),
    write(' ⊢ '),
	write(Delta).


%%% Derecha

% Negacion
secuentes(Gamma,[neg F|Delta]) :-
    secuentes([F|Gamma],Delta),
    nl,
    write(Gamma),
    write(' ⊢ '),
    write([neg F|Delta]).

% Disyunción
secuentes(Gamma, [F1 or F2 | Delta]) :-
    union([F1 , F2], Delta,X),
    secuentes(Gamma,X),
    nl,
    write(Gamma),
    write(' ⊢ '),
	write(F1 or F2 | Delta).

% Conjuncion
secuentes(Gamma, [F1 and F2 | Delta]) :-
    secuentes(Gamma,[F1 | Delta]),
    secuentes(Gamma,[F2 | Delta]),
    nl, nl,
    write(Gamma),
    write(' ⊢ '),
	write([F1 and F2 | Delta]).

% Implicacion
secuentes(Gamma, [F1 implies F2 | Delta]) :-
    union([F1], Gamma,X),
    union([F2], Delta,Y),
    secuentes(X,Y),
    nl,
    write(X),
    write(' ⊢ '),
	write(F1 implies F2 | Y).

% Doble implicacion
secuentes([F1 dimplies F2 | Gamma], Delta) :-
    secuentes([F1 | Gamma],Delta),
    secuentes([F2 | Gamma],Delta),
    nl, nl,
    write([F1 dimplies F2 | Gamma]),
    write(' ⊢ '),
	write(Delta).
