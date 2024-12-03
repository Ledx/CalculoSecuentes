% Definicion de las operaciones lógicas
:- op(1, fx, neg).
:- op(2, xfx, or).
:- op(2, xfx, and).
:- op(2, xfx, implica).
:- op(2, xfx, dimplica).
:- op(1, fx, para_todo).
:- op(1, fx, existe).

% Constantes a utilizar
constante(A).
constante(B).
constante(C).

variable(X) :- atom(X).


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

trans(F1 implica F2, (neg(R1) or R2)) :-
    trans(F1,R1),
    trans(F2,R2).

trans(F1 dimplica F2, R) :-
    trans((F1 implica F2) and (F2 implica F1), R).

%%%%% Secuente inicial
secuentes([F],[F]) :-
    nl,
    write([F]),
    write(' ⊢ '),
    write([F]).

%%%%% Reglas estructurales

%%% Izquierda

% Debilitamiento
secuentes([F|Gamma], Delta) :-
    secuentes(Gamma, Delta),
    secuentes([F|Gamma], Delta).

% Contraccion
secuentes([F, F|Gamma] :- Delta).

 
% Intercambio


%%% Derecha

% Debilitamiento
secuentes(Gamma, [F1 | Delta]) :-
    secuentes(Gamma, Delta),
    secuentes(Gamma, [F1 | Delta]).

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
secuentes([F1 implica F2 | Gamma], Delta) :-
    secuentes([F1 | Gamma],Delta),
    secuentes([F2 | Gamma],Delta),
    nl, nl,
    write([F1 implica F2 | Gamma]),
    write(' ⊢ '),
	write(Delta).
 
% Doble implicacion
secuentes([F1 dimplica F2 | Gamma], Delta) :-
    union([F1 , F2], Gamma,X),
    union([F1 , F2], Delta,Y),
    secuentes([X | Gamma],Delta),
    secuentes([Y | Gamma],Delta),
    nl, nl,
    write([F1 dimplica F2 | Gamma]),
    write(' ⊢ '),
	write(Delta).

% Existencial (Restrictivo)
secuentes([para_todo F|Gamma], Delta) :- 
    secuentes([F|Gamma],Delta),
    constante(C),
    F = [H|T],
    reemplazar(F, H, C, Delta),
    secuentes(Gamma, Delta).


% Universal (Libre)
secuentes( [existe F|Gamma],Delta) :- 
    secuentes([F | Gamma], Delta),
    F = [H|T],
	\+ variable(H),
    constante(C),
    reemplazar(F, H, C, Delta),
    secuentes(Gamma, Delta).


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
secuentes(Gamma, [F1 implica F2 | Delta]) :-
    union([F1], Gamma,X),
    union([F2], Delta,Y),
    secuentes(X,Y),
    nl,
    write(X),
    write(' ⊢ '),
	write(F1 implica F2 | Y).

% Doble implicacion
secuentes([F1 dimplica F2 | Gamma], Delta) :-
    secuentes([F1 | Gamma],Delta),
    secuentes([F2 | Gamma],Delta),
    nl, nl,
    write([F1 dimplica F2 | Gamma]),
    write(' ⊢ '),
	write(Delta).


% Existencial (Libre)
secuentes(Gamma, [existe F|Delta]) :- 
    secuentes(Gamma, [F | Delta]),
    constante(C),
    F = [H|T],
    reemplazar(F, H, C, Delta),
    secuentes(Gamma, Delta).


% Universal (Restrictivo)
secuentes(Gamma, [para_todo F|Delta]) :- 
    secuentes(Gamma, [F | Delta]),
    F = [H|T],
	\+ variable(H),
    constante(C),
    reemplazar(F, H, C, Delta),
    secuentes(Gamma, Delta).

%%%%% Auxiliares

% Reemplaza la variable Viejo en una lista con Nuevo, el resultado se guarda en NuevaLista.
% reemplazar(+Lista, +Viejo, +Nuevo, -NuevaLista)

% Caso base, si es una lista vacia, el resultado es una lista vacia.
reemplazar([], _, _, []). 

% Caso reemplazo: Si H coincide con Viejo, este es reemplazado por Nuevo y el predicado continua con T.
reemplazar([Viejo|T], Viejo, Nuevo, [Nuevo|NT]) :-
    reemplazar(T, Viejo, Nuevo, NT). % Remmplazamos en T.

% Manejo de listas anidadas: Si H no es Viejo, el predicado revisa si es una lista. Si lo es se procesa H recursivamente; si no, H queda igual.
reemplazar([H|T], Viejo, Nuevo, [NH|NT]) :-
    H \= Viejo, % Conservamos H si no es Viejo.
    reemplazar(H, Viejo, Nuevo, NH), % Verificamos si H es una lista.
    reemplazar(T, Viejo, Nuevo, NT).

% Caso de reemplazo atomico: Si el elementop es Viejo, se reemplaza con Nuevo. Si no es Viejo o una lista, se deja como estaba.
reemplazar(H, Viejo, Nuevo, Nuevo) :- 
    H == Viejo. % Reemplazamos H si es Viejo

reemplazar(H, Viejo, Nuevo, H) :- 
    H \= Viejo, % Conservamos H si no es Viejo
    \+ is_list(H). % Revisamos si H es una lista

