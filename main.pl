:-[aboxtbox].

%forme normale negative
nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)):- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),Y):- nnf(X,Y),!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

%concepts
concept(and(C1,C2)) :- concept(C1), concept(C2).
concept(or(C1,C2)) :- concept(C1) , concept(C2).
concept(not(C1)) :- concept(C1).
concept(all(R, C1)) :- rname(R), concept(C1).
concept(some(R, C1)) :- rname(R), concept(C1).
concept(C1) :- cnamea(C1).
concept(C1) :- cnamena(C1).
concept(C1) :- iname(C1).
concept(C1) :- rname(C1).

%autoref 
autoref(C, C).
autoref(C, and(C1, C2)) :- autoref(C, C1); autoref(C, C2),!.
autoref(C, or(C1, C2)) :- autoref(C, C1); autoref(C, C2), !.
autoref(C, not(D)) :- autoref(C, D),!.
autoref(C, some(_, C1)) :- autoref(C, C1),!.
autoref(C, all(_, C1)) :- autoref(C, C1),!.

%pas_autoref
pas_autoref(C, D) :- 
    \+ autoref(C, D).

verifier_auto_reference(Tbox) :- 
    member(equiv(Concept, Expression), Tbox),
    autoref(Concept, Expression),
    write('Erreur : Le concept complexe '), write(Concept), write(' est auto-referent.'), nl,
    halt.


%traitement TBox  T

%traitement ABox  T