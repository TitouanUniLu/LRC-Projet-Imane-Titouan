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

verifier_concept() :-
    setof(E, equiv(_, E), Concepts),
    member(C, Concepts),
    \+ concept(C),
    write('Invalid concept: '), write(C), nl,!, fail. % La fonction s'arrête dès qu'elle trouve un concept invalide
verifier_concept :- 
    write('Verification: Syntax and semantics are correct.'), nl.

%autoref 
autoref(C, C) :- cnamea(C), !.
autoref(C, C) :- cnamena(C), !. 
autoref(C, D) :- cnamena(D), equiv(D, D1), autoref(C, D1),!.
autoref(C, and(C1, C2)) :- autoref(C, C1); autoref(C, C2),!.
autoref(C, or(C1, C2)) :- autoref(C, C1); autoref(C, C2),!.
autoref(C, not(D)) :- autoref(C, D),!.
autoref(C, some(_, C1)) :- autoref(C, C1),!.
autoref(C, all(_, C1)) :- autoref(C, C1),!.

%pas_autoref
pas_autoref([(C, E)|R]) :- 
    \+ autoref(C, E), pas_autoref(R).
pas_autoref([]).


verifier_auto_reference() :- 
    setof((C, E), equiv(C, E), Tbox), 
    (pas_autoref(Tbox), write('This Tbox is not auto-referent.'), nl,!
    ;   write('Erreur : auto-reference detected '),fail), nl.
% Si aucune auto-référence n'est détectée, elle affiche un message indiquant que la T-Box n'est pas auto-référente.
% Sinon, elle affiche un message d'erreur indiquant que l'auto-référence a été détectée et provoque un échec. 

%remplacement récursif
remplace(C, C) :- 
    cnamea(C), !. % Vérifie si C est un concept atomique
 

remplace(C, E) :- % Si C est équivalent à un autre concept D on récupère l'équivalent D de C et remplacer par son équivalent 
    equiv(C, D), remplace(D, E), !. 

remplace(not(C1), not(C2)) :- % Si C1 est une négation remplacer par la négation
    remplace(C1, C2), !. 

remplace(or(C1, C2), or(D1, D2)) :- % Si C disjonction (or), remplacer par première disjonction puis deuxième disjonction
    remplace(C1, D1), remplace(C2, D2), !. 

remplace(and(C1, C2), and(D1, D2)) :- % pareil pour and
    remplace(C1, D1), remplace(C2, D2), !. 

remplace(some(R, C1), some(R, C2)) :- % meme logique
    remplace(C1, C2), !. 

remplace(all(R, C1), all(R, C2)) :- 
    remplace(C1, C2), 
    !. 

%traitement TBox  T
traitement_Tbox([],[]).
traitement_Tbox([(C1,C2)|O],[(C1,C3)|O1]) :- remplace(C2,C4), nnf(C4,C3), traitement_Tbox(O,O1), !. %call recursif pour le reste

%traitement ABox  T
traitement_Abox([],[]).
traitement_Abox([(I,C)|O],[(I,C1)|O1]) :- remplace(C,C2), nnf(C2,C1), traitement_Abox(O,O1), !.
traitement_Abox([(I1,I2,R)|O],[(I1,I2,R)|O1]) :- traitement_Abox(O,O1), !.

% TESTS POUR VOIR SI CA MARCHE ON PEUT ENLEVER APRES%
test1 :-
    traitement_Tbox([(sculpteur, some(aCree, sculpture)), (auteur, some(aEcrit, livre))], ResultatTbox),
    writeln('Resultat du traitement de la TBox :'),
    writeln(ResultatTbox).

test2 :-  
    traitement_Tbox([(sculpteur, some(aCree, sculpture)), (auteur, some(aEcrit, livre))], ResultatTbox),
    traitement_Abox([(michelAnge, personne), (david, sculpture), (sonnets, livre)], ResultatAbox),
    writeln('Resultat du traitement de la TBox :'), writeln(ResultatTbox),
    writeln('Resultat du traitement de la ABox :'), writeln(ResultatAbox).

traitement_Tbox_Abox() :- 
    setof((C, E), equiv(C, E), Tbox), 
    setof((I, C), inst(I, C), AboxC),
    setof((I1, I2, R), instR(I1, I2, R), AboxR),
    traitement_Tbox(Tbox, ResultatTbox),
    traitement_Abox(AboxC, ResultatAboxC),
    traitement_Abox(AboxR, ResultatAboxR),
    writeln('Resultat du traitement de la TBox :'), writeln(ResultatTbox),
    writeln('Resultat du traitement de la ABox :'), writeln(ResultatAboxC), writeln(ResultatAboxR).

% exécute tous les vérifications et traitements
partie1 :- verifier_concept(), verifier_auto_reference(), traitement_Tbox_Abox().