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

listTBox(Tbox) :- setof((C, E), equiv(C, E), Tbox).
listAboxInst(AboxInst):- setof((I1, I2), inst(I1, I2), AboxInst).
listAboxRole(AboxRole):- setof((I1, I2, R), instR(I1, I2, R), AboxRole).





%Implémentation de la partie 1 

%concepts
concept(and(C1,C2)) :- concept(C1), concept(C2).
concept(or(C1,C2)) :- concept(C1) , concept(C2).
concept(not(C1)) :- concept(C1).
concept(all(R, C1)) :- rname(R), concept(C1).
concept(some(R, C1)) :- rname(R), concept(C1).
concept(C1) :- cnamea(C1).
concept(C1) :- cnamena(C1).
concept(C,E) :- cnamena(C), concept(E).

concept(I,C):- iname(I), cnamea(C).
concept(I,C):- iname(I), cnamena(C).
concept(I1, I2, R):- iname(I1), iname(I2), rname(R).

verifier_concept(Tbox, AboxInst, AboxRole) :-
    listTBox(Tbox),
    listAboxInst(AboxInst),
    listAboxRole(AboxRole),
    (member((C,E), Tbox), \+ concept(C,E), 
     write('Concept invalide dans : '), write((C,E)), nl, !, fail
    ; member((I,C), AboxInst), \+ concept(I,C), 
      write('Concept invalide dans : '), write((I,C)), nl, !, fail
    ; member((I1,I2,R), AboxRole), \+ concept(I1,I2,R), 
      write('Concept invalide dans : '), write((I1,I2,R)), nl, !, fail
    ; true), 
    write("Verification : Syntaxe et semantique correctes"), nl.

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


verifier_auto_reference(Tbox) :- 
    listTBox(Tbox),
    (pas_autoref(Tbox), write("Cette T-Box n\'est pas auto-referente."), nl,!
    ;   write("Erreur : Auto-reference detectee. "),fail), nl.
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


traitement_Tbox_Abox(Tbox, AboxInst, AboxRole) :-
    listTBox(Tbox),
    listAboxInst(AboxInst),
    listAboxRole(AboxRole),
    traitement_Tbox(Tbox, ResultatTbox),
    traitement_Abox(AboxInst, ResultatAboxInst),
    traitement_Abox(AboxRole, ResultatAboxRole),
    write('Resultat du traitement de la TBox :'), nl, writeln(ResultatTbox), nl,
    write('Resultat du traitement de la ABox :'), nl, writeln(ResultatAboxInst), writeln(ResultatAboxRole), nl.

% exécute tous les vérifications et traitements (partie1)
premiere_etape(Tbox, Abi, Abr) :- verifier_concept(Tbox, Abi, Abr), verifier_auto_reference(Tbox), traitement_Tbox_Abox(Tbox, Abi, Abr).






%Implémentation de la partie 2 

programme :-
    premiere_etape(Tbox, Abi, Abr),
    deuxieme_etape(Abi, Abi1, Tbox),
    troisieme_etape(Abi1, Abr).

deuxieme_etape(Abi, Abi1, Tbox) :-
    saisie_et_traitement_prop_a_demontrer(Abi, Abi1, Tbox).

saisie_et_traitement_prop_a_demontrer(Abi, Abi1, Tbox) :-
    nl, write('Entrez le numéro du type de proposition que vous voulez démontrer :'), nl,
    write('1. Une instance donnée appartient à un concept donné.'), nl,
    write('2. Deux concepts n"ont pas d"éléments en commun (ils ont une intersection vide).'), nl,
    read(R), suite(R, Abi, Abi1, Tbox).

suite(1, Abi, Abi1, Tbox) :-
    acquisition_prop_type1(Abi, Abi1, Tbox), !.
suite(2, Abi, Abi1, Tbox) :-
    acquisition_prop_type2(Abi, Abi1, Tbox), !.
suite(_, Abi, Abi1, Tbox) :-
    nl, write('Cette réponse est incorrecte.'), nl,
    saisie_et_traitement_prop_a_demontrer(Abi, Abi1, Tbox).

% Saisie de l'identifiant d'une instance
entrerInstance(I) :-
    nl, write('Entrez l\'identifiant de l\'instance (I) : '), nl,
    read(I),
    iname(I) -> true ; 
        write('Erreur : Instance invalide. Veuillez entrer une instance valide.'), nl,
        entrerInstance(I).

% Saisie de l'identifiant d'un concept
entrerConcept(C) :-
    nl, write('Entrez l\'expression du concept (C) : '), nl,
    read(C),
    concept(C) -> true ; 
        write('Erreur : Concept invalide. Veuillez entrer un concept valide.'), nl,
        entrerConcept(C).

acquisition_prop_type1(Abi, [(I,C1)|Abi], _) :-
    entrerInstance(I),
    entrerConcept(C),
    remplace(not(C), NC), nnf(NC, C1),
    nl, write('Proposition ajoutee avec succes : '), write(inst(I, C1)), nl.

acquisition_prop_type2(Abi, Abi1, _) :-
    entrerConcept(C1),
    entrerConcept(C2),
    remplace(C1, CA1),
    remplace(C2, CA2),
    nnf(and(CA1, CA2), NCA),
    genere(Nom),
    concat(Abi, [(Nom, NCA)], Abi1),
    nl, write('Proposition ajoutee avec succes : '), write(concept_inter_vide(C1, C2)), nl.   



%Implémentation de la partie 3



%Trie les assertions de la Abox étendue dans différentes listes selon leur type

tri_Abox([],[],[],[],[],[]).
tri_Abox([(I,some(R,C))|Abi],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls) :- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,all(R,C))|Abi],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls) :- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,and(C1,C2))|Abi],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls) :- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,or(C1,C2))|Abi],Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls) :- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,C)|Abi],Lie,Lpt,Li,Lu,[(I,C)|Ls]) :- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.


troisieme_etape(Abi1, Abr):- true.






%Utils

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

compteur(1).

genere(Nom) :- 
    compteur(V),nombre(V,L1),
    concat([105,110,115,116],L1,L2),
    V1 is V+1,
    dynamic(compteur/1),
    retract(compteur(V)),
    dynamic(compteur/1),
    assert(compteur(V1)),nl,nl,nl,
    name(Nom,L2).

nombre(0,[]).
nombre(X,L1) :-
    R is (X mod 10),
    Q is ((X-R)//10),
    chiffre_car(R,R1),
    char_code(R1,R2),
    nombre(Q,L),
    concat(L,[R2],L1).
chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').