%==================================================================================
% Amharic Word constituent analysis Prolog code segment
%
% root_affix.pl 
%
% This is a Prolog function combining the learned rules from root.pl
% and affix.pl to form a combined rule taht accepts a word and identify its
% Stem, Root, Vowel Template, Prefix and Suffix for further processing!
% October 10, 2011
%By: Wondwossen Mulugeta  ywondisho@gmail.com
%==================================================================================


constituent(Word,Stem,Root,Template, Prefix,Suffix):-
	affix(Word,Stem,Prefix,Suffix),
	root(Stem, Root, Template).

root(A, B, V):-root_temp(A, B, ['I', 'I']), V=['I','I'],!.
root(A, B, V):-root_temp(A, B, ['I', e]),  V=['I',e],!.
root(A, B, V):-root_temp(A, B, [e, e]),  V=[e,e],!.

root_temp(A,R,V):-             
	   permutation(A,B),   
	   append(R,V,B). 

affix(A, B, ['I'], [a, l, e, h, u]):-set_affix(A, B, ['I'], [a, l, e, h, u]), !.
affix(A, B, [], ['E']):-set_affix(A, B, [], ['E']), !.
affix(A, B, [l, 'I'], []):-set_affix(A, B, [l, 'I'], []), !.
affix(A, B, ['I'], []):-set_affix(A, B, ['I'], []), !.
affix(A, B, [t, e], [k, u]):-set_affix(A, B, [t, e], [k, u]), !.

%% split  will spilt a list into two possible substrings
split([X,Y|Z],[X],[Y|Z]).
split([X|Y],[X|Z],W) :- split(Y,Z,W).


%% set_affix(W1, X, P1, S1) is true if 
%%       P1+X+S1 = W1  

set_affix(W1,X,P1,[]):-     %identify P1 as suffix of W1 
    split(W1,P1,X).

set_affix(W1,X,[],S1):-     %identify S1 as suffix of W1
    split(W1,X,S1).

set_affix(W1,_,P1,S2):-
    split(W1,P1,S2).

set_affix(W1,X,P1,S1):-
    split(W1,P1,W11),
    split(W11,X,S1).
