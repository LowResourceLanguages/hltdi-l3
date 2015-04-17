## Nouns

# Masculine common nouns
^nm
   vars= name pl gn
   desc= Sustantivos masculinos
   # Singular
   entry= ?name?
      pos=n
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= cuan ?, preadj *, det ?, postadj *
         agree= det ng ng, postadj ng ng, preadj ng ng, cuan ng ng
         agrs= ng 0 0;
               pos  0
         order= det cuan preadj ^ postadj
      cross=gn
         dim=synsyn
            ldend= det det
            agree= pl ng
         lex=?gn?
   # Plural
   entry= ?pl?
      pos=n
      cond = l;.+s
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= cuan ?, preadj *, det ?, postadj *
         agree= det ng ng, postadj ng ng, preadj ng ng, cuan ng ng
         agrs= ng 1 0;
               pos  0
         order= det cuan preadj ^ postadj
      cross=gn
         dim=synsyn
            ldend= det det
            agree= pl ng
         lex=?gn?

# Masculine names: adjectives, quantifiers, or plural; determiner possible
# el Paraguay is different!
^nomm
   vars= name gn
   desc= Nombres masculinos
   entry= ?name?
      pos=n
      cond = U
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= det ?
         agree= det ng ng
         agrs= ng 0 0;
               pos  0
         order= det ^
         agrs= ng 0 0;
               pos  0
      cross=gn
         lex=?gn?

# Feminine common nouns
^nf
   vars= name pl gn
   desc= Sustantivos femeninos
   entry= ?name?
      pos=n
      cond = l
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= cuan ?, preadj *, det ?, postadj *
         agree= det ng ng, postadj ng ng, preadj ng ng, cuan ng ng
         agrs= ng 0 1;
               pos  0
         order= det cuan preadj ^ postadj
      cross=gn
         dim=synsyn
            ldend= det det
            agree= pl ng
         lex=?gn?
   entry= ?pl?
      pos=n
      cond = l;.+s
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= cuan ?, preadj *, det ?, postadj *
         agree= det ng ng, postadj ng ng, preadj ng ng, cuan ng ng
         agrs= ng 1 1;
               pos  0
         order= det cuan preadj ^ postadj
      cross=gn
         dim=synsyn
            ldend= det det
            agree= pl ng
         lex=?gn?

# Feminine names: adjectives, quantifiers, or plural; determiner possible
^nomf
   vars= name gn
   desc= Nombres femeninos
   entry= ?name?
      pos=n
      cond = U
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= det ?
         agree= det ng ng
         agrs= ng 0 1;
               pos  0
         order= det ^
      cross=gn
         lex=?gn?

# Plural masculine, possibly with singular translation
^nmp
   vars= name gn
   desc= Sustantivos masculinos sin forma singular
   entry= ?name?
      pos=n
      cond = l;.+s
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= cuan ?, preadj *, det ?, postadj *
         agree= det ng ng, postadj ng ng, preadj ng ng, cuan ng ng
         agrs= ng 1 0;
               pos  0
         order= det cuan preadj ^ postadj
      cross=gn
         dim=synsyn
            ldend= det det
#            agree= pl ng
         lex=?gn?

# Plural feminine, possibly with singular translation
^nfp
   vars= name gn
   desc= Sustantivos femeninos sin forma singular
   entry= ?name?
      pos=n
      cond = l;.+s
      dim=syn
         # Could be root, prep comp or conjunct
         in= conj1 ?, conj2 ?, pcomp ?, npred ?, root ?
         out= cuan ?, preadj *, det ?, postadj *
         agree= det ng ng, postadj ng ng, preadj ng ng, cuan ng ng
         agrs= ng 1 1;
               pos  0
         order= det cuan preadj ^ postadj
      cross=gn
         dim=synsyn
            ldend= det det
#            agree= pl ng
         lex=?gn?

## Adjectives

^adj4
   # Separate translations for attributive and predicative adjs
   vars= name fs mp fp gna gnv
   desc= Adjetivos con 4 formas
   # Singular masculine: attributive
   entry= ?name?
      pos=adj
      cond= .+o;l
      dim=syn
        in= preadj ?, postadj ?
        agrs= ng  0 0;
              pos 2
      cross=gn
         lex=?gna?
   entry= ?name?
      pos=adj
      cond= .+o;l
      dim=syn
         in= apred !
         agrs= ng 0 0;
               sj 1 0 0, 0 1 0, 0 0 0;
               tam 0, 1;
               neg 0, 1;
               cont 0;
               prf 0;
               pos 2
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gnv?
   # Singular feminine
   entry= ?fs?
      pos=adj
      cond= .+a;l
      dim=syn
        in= preadj ?, postadj ?
        agrs= ng  0 1;
              pos 2
      cross=gn
         lex=?gna?
   entry= ?fs?
      pos=adj
      cond= .+a;l
      dim=syn
         in= apred !
         agrs= ng 0 1;
               sj 1 0 0, 0 1 0, 0 0 0;
               tam 0, 1;
               neg 0, 1;
               cont 0;
               prf 0;
               pos 2
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gnv?
   # Plural masculine
   entry= ?mp?
      pos=adj
      cond = .+os;l
      dim=syn
        in= preadj ?, postadj ?
        agrs= ng  1 0;
              pos 2
      cross=gn
         lex=?gna?
   entry= ?mp?
      pos=adj
      cond = .+os;l
      dim=syn
         in= apred !
         agrs= ng 1 0;
               sj 1 0 1, 0 1 1, 0 0 1;
               tam 0, 1;
               neg 0, 1;
               cont 0;
               prf 0;
               pos 2
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gnv?
   # Plural feminine
   entry= ?fp?
      pos=adj
      cond = .+as;l
      dim=syn
        in= preadj ?, postadj ?
        agrs= ng  1 1;
              pos 2
      cross=gn
         lex=?gna?
   entry= ?fp?
      pos=adj
      cond = .+as;l
      dim=syn
         in= apred !
         agrs= ng 1 1;
               sj 1 0 1, 0 1 1, 0 0 1;
               tam 0, 1;
               neg 0, 1;
               cont 0;
               prf 0;
               pos 2
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gnv?

^adj2
   vars= name pl gna gnv
   desc= Adjetivos con 2 formas
   # Singular
   entry= ?name?
      pos=adj
      dim=syn
        in= preadj ?, postadj ?
        agrs= ng  0 0, 0 1;
              pos 2
      cross=gn
         lex=?gna?
   entry= ?name?
      pos=adj
      dim=syn
         in= apred !
         agrs= ng 0 0, 0 1;
               sj 1 0 0, 0 1 0, 0 0 0;
               tam 0, 1;
               neg 0, 1;
               cont 0;
               prf 0;
               pos 2
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gnv?
   # Plural
   entry= ?pl?
      pos=adj
      cond = .+s;l
      dim=syn
        in= preadj ?, postadj ?
        agrs= ng  1 0, 1 1;
              pos 2
      cross=gn
         lex=?gna?
   entry= ?pl?
      pos=adj
      cond = .+s;l
      dim=syn
         in= apred !
         agrs= ng 1 0, 1 1;
               sj 1 0 1, 0 1 1, 0 0 1;
               tam 0, 1;
               neg 0, 1;
               cont 0;
               prf 0;
               pos 2
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gnv?

## Verbs

# Intransitive verbs
^vi
   vars= name gn
   desc= Verbos intransitivos
   # finite
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn 
         in= root !
         out= neg ?, aux 0
         arcagree= neg, neg, 0, 1
         agrs= sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  -1;
               neg  0, 1;
               rfl  0;
               prf  0;
               cont 0;
               inf  0;
               fin  1;
               pos  1;
               tam  0, 1
         order= neg aux ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?
   # non-finite
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn 
         in= root !
         out= neg ?, aux +
         agree= aux sj sj, aux tam tam, aux cont cont, aux prf prf
         arcagree= neg, neg, 0, 1
         agrs= sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  -1;
               neg  0, 1;
               rfl  0;
               prf  0, 1;
               cont 0, 1;
               inf  0, 1;
               fin  0;
               pos  1;
               tam  0, 1
         order= neg aux ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?

# Transitive verbs
^vt
   vars= name gn
   desc= Verbos transitivos
   # pronoun object; finite
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn
         in= root !
         out= neg ?, pron +, aux 0
         agree= pron oj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               rfl  0;
               prf  0;
               cont 0;
               inf  0;
               fin  1;
               pos  1;
               tam  0, 1
         order= neg pron ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?
   # finite, no pronoun
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn
         in= root !
         out= neg ?, pron 0, aux 0
         agree= pron oj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  0 0 0, 0 0 1;
               rfl  0;
               prf  0;
               cont 0;
               inf  0;
               fin  1;
               pos  1;
               tam  0, 1
         order= neg ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?
   # Non-finite, pronoun
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn
         in= root !
         out= neg ?, pron +, aux +
         agree= aux sj sj, aux tam tam, aux cont cont, aux prf prf, pron oj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               rfl  0;
               prf  0, 1;
               cont 0, 1;
               inf  0, 1;
               fin  0;
               pos  1;
               tam  0, 1
         order= neg pron aux ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?
   # Non-finite, no pronoun
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn
         in= root !
         out= neg ?, pron 0, aux +
         agree= aux sj sj, aux tam tam, aux cont cont, aux prf prf, pron oj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  0 0 0, 0 0 1;
               rfl  0;
               prf  0, 1;
               cont 0, 1;
               inf  0, 1;
               fin  0;
               pos  1;
               tam  0, 1
         order= neg aux ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?

# Reflexive verbs, translated as reflexive
^vr
   vars= name gn
   desc= Verbos reflexivos que se traducen como reflexivos
   # Finite
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn 
         in= root !
         out= neg ?, pron +, aux 0
         agree= pron sj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  -1;
               rfl  1;
               prf  0;
               cont 0;
               inf  0, 1;
               fin  1;
               pos  1;
               tam  0, 1
         order= neg pron ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gn?
   # Non-finite
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn 
         in= root !
         out= neg ?, pron +, aux +
         agree= aux sj sj, aux tam tam, aux cont cont, aux prf prf, pron sj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  -1;
               rfl  1;
               prf  0, 1;
               cont 0, 1;
               inf  0, 1;
               fin  0;
               pos  1;
               tam  0, 1
         order= neg pron aux ^
      cross=gn
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tmp tam, cont cont, sj sj
         lex=?gn?

# Reflexive verbs, translated as intransitive, non-reflexive
^vri
   vars= name gn
   desc= Verbos reflexivos que se traducen como intransitivos que no son reflexivos
   # Finite
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn 
         in= root !
         out= neg ?, pron +, aux 0
         agree= pron sj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  -1;
               rfl  1;
               prf  0;
               cont 0;
               inf  0;
               fin  1;
               pos  1;
               tam  0, 1
         order= neg pron ^
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?
   # Non-finite
   entry= ?name?
      pos=v
      lexeme=True
      dim=syn 
         in= root !
         out= neg ?, pron +, aux +
         agree= aux sj sj, aux tam tam, aux cont cont, aux prf prf, pron sj pn, pron rfl rfl
         arcagree= neg, neg, 0, 1
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 0 0 1, 1 0 1;
               oj  -1;
               rfl  1;
               prf  0, 1;
               cont 0, 1;
               inf  0, 1;
               fin  0;
               pos  1;
               tam  0, 1
         order= neg pron aux ^
      cross=gn
         dim=synsyn
            agree= prf prf, neg neg, tmp tam, cont cont, sj sj, oj oj
         lex=?gn?

