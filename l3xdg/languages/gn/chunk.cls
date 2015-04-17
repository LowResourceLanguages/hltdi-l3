## Nouns

^n
   vars= name nas es_sing es_plur
   desc= Sustantivos / tero
   entry= ?name?
      pos=n
      cond= !n
      lexeme=True
      dim=syn
         # Could be root, prep comp or conjunct (arg for future use)
         in= conj1 ?, conj2 ?, pcomp ?, arg ?, root ?
         out= cuan ?, adj *, det ?, poses ?
         agrs= pl  0, 1;
               poses 0, 1;
               nas ?nas?;
               pos 0
         agree= poses nas nas
         arcagree= poses, poses, 0, 1
         order= det poses cuan ^ adj
      cross=es
         dim=synsyn
            ldend= det det
            agree= ng pl
         lex=?es_sing?
         lex=?es_plur?
#   entry= ?name?
#      pos=n
#      lexeme=True
#      dim=syn
#         # Could be root, prep comp or conjunct (arg for future use)
#         in= conj1 ?, conj2 ?, pcomp ?, arg ?, root ?
#         out= cuan ?, adj *, det ?, poses ?
#         agrs= pl  1;
#               poses 0, 1;
#               nas ?nas?;
#               pos 0
#         agree= poses nas nas
#         arcagree= poses, poses, 0, 1
#         order= det poses cuan ^ adj
#      cross=es
#         dim=synsyn
#            ldend= det det
#            agree= ng pl
#         lex=?es_plur?

# Names
^nom
   vars= name es
   desc= Nombres
   entry= ?name?
      pos=n
      lexeme=True
      dim=syn
         # Could be root, prep comp or conjunct (arg for future use)
         in= conj1 ?, conj2 ?, pcomp ?, arg ?, root ?
         agrs= pl  0;
               pos 0
      cross=es
         lex=?es?

## Verbs
# areal, aireal; transitive
^vat
   vars= name es
   desc= Verbos areales transitivos / ñe'ẽtéva ...
   # not reflexive
   entry= ?name?
      pos=va
      lexeme=True
      dim=syn
         in= root !
         out= arg ?, plur ?
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 1 1 1, 1 0 1, 0 0 1;
               oj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 1 1 1, 1 0 1, 0 0 1;
               rfl  0;
               prf  0, 1;
               cont 0, 1;
               pos  1;
               tmp  0, 1
         agree= plur sj sj, arg oj oj
         order= ^ plur arg
      cross=es
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tam tmp, cont cont, sj sj, oj oj
         lex=?es?
         empty= %PRON_OJ daughter pron
         empty= no daughter neg 0, neg 1
         empty= %PROG_AUX daughter aux, cont 1
   # reflexive
   entry= ?name?
      pos=va
      lexeme=True
      dim=syn
         in= root !
         out= plur ?
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 1 1 1, 1 0 1, 0 0 1;
               oj  0 0;
               rfl  1;
               prf  0, 1;
               cont 0, 1;
               pos  1;
               tmp  0, 1
         agree= plur sj sj, arg oj oj
         order= ^ plur
      cross=es
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tam tmp, cont cont, sj sj, oj oj
         lex=?es?
         empty= %PRON_REFL daughter pron
         empty= no daughter neg 0, neg 1
         empty= %PROG_AUX daughter aux, cont 1

# areal, aireal; intransitive
^vai
   vars= name es
   desc= Verbos areales intransitivos / ñe'ẽtéva ...
   entry= ?name?
      pos=va
      lexeme=True
      dim=syn
         in= root !
         out= plur ?
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 1 1 1, 1 0 1, 0 0 1;
               oj  0 0;
               rfl  0;
               prf  0, 1;
               cont 0, 1;
               pos  1;
               tmp  0, 1
         agree= plur sj sj
         order= ^ plur
      cross=es
         dim=synsyn
            # rfl will not always agree
            agree= rfl rfl, prf prf, neg neg, tam tmp, cont cont, sj sj, oj oj
         lex=?es?
         empty= no daughter neg 0, neg 1
         empty= %PROG_AUX daughter aux, cont 1

# chendal
^vc
   vars= name es
   desc= Verbos chendales / ñe'ẽtéva ...
   entry= ?name?
      pos=vc
      lexeme=True
      dim=syn
         in= root !
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 1 1 1, 1 0 1, 0 0 1;
               oj  0 0;
               rfl  0;
               prf  0, 1;
               cont 0, 1;
               pos  1;
               tmp  0, 1
      cross=es
         dim=synsyn
            # rfl will not always agree; we probably need a separate class
            agree= rfl rfl, prf prf, neg neg, tam tmp, cont cont, sj sj, oj oj
         lex=?es?

# adjectives: either attributive or predicative (chendal)
^adj
   vars= name es
   desc= Adjetivos / teroja
   # atributivo
   entry= ?name?
      pos=adj
      dim=syn
         agrs= pos 2
         in= adj !
      cross=es
         lex=?es?
   # predicativo
   entry= ?name?
      pos=vc
      lexeme=True
      dim=syn
         in= root !
         agrs= neg  0, 1;
               sj  0 1 1, 0 0 0, 1 0 0, 0 1 0, 1 1 1, 1 0 1, 0 0 1;
               oj  0 0;
               rfl  0;
               prf  0;
               cont 0;
               pos  1;
               tmp  0, 1
      cross=es
         dim=synsyn
            agree= rfl rfl, prf prf, neg neg, tam tmp, cont cont, sj sj, oj oj
         lex=?es?
