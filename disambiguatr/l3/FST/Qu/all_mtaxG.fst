###
### Quechua morphotactics: verbs, nouns/adjectives
###

-> start

### ROOT, STEM
# Each word (verb stem/root) gets a "root (or stem) POS" (rpos), v, n, or adj
start -> der       +all+
# Handle personal pronouns separately for various reasons
start -> pron      [:]            [pos=n,rpos=n,pos2=pron]
pron -> case       +pronG+

### DERIVATIONAL SUFFIXES
# verb ->
der -> vder1       [:]            [rpos=v]
# noun/adj ->
der -> nder1       [:]            [rpos=n];[rpos=adj]

### DERIVATIONAL SUFFIXES
### (not a complete list; only includes apparently most productive suffixes)
## V -> V
## no order specified so only one can appear
# reflexive
vder1 -> vder2     <ku:>          [-tr,der=[+rfl,-rcp],m=[DER=ku]]
# reciprocal
vder1 -> vder2     <naku:>        [-tr,der=[-rfl,+rcp],sb=[+pl],m=[DER=naku]]
# desiderative
vder1 -> vder2     <naya:>        [der=[+des],m=[DER=naya]]
# cislocative (movement toward the speaker)
vder1 -> vder2     <mu:>          [der=[+cisloc],m=[DER=mu]]
# causative
vder1 -> vder2     <chi:>         [der=[+caus,-rfl,-rcp],m=[DER=chi]]
# consecutive
vder1 -> vder2     <sti:>         [der=[+cnsc],m=[DER=sti]]
# limitation
vder1 -> vder2     <lla:>         [pos=v,der=[+lim],cs=None,m=[DER2=lla]]
## No initial V-> derivational suffix; nominalization still possible
## (we don't know POS yet), so include case constraints for limiter -lla:
## either der=[-lim] or cs=[+intrc | +dstr | +trm]
vder1 -> vder1a    [:]            [der=[-rfl,-rcp,-inch,-fct]]
vder1a -> vder2    [:]            [der=[-lim],cs=None];[der=[-lim]];[cs=[+dstr]];[cs=[+intrc]];[cs=[+trm]]

## N/Adj -> N/Adj
# diminutive, augmentative (can these take verbalization suffixes?)
nder1 -> nder2     <cha:>         [rpos=n,der=[+dim],m=[DER1=cha]]
nder1 -> nder2     <sapa:>        [rpos=n,der=[+aug],m=[DER1=sapa]]
# possessor: with N; can also appear *after* -kuna: wasi-kuna-yuq, wasi-yuq-kuna (Soto Ruiz, p. 141); not covered yet
nder1 -> nder2     <^yuq:>        [pos=n,rpos=n,der=[+pos],m=[DER1=yoq]]
# no first N-> derivational suffix
nder1 -> nder2     [:]            [pos=n,rpos=n,der=[-dim,-aug,-pos]];[pos=adj,rpos=adj,der=[-dim,-aug,-pos]]
# limitation (also after some case suffixes)
nder2 -> nom_sbj   <lla:>         [pos=n,rpos=n,pos2=cn,der=[+lim],cs=[-dstr,-intrc,-trm],m=[DER2=lla]]
nder2 -> case      <lla:>         [pos=adj,rpos=adj,pos2=cn,der=[+lim],cs=[-dstr,-intrc,-trm],m=[DER2=lla]]
nder2 -> case      [:]            [pos=adj,rpos=adj,pos2=cn,der=[-lim]]
nder2 -> nom_sbj   [:]            [pos=n,pos2=cn,der=[-lim]];[pos=n,pos2=cn,+pl];[pos=n,pos2=cn,cs=[+dstr]];[pos=n,pos2=cn,cs=[+intrc]];[pos=n,cs=[+trm]]

## N -> V
# realization (n->v)
nder1 -> vder2     <cha:>         [rpos=n,der=[+fct],m=[DER=cha]]
# inchoative (n/adj->v)
nder1 -> vder2     <ya:>          [rpos=n,der=[+inch],m=[DER=ya]];[rpos=adj,der=[+inch],m=[DER=ya]]

## No derivational suffix
# for rpos=adj, only case and independent suffixes possible
nder1 -> case      [:]            [pos=adj,rpos=adj,pos2=adj,der=[-dim,-aug,-pos,-lim]]
# for rpos=n, full range of noun suffixes possible
nder1 -> nom_sbj   [:]            [pos=n,rpos=n,pos2=cn,der=[-dim,-aug,-pos,-lim]]

### NOMINALIZATION (V->N), WITH NO PERSONAL SUFFIXES (SKIP TO case)
# Infinitive
vder2 -> case      [y:]           [pos=n,pos2=inf,m=[NOM=y]]
# "Agent"
vder2 -> num       [q:]           [pos=n,pos2=agt,m=[NOM=y]]

### ASPECT (only PROGRESSIVE)
# not possible for nominalized forms
vder2 -> trans     <sha:>         [pos=v,asp=[+prg],cs=None,m=[ASP=sha]]
# not nominalized here, but could be later
vder2 -> trans     [:]            [asp=[-prg]]

## TRANSITIVITY: POSSIBLE SUBJECTS AND OBJECTS
# Intransitive or transitive with 1p or 2p object
trans -> sbj       [:]            [-tr,ob=[-xpl]];[+tr,ob=[+p2,+xpl]];[+tr,ob=[+p1,+xpl]]
# Possible subjects (for verbs or nominalizations)
sbj -> obj         [:]            [sb=[+p1,-p2,-pl],ob=[-p1]];[sb=[-p1,+p2,-pl],ob=[-p2]];[sb=[-p1,-p2,-pl]];[sb=[+pl]]
# Possible objects; conventionally constrain all non-explicit objects to be 3s to prevent spurious ambiguity
obj -> obj_agr1    [:]            [ob=[+p1,-p2,-pl,+xpl]];[ob=[-p1,+p2,-pl,+xpl]];[ob=[+p1,+pl,+xpl],sb=[-p1]];[ob=[+p2,+pl,+xpl],sb=[-p2]];[ob=[-p1,-p2,-pl,-xpl]]

### OBJECT AGREEMENT 1
# (possible with nominalized suffixes spa, sqa, qti, na ??; but not covered yet)
obj_agr1 -> tam    <wa:>          [ob=[+p1,+xpl],m=[AGR1=wa]]
obj_agr1 -> tam    [:]            [ob=[-p1]]

### TENSE 1 and NOMINALIZATIONS 2 (PERMITTING SUBJ (POSSESSOR) SUFFIXES)
# Past: rqa (for generation, require the q)
tam -> sb_ob       <rqa:>           [pos=v,pos2=v,cs=None,tam=[+ps,-pp,-ft,-cd,-im],m=[TM1=rqa]]
# Past perfect
tam -> sb_ob       <sqa:>         [pos=v,pos2=v,cs=None,tam=[+pp,-ps,-ft,-cd,-im],m=[TM1=sqa]]
# Future
tam -> sb_ob       <sa:>          [pos=v,pos2=v,cs=None,tam=[+ft,-ps,-pp,-cd,-im],sb=[+p1,-p2],m=[TM1=sa]]
# Nominalizers that *can* take subject/possessor suffixes (also objects for some, but this is not supported)
tam -> nom_sbj     <na:>          [pos=n,pos2=nft,tam=[-ft,-ps,-pp,-cd,-im],ob=[-xpl],m=[TM1=na]]
tam -> nom_sbj     <spa:>         [pos=n,pos2=ger,tam=[-ft,-ps,-pp,-cd,-im],ob=[-xpl],m=[TM1=spa]]
tam -> nom_sbj     <sqa:>         [pos=n,pos2=prt,tam=[-ft,-ps,-pp,-cd,-im],ob=[-xpl],m=[TM1=sqa]]
# Ayacucho: pti
tam -> nom_sbj     <qti:>         [pos=n,pos2=sub,tam=[-ft,-ps,-pp,-cd,-im],ob=[-xpl],m=[TM1=qti]]
# This was the last chance to be nominalized, so it must be a verb
## No TAM1 prefix
# This was the last chance to be nominalized, so it must be a verb.
# TAM prefix must already have been found for pp and ps; and for ft if sb is +p1,-p2 (sa-)
# First person subject (no imperative, no future unless inclusive); second, third person subject (future, imperative possible)
tam -> tam1        [:]            [pos=v,pos2=v,cs=None,tam=[-ps,-pp]]
tam1 -> sb_ob      [:]            [tam=[-ft,-im],sb=[+p1,-p2]];[tam=[-im],sb=[+p1,+p2],ob=[-xpl]];[sb=[+p2,-p1]];[sb=[-p1,-p2]]

### POSSESSOR/SUBJECT AGREEMENT FOR NOUNS (INCLUDING NOMINALIZED VERBS)
nom_sbj -> num     >possG<

### SUBJECT-OBJECT AGREEMENT 2
sb_ob -> cond      >sb_obG<
# Short for sun(chis)man (conditional); skip over cond state; BUT NOT FOR GENERATION
# sb_ob -> indep     <swan:>        [-tr,tam=[+cd],sb=[+p1,+p2,+pl],m=[AGR_TM=swan]];[tam=[+cd],sb=[-p1,-p2],ob=[+p1,+p2,+pl,+excl],m=[AGR_TM=swan]]

### CONDITIONAL
# Conditional, except 2 intransitive (but 1p incl intransitive does have -man)
cond -> cond1      <man:>         [tam=[+cd,-ps,-ft,-pp],m=[TM2=man]]
cond1 -> indep     [:]            [ob=[+xpl]];[-tr,sb=[-p2]];[-tr,sb=[+p1,+p2,+pl]]
# No -man: either not conditional or 2 instransitive
cond -> indep      [:]            [tam=[-cd]];[-tr,tam=[+cd],sb=[+p2,-p1]]

### NUMBER: NOUNS
num -> pl_lim      <kuna:>        [+pl]
num -> case        [:]            [-pl]
# Second possible position for limitation suffix -lla
pl_lim -> case     <lla:>         [der=[+lim],+pl,m=[PL_LIM=lla]]
pl_lim -> case     [:]            [der=[-lim]]

### CASE: NOUNS AND ADJECTIVES
case  -> indep     >case<

### "INDEPENDENT" SUFFIXES: POSSIBLE WITH ALL WORDS
indep -> end       >indep<

end ->
