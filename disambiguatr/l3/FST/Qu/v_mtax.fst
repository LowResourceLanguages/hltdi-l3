###
### Quechua verb morphotactics
###

-> start

### ROOT, STEM
start -> drv1     +v+

### MISCELLANEOUS DERIVATIONAL SUFFIXES
### (nowhere near a complete list, and the order is not specified)
# reflexive
drv1 -> nom_asp      <ku:>          [-tr,der=[+rfl,-rcp],m=[DER=ku]]
# reciprocal
drv1 -> nom_asp      <naku:>        [-tr,der=[-rfl,+rcp],sb=[+pl],m=[DER=naku]]
# causative
drv1 -> nom_asp      <chi:>         [der=[+caus,-rfl,-rcp],m=[DER=chi]]
# consecutive
drv1 -> nom_asp      <sti:>         [der=[+cnsc],m=[DER=sti]]
# limitation (also after some case suffixes)
drv1 -> nom_asp      <lla:>         [der=[+lim],cs=[-dstr,-intn,-trm],m=[DER2=lla]]
drv1 -> nom_asp      [:]            [der=[-rfl,-rcp,-lim]];[der=[-rfl,-rcp],cs=[+dstr]];[der=[-rfl,-rcp],cs=[+intn]];[der=[-rfl,-rcp],cs=[+trm]]

### NOMINALIZATION WITH NO PERSONAL SUFFIXES
# Infinitive
nom_asp -> case      [y:]           [pos=n,pos2=inf,m=[NOM=y]]
# "Agent"
nom_asp -> case      [q:]           [pos=n,pos2=agt,m=[NOM=y]]
## PROGRESSIVE
# not possible for nominalized forms
nom_asp -> trans     <sha:>         [pos=v,asp=[+prg],m=[ASP=sha]]
# not nominalized
nom_asp -> trans     [:]            [asp=[-prg]]

## TRANSITIVITY: POSSIBLE SUBJECTS AND OBJECTS
# Intransitive or transitive with 1p or 2p object
trans -> sbj         [:]            [-tr,ob=[-xpl]];[+tr,ob=[+p2,+xpl]];[+tr,ob=[+p1,+xpl]]
# Possible subjects
sbj -> obj           [:]            [sb=[+p1,-p2,-pl],ob=[-p1]];[sb=[-p1,+p2,-pl],ob=[-p2]];[sb=[-p1,-p2,-pl]];[sb=[+pl]]
# Possible objects; conventionally constrain all non-explicit objects to be 3s to prevent spurious ambiguity
obj -> obj_agr1      [:]            [ob=[+p1,-p2,-pl,+xpl]];[ob=[-p1,+p2,-pl,+xpl]];[ob=[+p1,+pl,+xpl],sb=[-p1]];[ob=[+p2,+pl,+xpl],sb=[-p2]];[ob=[-p1,-p2,-pl,-xpl]]

### OBJECT AGREEMENT 1
# (possible with nominalized suffixes spa, sqa, qti, na ??)
obj_agr1 -> tam      <wa:>          [ob=[+p1,+xpl],m=[AGR1=wa]]
obj_agr1 -> tam      [:]            [ob=[-p1]]

### TENSE 1
# Past: r(q)a
tam -> ps1           [r:]           [pos=v,tam=[+ps,-pp,-ft,-cd,-im],m=[TM1=rqa]]
ps1 -> ps2           [q:;:]
ps2 -> sb_ob         [a:]
# Past perfect
tam -> sb_ob         <sqa:>         [pos=v,tam=[+pp,-ps,-ft,-cd,-im],m=[TM1=sqa]]
# Future
tam -> sb_ob         <sa:>          [pos=v,tam=[+ft,-ps,-pp,-cd,-im],sb=[+p1,-p2],m=[TM1=sa]]
# Nominalizers
tam -> nom_sbj       <na:>          [pos=n,pos2=nft,tam=[-ft,-ps,-pp,-cd,-im],m=[TM1=na]]
tam -> nom_sbj       <spa:>         [pos=n,pos2=ger,tam=[-ft,-ps,-pp,-cd,-im],m=[TM1=spa]]
tam -> nom_sbj       <sqa:>         [pos=n,pos2=prt,tam=[-ft,-ps,-pp,-cd,-im],m=[TM1=sqa]]
# Ayacucho: pti
tam -> nom_sbj       <qti:>         [pos=n,pos2=sub,tam=[-ft,-ps,-pp,-cd,-im],m=[TM1=qti]]
# Add POS=v here
tam -> sb_ob         [:]            [pos=v,tam=[-ps,-pp,-ft]];[pos=v,tam=[+ft,-ps,-pp,-cd,-im],sb=[-p1]]

### SUBJECT AGREEMENT -- NOMINALIZATIONS
# 1s
nom_sbj -> arg_plr   [y:]           [-tr,sb=[+p1,-p2],m=[AGR2=y]]
# 2
nom_sbj -> arg_plr   <yki:>         [-tr,sb=[-p1,+p2],m=[AGR2=yki]]
# 3, 1pi (same as for verbs)
nom_sbj -> arg_plr   [n:]           [-tr,sb=[-p1,-p2],m=[AGR2=n]] ; [-tr,sb=[+p1,+p2,+pl],m=[AGR2=n]]
# no subject/possessor
nom_sbj -> case      [:]            [-tr,sb=[-p1,-p2,-plr]]

### SUBJECT-OBJECT AGREEMENT 2
# Intransitive 1s
sb_ob -> arg_plr     <ni:>          [-tr,sb=[+p1,-p2,-pl],tam=[-ft,-cd],m=[AGR2=ni]]
# Future 1 intransitive
sb_ob -> arg_plr     [q:]           [-tr,sb=[+p1,-p2],tam=[+ft,-ps,-pp],m=[AGR2=q]]
# Intransitive 2 (except for cond and nominalized); transitive 2->1 (wa...nki)
sb_ob -> arg_plr     <nki:>         [-tr,sb=[-p1,+p2],tam=[-cd],m=[AGR2=nki]];[sb=[-p1,+p2],ob=[+p1,+xpl],m=[AGR2=nki]]
# Future, conditional 1pi
sb_ob -> arg_plr     <sun:>         [sb=[+p1,+p2,+pl],ob=[-p1,-p2],tam=[-ps,-pp],m=[AGR2=sun]] ; [ob=[+p1,+p2,+pl,+xpl],sb=[-p1,-p2],tam=[-ps,-pp],m=[AGR2=sun]]
# Intransitive 3; intransitive 1pi; transitive 3->1 (wa...n), except fut
sb_ob -> arg_plr     [n:]           [-tr,sb=[-p1,-p2],m=[AGR2=n]] ; [-tr,sb=[+p1,+p2,+pl],m=[AGR2=n]] ; [sb=[-p1,-p2],ob=[+p1,+xpl],tam=[-ft],m=[AGR2=n]]
# Future 3, 3->
sb_ob -> arg_plr     <nqa:>         [sb=[-p1,-p2],ob=[-p2],tam=[+ft,-ps,-pp,-cd],m=[AGR2=nqa]]
# Intransitive 1px; imperative 2-> ; conditional 1s
sb_ob -> arg_plr     [y:]           [-tr,sb=[+p1,-p2,+pl],m=[AGR2=y]] ; [sb=[+p2,-p1],tam=[+im,-cd,-pp,-ps,-ft],m=[AGR2=y]] ; [-tr,sb=[+p1,-p2],tam=[+cd,-pp,-ps,-ft],m=[AGR2=y]]
# Transitive 1->2
sb_ob -> arg_plr     <yki:>         [sb=[+p1,-p2],ob=[-p1,+p2,+xpl],m=[AGR2=yki]]
# Transitive 3->2
sb_ob -> arg_plr     <sunki:>       [sb=[-p1,-p2],ob=[-p1,+p2,+xpl],m=[AGR2=sunki]]
# Imperative 3->-2
sb_ob -> arg_plr     <chun:>        [sb=[-p1,-p2],ob=[-p2,-pl],tam=[+im],m=[AGR2=chun]]
# Conditional 2 intr
sb_ob -> arg_plr     <waq:>         [-tr,sb=[-p1,+p2],tam=[+cd,-ft,-ps,-pp],m=[AGR2=waq]]
# Past or pp 3s sb, intr or 1s obj
sb_ob -> arg_plr     [:]            [tam=[+pp],sb=[-p1,-p2,-pl],ob=[-p2]];[tam=[+ps],sb=[-p1,-p2,-pl],ob=[-p2]]
# Short for sun(chis)man
sb_ob -> indep       <swan:>        [-tr,tam=[+cd],sb=[+p1,+p2,+pl],m=[AGR_TM=swan]];[tam=[+cd],sb=[-p1,-p2],ob=[+p1,+p2,+pl,+excl],m=[AGR_TM=swan]]

### SUBJECT-OBJECT PLURAL NUMBER
# P2 pl subj or obj, but not P1 pl <-> P2 pl
arg_plr -> pl_chi    <chi:>        [sb=[+p2,+pl],ob=[-p2,-pl],m=[AGR3=chis]];[sb=[+p2,+pl],ob=[-p1,-p2,+pl],m=[AGR3=chis]];[ob=[+p2,+pl,+xpl],sb=[-p2,-pl],m=[AGR3=chis]];[ob=[+p2,+pl,+xpl],sb=[-p1,-p2,+pl],m=[AGR3=chis]]
# Both -chis and -chik possible
pl_chi -> cond       [s:;k:]
# 1 pl excl subj or 3 pl subj (1 s/excl or 2s obj), or 1 pl excl obj
arg_plr -> cond      <ku:>          [sb=[+p1,-p2,+pl],ob=[-p1],m=[AGR3=ku]];[sb=[-p1,-p2,+pl],ob=[-p2],m=[AGR3=ku]];[sb=[-p1,-p2,+pl],ob=[-pl],m=[AGR3=ku]];[ob=[+p1,-p2,+pl],sb=[-p1],m=[AGR3=ku]]
# neither subject nor object is plural; should AGR3='0'?
arg_plr -> cond      [:]            [sb=[-pl],ob=[-pl]]

### CONDITIONAL
# Conditional, except 2 intransitive (but 1p incl intransitive does have -man)
cond -> indep        <man:>         [tam=[+cd,-ps,-ft,-pp],ob=[+xpl],m=[TM2=man]];[-tr,tam=[+cd,-ps,-ft,-pp],sb=[-p2],m=[TM2=man]];[-tr,tam=[+cd,-ps,-ft,-pp],sb=[+p1,+p2,+pl],m=[TM2=man]]
cond -> indep        [:]            [tam=[-cd]];[-tr,tam=[+cd],sb=[+p2,-p1]]

#### CASE ON NOUNS
case  -> indep       >case<

### INDEPENDENT SUFFIXES
indep -> end         >indep<

end ->
