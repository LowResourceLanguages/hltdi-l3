###
### Morfotaxis de verbos españoles
###

-> start

# irregular participles
start -> pps    +irr_part+

start -> prepron  [:]
### old version with pre-clitics
## start -> prepron >cl_pre<
## if no pre-clitics, either tenseless or continuous participle (possible post-clitics)
## or not clitics at all
##        [tam=[-tns]] ; [tam=[+tns],as=[+cnt]] ; [tam=[+tns],as=[-cnt],-refl,iob=[-xpl],dob=[-xpl]]
###

# prefixes which begin some irregular verbs
prepron           +prefix+
prepron -> stem   [:]

stem -> stem_e  +verbs_e+
stem -> stem_a  +verbs_a+
stem -> stem_i  +verbs_i+
# these specify different destination states
stem              +vb_irr+
stem -> caer      [:]
caer              +caer+
stem -> decir     [:]
decir             +decir+
stem -> ducir     [:]
ducir             +ducir+
stem -> poner     [:]
poner             +poner+
stem -> tener     [:]
tener             +tener+
stem -> traer     [:]
traer             +traer+
stem -> venir     [:]
venir             +venir+
stem -> ver       [:]
ver               +ver+

# Presente 2,3,1p; imperativo familiar; infinitivo; imperfecto (no futuro, pretérito, subjuntivo, presente 1s)
stem_a -> stem_a1      [:]     [tam=[-prt,-fut]]
stem_e -> stem_e1      [:]     [tam=[-prt,-fut]]
stem_i -> stem_i1      [:]     [tam=[-prt,-fut]]

# Subjuntivo presente, presente 1s, imperativo formal
stem_a -> a_sub_prs1   [:]     [pos=v,tam=[-prt,-fut,-ipf],as=[-cnt,-prf]]
stem_e -> e_sub_prs1   [:]     [pos=v,tam=[-prt,-fut,-ipf],as=[-cnt,-prf]]
stem_i -> e_sub_prs1   [:]     [pos=v,tam=[-prt,-fut,-ipf],as=[-cnt,-prf]]

# Imperativo
stem_a1 -> postpron <`a:>    [pos=v,tam=[-tns,+imv],sb=[-p1,+p2,-pl]]
stem_e1 -> postpron <`e:>    [pos=v,tam=[-tns,+imv],sb=[-p1,+p2,-pl]]
stem_i1 -> postpron <`e:>    [pos=v,tam=[-tns,+imv],sb=[-p1,+p2,-pl]]

# Presente
# 1s
a_sub_prs1 -> person    [o:]    [tam=[-sub,-cnd,-imv,+tns],sb=[+p1,-p2,-pl]]
e_sub_prs1 -> person    [o:]    [tam=[-sub,-cnd,-imv,+tns],sb=[+p1,-p2,-pl]]
# otras
stem_a1 -> prs    [a:]     [pos=v,tam=[-sub,-ipf,-cnd,-imv,+tns],as=[-cnt,-prf]]
stem_e1 -> prs    [e:]     [pos=v,tam=[-sub,-ipf,-cnd,-imv,+tns],as=[-cnt,-prf]]
# becomes e when not stressed
stem_i1 -> prs    [I:]     [pos=v,tam=[-sub,-ipf,-cnd,-imv,+tns],as=[-cnt,-prf]]
prs -> person    [:]      [sb=[+pl]] ; [sb=[-p1]]

# Futuro
stem_a -> fut    <ar':>   [pos=v,tam=[+fut,-imv,-prt,-sub,+tns],as=[-cnt,-prf]]
stem_e -> fut    <er':>   [pos=v,tam=[+fut,-imv,-prt,-sub,+tns],as=[-cnt,-prf]]
stem_i -> fut    <ir':>   [pos=v,tam=[+fut,-imv,-prt,-sub,+tns],as=[-cnt,-prf]]

fut -> person    [e:]     [sb=[+p1],tam=[-cnd,+tns]]
fut -> person    [a:]     [sb=[-p1],tam=[-cnd,+tns]]

# Condicional
fut -> person    <ía:>    [tam=[+cnd]]

# Subjuntivo presente, imperativo (sing formal, plur (1st, 2nd (gram 3rd) person))
a_sub_prs1 -> person [e:]    [tam=[+sub,-imv,+tns]]
a_sub_prs1 -> person <`e:>   [tam=[+imv,-sub,-tns],sb=[-p1,-p2]]
a_sub_prs1 -> person <'e:>   [tam=[+imv,-sub,-tns],sb=[+p1,+pl]]
e_sub_prs1 -> person [a:]    [tam=[+sub,-imv,+tns]]
e_sub_prs1 -> person <`a:>   [tam=[+imv,-sub,-tns],sb=[-p1,-p2]]
e_sub_prs1 -> person <'a:>   [tam=[+imv,-sub,-tns],sb=[+p1,+pl]]

# Imperfecto
stem_a1 -> person <'aba:>  [pos=v,tam=[+ipf,-imv,+tns],as=[-cnt,-prf]]
stem_e1 -> person <ía:>    [pos=v,tam=[+ipf,-imv,+tns],as=[-cnt,-prf]]
stem_i1 -> person <ía:>    [pos=v,tam=[+ipf,-imv,+tns],as=[-cnt,-prf]]

# Pretérito

# Orthographic changes may precede 1s é
stem_a -> end    [é:]     [pos=v,tam=[+prt,-imv,-fut,+tns],as=[-cnt,-prf],sb=[+p1,-pl]]
stem_a -> end    [ó:]     [pos=v,tam=[+prt,-imv,-fut,+tns],as=[-cnt,-prf],sb=[-p1,-p2,-pl]]
stem_a -> prt2   [a:]     [pos=v,tam=[+prt,-sub,-imv,-fut,+tns],as=[-cnt,-prf],sb=[+p2,-pl]] ; [pos=v,tam=[+prt,-sub,+tns],as=[-cnt,-prf],sb=[+pl]]
stem_a -> prt2   <'a:>    [pos=v,tam=[+prt,+sub,-imv,-fut,+tns],as=[-prf,-cnt]]

stem_e -> ie_prt [:]      [pos=v,tam=[+prt,+tns],as=[-cnt,-prf]]
stem_i -> ie_prt [:]      [pos=v,tam=[+prt,+tns],as=[-cnt,-prf]]

ie_prt -> end     [í:]    [sb=[+p1,-pl],tam=[-sub]]
ie_prt -> end     <ió:>   [sb=[-p1,-p2,-pl],tam=[-sub]]
ie_prt -> prt2    [i:]    [sb=[+p2,-pl],tam=[-sub]] ; [sb=[+p1,+pl],tam=[-sub]]
ie_prt -> prt2    <i'e:>  [sb=[-p1,+pl]] ; [tam=[+sub]]

irr_prt -> end    [e:]    [sb=[+p1,-pl],tam=[-sub,+tns]]
irr_prt -> end    [o:]    [sb=[-p1,-p2,-pl],tam=[-sub,+tns]]
irr_prt -> prt2   [i:]    [sb=[+p2,-pl],tam=[-sub,+tns]] ; [sb=[+p1,+pl],tam=[-sub,+tns]]
irr_prt -> prt2   <i'e:>  [sb=[-p1,+pl],tam=[-sub,+tns]] ; [tam=[+sub,+tns]]

# Special person endings for preterite
prt2 -> end      <ste:>   [tam=[-sub],sb=[-p1,+p2,-pl]]
prt2 -> end      <mos:>   [tam=[-sub],sb=[+p1,-p2,+pl]]
prt2 -> end      <ron:>   [tam=[-sub],sb=[-p1,+pl]]

# Subjuntivo imperfecto
prt2 -> person    <ra:>    [tam=[+sub,-imv]]
prt2 -> person    <se:>    [tam=[+sub,-imv]]

# Infinitivo
stem_a1 -> inf    <'ar:>
stem_e1 -> inf    <'er:>
stem_i1 -> inf    <'ir:>
inf -> postpron  [:]      [pos=n,tam=[-imv,-sub,-tns]]

# Participio presente
stem_a1 -> ppr  <'ando:> 
stem_e1 -> ppr  <i'endo:>
stem_i1 -> ppr  <i'endo:>
ppr -> postpron  [:]      [pos=adv,tam=[-imv,-sub,-tns]] ; [pos=v,tam=[+tns],as=[+cnt,-prf]]

# Participio pasado
stem_a1 -> pps       <ad:>
stem_e1 -> pps       <id:>
stem_i1 -> pps       <id:>
pps -> adjsuff      [:]    [pos=adj,tam=[-imv,-sub,-tns],-refl,iob=[-xpl],dob=[-xpl]];[pos=v,tam=[+tns],as=[+prf,-cnt],-refl,iob=[-xpl],dob=[-xpl]]

# Person endings for most tenses/moods
person -> end      [s:]    [sb=[-p1,+p2,-pl]]
person -> mos1     <mo:>   [sb=[+p1,-p2,+pl]]
mos1 -> end        [s:]    [tam=[-imv]]
mos1 -> postpron   [s:]    [-refl,tam=[+imv]]
mos1 -> postpron   [:]     [+refl,tam=[+imv]]
# 2, 3 pers plur non-imperative
person -> end      [n:]    [sb=[-p1,-p2,+pl],tam=[-imv]]
# 2 pers (3 gram) plur imperative
person -> postpron [n:]    [sb=[-p1,-p2,+pl],tam=[+imv]]
# sing non-imperative; 1st or 3rd person
person -> end      [:]     [sb=[-pl,-p2],tam=[-imv]]
# 2 pers sing polite (3 gram) imperative
person -> postpron [:]     [sb=[-p1,-p2,-pl],tam=[+imv]]

# Object suffixes for imperative, pres part, and infinitive

postpron -> end   >cl_post<

# Adjective suffixes for past part

adjsuff -> end     [o:]    [pos=adj,ref=[+xpl,-fem,-pl]] ; [pos=v,as=[+prf]]
adjsuff -> end     [a:]    [pos=adj,ref=[+xpl,+fem,-pl]]
adjsuff -> end     <os:>   [pos=adj,ref=[+xpl,-fem,+pl]]
adjsuff -> end     <as:>   [pos=adj,ref=[+xpl,+fem,+pl]]

end ->
