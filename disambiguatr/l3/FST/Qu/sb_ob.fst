### SUBJECT-OBJECT SUFFIXES (excluding initial -wa: 1p object)

-> start

# Intransitive 1s
start -> plur     <ni:>    [-tr,sb=[+p1,-p2,-pl],tam=[-ft,-cd],m=[AGR2=ni]]
# Future 1 intransitive
start -> plur     [q:]     [-tr,sb=[+p1,-p2],tam=[+ft,-ps,-pp],m=[AGR2=q]]
# Intransitive 2 (except for cond, imper, nominalized); transitive 2->1 (wa...nki) (except for imper and nominalized?)
start -> plur     <nki:>   [-tr,sb=[-p1,+p2],tam=[-cd,-im],m=[AGR2=nki]];[sb=[-p1,+p2],ob=[+p1,+xpl],tam=[-im],m=[AGR2=nki]]
# Future, conditional 1pi
start -> ft_cd_1i <sun:>   [sb=[+p1,+p2,+pl],ob=[-p1,-p2]] ; [ob=[+p1,+p2,+pl,+xpl],sb=[-p1,-p2]]
ft_cd_1i -> plur  [:]      [tam=[+ft,-cd,-ps,-pp,-im],AGR2=sun] ; [tam=[-ft,+cd,-ps,-pp,-im],AGR2=sun]
# Intransitive 3 (except fut); intransitive 1pi; transitive 3->1 (wa...n), except fut
start -> plur     [n:]     [-tr,sb=[-p1,-p2],tam=[-ft],m=[AGR2=n]];[-tr,sb=[+p1,+p2,+pl],m=[AGR2=n]];[sb=[-p1,-p2],ob=[+p1,+xpl],tam=[-ft],m=[AGR2=n]]
# Future 3, 3->
start -> plur     <nqa:>   [sb=[-p1,-p2],ob=[-p2],tam=[+ft,-ps,-pp,-cd],m=[AGR2=nqa]]
# Intransitive 1px; imperative 2->; conditional 1s
start -> plur     [y:]     [-tr,sb=[+p1,-p2,+pl],m=[AGR2=y]];[sb=[+p2,-p1],tam=[+im,-cd,-pp,-ps,-ft],m=[AGR2=y]];[-tr,sb=[+p1,-p2],tam=[+cd,-pp,-ps,-ft],m=[AGR2=y]]
# Transitive 1->2
start -> plur     <yki:>   [sb=[+p1,-p2],ob=[-p1,+p2,+xpl],m=[AGR2=yki]]
# Transitive 3->2
start -> plur     <sunki:> [sb=[-p1,-p2],ob=[-p1,+p2,+xpl],m=[AGR2=sunki]]
# Imperative 3->-2
start -> plur     <chun:>  [sb=[-p1,-p2],ob=[-p2,-pl],tam=[+im],m=[AGR2=chun]]
# Conditional 2 intr
start -> plur     <waq:>   [-tr,sb=[-p1,+p2],tam=[+cd,-ft,-ps,-pp],m=[AGR2=waq]]
# Past or pp 3s sb, intr or 1s obj
start -> plur     [:]      [tam=[+pp],sb=[-p1,-p2,-pl],ob=[-p2]];[tam=[+ps],sb=[-p1,-p2,-pl],ob=[-p2]]

### PLURAL SUFFIXES
# P2 pl subj or obj, but not P1 pl <-> P2 pl
plur ->  pl_chi   <chi:>   [sb=[+p2,+pl],ob=[-p2,-pl]];[sb=[+p2,+pl],ob=[-p1,-p2,+pl]];[ob=[+p2,+pl,+xpl],sb=[-p2,-pl]];[ob=[+p2,+pl,+xpl],sb=[-p1,-p2,+pl]]
# Both -chis and -chik possible
pl_chi -> end     [s:;k:]  [m=[AGR3=chis]]
# 1 pl excl subj or 3 pl subj (1 s/excl or 2s obj), or 1 pl excl obj
plur  -> pl_ku    <ku:>    [sb=[+p1,-p2,+pl],ob=[-p1]];[sb=[-p1,-p2,+pl],ob=[-p2]];[sb=[-p1,-p2,+pl],ob=[-pl]];[ob=[+p1,-p2,+pl],sb=[-p1]]
pl_ku -> end      [:]      [m=[AGR3=ku]]
# neither subject nor object is plural; should AGR3='0'?
plur   -> end     [:]      [sb=[-pl],ob=[-pl]]

end ->

