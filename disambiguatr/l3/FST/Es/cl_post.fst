-> se

# se as IO before 3,2p DO
se -> sD  <se:>   [iob=[-p1,-p2,+xpl],dob=[-p1,-p2,+xpl]]
se -> sT  <se:>   [+refl,sb=[-p1,-p2]]
# no se: either not reflexive or refl:1 or refl:2s,fam
se -> T   [:]      [-refl] ; [+refl,sb=[+p1]] ; [+refl,sb=[+p2,-pl]]

sT -> stM <te:>   [dob=[-p1,+p2,-pl,+xpl],iob=[-p2],sb=[-p2]] ; [iob=[-p1,+p2,-pl,+xpl],dob=[-p2],sb=[-p2]]
# No xplicit 2fam dob or iob; no 2fam refl
sT -> sM   [:]     
T -> tM   <te:>   [dob=[-p1,+p2,-pl,+xpl],iob=[-p2],sb=[-p2]] ; [iob=[-p1,+p2,-pl,+xpl],dob=[-p2],sb=[-p2]] ; [+refl,sb=[-p1,+p2,-pl]]
# No xplicit 2fam dob or iob; no 2fam refl
T -> M     [:]     [-refl] ; [+refl,sb=[-p2]]

# p2 -> p1  <te:>   [dob=[-p1,+p2,-pl,+xpl],iob=[-p2],sb=[-p2]] ; [iob=[-p1,+p2,-pl,+xpl],dob=[-p2],sb=[-p2]] ; [+refl,sb=[-p1,+p2,-pl]]
# No xplicit 2fam dob or iob; no 2fam refl
# p2 -> p1   [:]     [-refl] ; [+refl,sb=[-p2]]

stM -> clend <me:>   [dob=[+p1,-p2,-pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,-pl,+xpl],dob=[-p1],sb=[-p1]]
stM -> clend <nos:>  [dob=[+p1,-p2,+pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,+pl,+xpl],dob=[-p1],sb=[-p1]]
stM -> stL   [:]
sM -> smL    <me:>   [dob=[+p1,-p2,-pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,-pl,+xpl],dob=[-p1],sb=[-p1]]
sM -> smL    <nos:>  [dob=[+p1,-p2,+pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,+pl,+xpl],dob=[-p1],sb=[-p1]]
sM -> sL     [:]
tM -> clend  <me:>   [dob=[+p1,-p2,-pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,-pl,+xpl],dob=[-p1],sb=[-p1]] ; [+refl,sb=[+p1,-p2,-pl]]
tM -> clend  <nos:>  [dob=[+p1,-p2,+pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,+pl,+xpl],dob=[-p1],sb=[-p1]] ; [+refl,sb=[+p1,-p2,+pl]]
tM -> tL     [:]      [-refl] ; [+refl,sb=[-p1]]
M -> mL      <me:>   [dob=[+p1,-p2,-pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,-pl,+xpl],dob=[-p1],sb=[-p1]] ; [+refl,sb=[+p1,-p2,-pl]]
M -> mL      <nos:>  [dob=[+p1,-p2,+pl,+xpl],iob=[-p1],sb=[-p1]] ; [iob=[+p1,-p2,+pl,+xpl],dob=[-p1],sb=[-p1]] ; [+refl,sb=[+p1,-p2,+pl]]
M -> L       [:]      [-refl] ; [+refl,sb=[-p1]]

# se te l_
stL -> clend <lo:>   [dob=[-p1,-p2,-pl,-fem,+xpl]]
stL -> clend <la:>   [dob=[-p1,-p2,-pl,+fem,+xpl]]
stL -> clend <los:>  [dob=[-p1,-p2,+pl,-fem,+xpl]]
stL -> clend <las:>  [dob=[-p1,-p2,+pl,+fem,+xpl]]
stL -> clend <le:>   [iob=[-p1,-p2,-pl,+xpl]] ; [dob=[-p1,-p2,-pl,+anim,+xpl]]
stL -> clend <les:>  [iob=[-p1,-p2,+pl,+xpl]] ; [dob=[-p1,-p2,+pl,+anim,+xpl]]
# se te
stL -> clend  [:]     

# se me/nos l_
smL -> clend <lo:>   [dob=[-p1,-p2,-pl,-fem,+xpl]]
smL -> clend <la:>   [dob=[-p1,-p2,-pl,+fem,+xpl]]
smL -> clend <los:>  [dob=[-p1,-p2,+pl,-fem,+xpl]]
smL -> clend <las:>  [dob=[-p1,-p2,+pl,+fem,+xpl]]
smL -> clend <le:>   [iob=[-p1,-p2,-pl,+xpl]] ; [dob=[-p1,-p2,-pl,+anim,+xpl]]
smL -> clend <les:>  [iob=[-p1,-p2,+pl,+xpl]] ; [dob=[-p1,-p2,+pl,+anim,+xpl]]
# se me/nos
smL -> clend  [:]     

# se l_ (se: iob)
sD ->  clend <lo:>   [dob=[-p1,-p2,-pl,-fem,+xpl]]
sD ->  clend <la:>   [dob=[-p1,-p2,-pl,+fem,+xpl]]
sD ->  clend <los:>  [dob=[-p1,-p2,+pl,-fem,+xpl]]
sD ->  clend <las:>  [dob=[-p1,-p2,+pl,+fem,+xpl]]
sD ->  clend <le:>   [dob=[-p1,-p2,-pl,+anim,+xpl]]
sD ->  clend <les:>  [dob=[-p1,-p2,+pl,+anim,+xpl]]

# se l_ (reflexive)
sL -> clend <lo:>    [dob=[-p1,-p2,-pl,-fem,+xpl]]
sL -> clend <la:>    [dob=[-p1,-p2,-pl,+fem,+xpl]]
sL -> clend <los:>   [dob=[-p1,-p2,+pl,-fem,+xpl]]
sL -> clend <las:>   [dob=[-p1,-p2,+pl,+fem,+xpl]]
sL -> clend <le:>    [iob=[-p1,-p2,-pl,+xpl]] ; [dob=[-p1,-p2,-pl,+anim,+xpl]]
sL -> clend <les:>   [iob=[-p1,-p2,+pl,+xpl]] ; [dob=[-p1,-p2,+pl,+anim,+xpl]]
# JUST se
sL -> clend  [:]      [dob=[-xpl],iob=[-xpl]]

tL -> clend <lo:>    [dob=[-p1,-p2,-pl,-fem,+xpl]]
tL -> clend <la:>    [dob=[-p1,-p2,-pl,+fem,+xpl]]
tL -> clend <los:>   [dob=[-p1,-p2,+pl,-fem,+xpl]]
tL -> clend <las:>   [dob=[-p1,-p2,+pl,+fem,+xpl]]
tL -> clend <le:>    [iob=[-p1,-p2,-pl,+xpl]] ; [dob=[-p1,-p2,-pl,+anim,+xpl]]
tL -> clend <les:>   [iob=[-p1,-p2,+pl,+xpl]] ; [dob=[-p1,-p2,+pl,+anim,+xpl]]
# JUST te
tL -> clend  [:]      [dob=[-xpl],iob=[+xpl],-refl] ; [iob=[-xpl],dob=[+xpl],-refl] ; [+refl,iob=[-xpl],dob=[-xpl]]

mL -> clend <lo:>    [dob=[-p1,-p2,-pl,-fem,+xpl]]
mL -> clend <la:>    [dob=[-p1,-p2,-pl,+fem,+xpl]]
mL -> clend <los:>   [dob=[-p1,-p2,+pl,-fem,+xpl]]
mL -> clend <las:>   [dob=[-p1,-p2,+pl,+fem,+xpl]]
mL -> clend <le:>    [iob=[-p1,-p2,-pl,+xpl]] ; [dob=[-p1,-p2,-pl,+anim,+xpl]]
mL -> clend <les:>   [iob=[-p1,-p2,+pl,+xpl]] ; [dob=[-p1,-p2,+pl,+anim,+xpl]]
# JUST me/nos
mL -> clend  [:]      [dob=[-xpl],iob=[+xpl],-refl] ; [iob=[-xpl],dob=[+xpl],-refl] ; [+refl,iob=[-xpl],dob=[-xpl]]

# JUST l_
L -> clend <lo:>     [dob=[-p1,-p2,-pl,-fem,+xpl],iob=[-xpl]]
L -> clend <la:>     [dob=[-p1,-p2,-pl,+fem,+xpl],iob=[-xpl]]
L -> clend <los:>    [dob=[-p1,-p2,+pl,-fem,+xpl],iob=[-xpl]]
L -> clend <las:>    [dob=[-p1,-p2,+pl,+fem,+xpl],iob=[-xpl]]
L -> clend <le:>     [iob=[-p1,-p2,-pl,+xpl],dob=[-xpl]] ; [dob=[-p1,-p2,-pl,+anim,+xpl],iob=[-xpl]]
L -> clend <les:>    [iob=[-p1,-p2,+pl,+xpl],dob=[-xpl]] ; [dob=[-p1,-p2,+pl,+anim,+xpl],iob=[-xpl]]
# NO CLITIC PRONOUNS
L -> clend  [:]       [dob=[-xpl],iob=[-xpl],-refl]

clend ->
