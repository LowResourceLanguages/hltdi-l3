### CASE SUFFIXES

# Up to three case suffixes are possible, appearing in at least 3
# slots. This FST accounts for most, but not all of the possibilities and
# restrictions discussed in Calvo Pérez, pp. 335ff.

# $: genitive morpheme: -q, -pa

-> case1

# no case marker, nominative
# case1 -> end    [:]      [cs=[+nom,-gen,-intrc,-pos,-acc,-ben,-ill,-abl,-ins,-trm,-caus,-loc,-prol,-dstr]]

# -pa/-q, -pura, -npa, -nka?, -nta?
case1 -> case2  [$:]     [cs=[+gen,-intrc,-pos,-prol,-dstr],m=[CASE1=pa]]
case1 -> case2  <pura:>  [cs=[+intrc,-gen,-pos,-prol,-dstr],m=[CASE1=pura]]
case1 -> case2  <npa:>   [cs=[+pos,-gen,-intrc,-prol,-dstr],m=[CASE1=npa]]
case1 -> case2  <nta:>   [cs=[+prol,-gen,-intrc,-pos,-dstr],m=[CASE1=nta]]
case1 -> case2  <nka:>   [cs=[+dstr,-gen,-intrc,-pos,-prol],m=[CASE1=nka]]
case1 -> case2  [:]      [cs=[-gen,-intrc,-pos,-prol,-dstr]]

# -pi, -paq, -ta, -man, -manta, -rayku
case2 -> case3  <pi:>    [cs=[+loc,-ben,-acc,-ill,-abl,-caus],m=[CASE2=pi]]
case2 -> case3  <paq:>   [cs=[+ben,-loc,-acc,-ill,-abl,-caus],m=[CASE2=paq]]
case2 -> case3  <ta:>    [cs=[+acc,-loc,-ben,-ill,-abl,-caus],m=[CASE2=ta]]
# ablative, illative: -man, -manta
case2 -> ab_il  <man:>
ab_il -> case3  [:]      [cs=[+ill,-loc,-ben,-acc,-abl,-caus],m=[CASE2=man]]
ab_il -> case3  <ta:>    [cs=[+abl,-loc,-ben,-acc,-ill,-caus],m=[CASE2=manta]]
case2 -> case3  <rayku:> [cs=[+caus,-loc,-ben,-acc,-ill,-abl],m=[CASE2=rayku]]
case2 -> case3  [:]      [cs=[-loc,-ben,-acc,-ill,-abl,-caus]]

case3 -> p_case <kama:>  [cs=[+trm,-ins],m=[CASE3=kama]]
# what about puwan??
case3 -> p_case <wan:>   [cs=[+ins,-trm],m=[CASE3=wan]]
case3 -> p_case [:]      [cs=[-trm,-ins]]

## pseudo-case
# -lla appears here (rather than in one of usual derivational suffix slots) if -pura, -nka, or -kama appear
# or if this is a pronoun
p_case -> end   <lla:>   [der=[+lim,-incl],cs=[+intrc]];[der=[+lim,-incl],cs=[+dstr]];[der=[+lim,-incl],cs=[+trm],m=[P_CASE=lla]];[der=[+lim,-incl],pos2=pron]
# ntin can also appear *before* case suffixes, for example, qhari-ntin warmi-ntin-ta (Calvo Pérez, p 338)
p_case -> end   <ntin:>  [der=[+incl,-lim],m=[P_CASE=ntin]]
# everything but pronouns (special conditions on occurrence of -lla and -ntin(?))
p_case -> non_pron [:]   [pos2=cn];[pos2=inf];[pos2=agt];[pos2=inf];[pos2=nft];[pos2=ger];[pos2=prt];[pos2=sub];[pos2=adj]
non_pron -> end [:]      [der=[-lim,-incl]];[der=[+lim,-incl],cs=[-dstr,-trm,-intrc]]
# pronouns
p_case -> end   [:]      [pos2=pron,der=[-lim,-incl]]

end ->