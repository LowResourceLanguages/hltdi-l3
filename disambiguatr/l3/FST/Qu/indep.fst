### "INDEPENDENT" SUFFIXES (ENCLITICS)

# These appear in 6 slots.

# For Ayacucho, add -miki, -siki, -chiki; -ch allomorph of -cha

# C!: Ci or C, depending on previous segment

-> start

### -puni: definite, certain, necessary, "explicitativo"

start -> add         <puni:>        [prag=[+xplc],m=[INDEP1=puni]]
start -> add         [:]            [prag=[-xplc]]

### Conjunctions 1: additive -pas/-pis, -wan (does it go here?)

add -> cont          <pas:>         [conj=[+add],m=[INDEP2=pas]]
add -> cont          <pis:>         [conj=[+add],m=[INDEP2=pis]]
add -> cont          <wan:>         [conj=[+cop],m=[INDEP2=wan]]
add -> cont          [:]            [conj=[-add,-cop]]

### Continuative -ña ('already'), -raq ('still')

cont -> seq          <ña:>          [asp=[contin=n],m=[INDEP3=ña]]
cont -> seq          <raq:>         [asp=[contin=y],m=[INDEP3=raq]]
cont -> seq          [:]            [asp=[contin=None]]

### Conjunctions 2: -taq; sequential, also signals contradiction

seq -> intneg        <taq:>         [conj=[+seq],m=[INDEP4=taq]]
seq -> intneg        [:]            [conj=[-seq]]

### Non-assertive -chu: negative or interrogative

intneg -> prag       <chu:>         [prag=[+nonassr],m=[INDEP5=chu]]
intneg -> prag       [:]            [prag=[-nonassr]]

### Miscellaneous pragmatic suffixes

## Evidentials
prag -> evid        [m:]           [prag=[ev=vald],m=[INDEP6=mi]]
prag -> evid        [s:]           [prag=[ev=rprt],m=[INDEP6=si]]
# mi/n, si/s
evid -> end         [!:]           [prag=[-emph]]
# má, sá
evid -> end         [á:]           [prag=[+emph]]

## "Responsive"
prag -> end         <ri:>          [prag=[+resp]]

## "Prognosticator" -cha, -chá
prag -> end         <cha:>         [prag=[+progn,-emph],m=[INDEP6=cha]]
# Ayacucho: <ch!:>
prag -> end         <chá:>         [prag=[+progn,+emph],m=[INDEP6=chá]]

## Doubt: -suna, -sina
prag -> suna        <su:>          [prag=[+dbt],m=[INDEP6=suna]]
# -sina must follow -chu
prag -> suna        <si:>          [prag=[+dbt,+nonassr],m=[INDEP6=sina]]
suna -> end         <na:>

## Topicalizer
prag -> end         <qa:>          [prag=[+top,ev=None],m=[INDEP6=qa]]

## Other emphatic
prag -> end         <yá:>          [prag=[+emot,+emph],m=[INDEP6=yá]]
prag -> end         <tá:>          [prag=[+intj,+emph],m=[INDEP6=tá]]

## No pragmatic suffix
prag -> end         [:]            [prag=[-top,-emph,-emot,-intj,-progn,-dbt,-resp,ev=None]]

end ->
