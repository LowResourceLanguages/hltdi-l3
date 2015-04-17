###
### Quechua noun morphotactics
###

# ^: -ni- after consonants, 0 after vowels

-> start

### ROOT, STEM
start -> der1        +n+

### VARIOUS DERIVATIONAL SUFFIXES
der1 -> der2         <cha:>         [der=[+dim],m=[DER1=cha]]
der1 -> der2         <sapa:>        [der=[+aug],m=[DER1=sapa]]
# possessor: with N; can also appear *after* -kuna: wasi-kuna-yuq, wasi-yuq-kuna (Soto Ruiz, 141)
der1 -> der2         <^yuq:>        [der=[+pos],m=[DER1=yoq]]
der1 -> der2          [:]           [der=[-dim,-aug]]

# -lla occurs when -kuna, -kama, -pura, and -nka are absent
der2 -> poss         <lla:>         [der=[+lim],-pl,cs=[-dstr,-intn,-trm],m=[DER2=lla]]
der2 -> poss          [:]           [der=[-lim]];[+pl];[cs=[+dstr]];[cs=[+intn]];[cs=[+trm]]

### POSSESSOR
poss -> num          >poss<

### NUMBER
num -> pl_lim       <kuna:>         [+pl]
num -> case          [:]            [-pl]

pl_lim -> case      <lla:>          [der=[+lim],+pl,m=[PL_LIM=lla]]
pl_lim -> case       [:]            [der=[-lim]]

### CASE
case  -> indep       >case<

### "INDEPENDENT" SUFFIXES
indep -> end         >indep<

end ->
