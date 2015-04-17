# consonant changes before certain vowels
# G(o|a|u) -> g;  G(i|e) -> gu; Gu(e|i) -> gü
# Z(o|a|u) -> z;  Z(i|e) -> c
# J(o|a|u) -> j;  J(i|e) -> g
# K(o|a|u) -> c;  K(i|e) -> qu
# C(o|a|u) -> zc; C(i|e) -> c

-> start

start -> start  [V;X-g,c,z,qu;Q-+]

# -a verbs (cagar): insert 'u' before e,é
start -> g      [g] 
g -> g_u        [u:]
g_u -> g_u+     [:+]
g_u+ -> start   [e;é]
# -a verbs (averiguar): gu -> gü before e,é
g -> gü         [ü:u]
gü -> gü+       [:+]
gü+ -> start    [e;é]
# -i,-e verbs (elegir): j -> g before a, o
start -> gj     [j:g]
gj -> gj+       [:+]
gj+ -> start    [a;o]
# -i verbs (distinguir): gu -> g before a, o
g -> gDu        [:u]              # delete the u
gDu -> gDu+     [:+]
gDu+ -> start   [a;o]
# -i verbs (argüir): gü -> gu(y)
####

# -a verbs (sacar): c -> qu before e, é
start -> cqu    [qu:c]
cqu -> cqu+     [:+]
cqu+ -> start   [e;é]
# -e,-i verbs (cocer): c -> before a, o
start -> cz     [z:c]
cz -> cz+       [:+]
cz+ -> start    [a;o]

# -a verbs (cazar): z -> c before e, é
start -> zc     [c:z]
zc -> zc+       [:+]
zc+ -> start    [e;é]

# -i verbs (delinquir): qu -> c before a, o
start -> quc    [c:qu]
quc -> quc+     [:+]
quc+ -> start   [a;o]

# other cases of g,z,c,qu

g -> gu         [u]
gu -> start     [V;X;Q-+]
g -> start      [V-u;Q-+]

start -> c      [c]
c -> start      [V;Q-+]

start -> z      [z]
z -> start      [V;c;Q-+]

start -> qu     [qu]
qu -> start     [V;X;Q-+]

# delete other +
start -> del+   [:+]
del+ -> start   [X;V;Q]

start ->
