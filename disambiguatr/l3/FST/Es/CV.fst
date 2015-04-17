# consonant changes before certain vowels
# G(o|a|u) -> g;  G(i|e) -> gu; Gu(e|i) -> gü
# Z(o|a|u) -> z;  Z(i|e) -> c
# J(o|a|u) -> j;  J(i|e) -> g
# K(o|a|u) -> c;  K(i|e) -> qu
# C(o|a|u) -> zc; C(i|e) -> c

-> start

start -> start  [V;X-C,G,J,K,Z;Q]

start -> .A     [z:Z;j:J;c:K]
.A -> start     [a;o;u;á;ó;ú]
start -> .E     [c:Z;g:J;c:C;qu:K]
.E -> start     [e;i;é;í]

# C -> zc before a,o,u
start -> Cz     [z:C]
Cz -> .A        [c:]

start -> g      [g:G]
# cago
g -> start      [a;o;á;ó]
g -> gu         [u]
# averiguamos
gu -> start     [a;o;á;ó;X;Q]       # arcs to G,Z,J,K,C states?
# averigüe, avergüenzo
g -> .E         [ü:u]
# cague, seguimos
gu.I -> start   [e;i;é;í]
g -> .E         [u:]

# Z can appear before consonants or word finally
start -> z=Z    [z:Z]
# hazlo
z=Z -> start    [X]

start ->
# haz
z=Z ->
