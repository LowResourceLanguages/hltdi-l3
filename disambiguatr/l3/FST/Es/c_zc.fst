# C -> zc before o and a
# C -> c otherwise

-> start

start -> start  [V;X-C;Q]

# -> zc
start -> Cz.c   [z:C]
Cz.c -> Czc     [c:]
Czc -> start    [o;ó;a;á]     # 1p sing, pres subj

# -> c
start -> Cc     [c:C]
Cc -> start     [V-o,a,ó,á;Q]

start ->
