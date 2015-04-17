# lliV -> llV
# ñiV -> ñV
# yiV -> yV

-> start

start -> start    [V;X-ll,ñ,y;Q]

start -> llny     [ll;ñ;y]       # word can't end in ll, ñ
start -> y        [y]            # but it can end in y
y    -> llnyi     [:i]
llny -> llnyi     [:i]           # ... or i
llnyi -> start    [V]

# lliC, ñiC
y    -> llnyi.C   [i]
llny -> llnyi.C   [i]
llnyi.C -> start  [X;Q]

y -> start        [V-i;X;Q]
llny -> start     [V-i;X;Q]

start ->
y ->
