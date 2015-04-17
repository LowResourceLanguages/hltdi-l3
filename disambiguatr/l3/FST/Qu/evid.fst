# realization of !: vowel or 0 in evidentials
# V + n, s, (ch in Ayacucho)
# C + mi, si, (cha in Ayacucho)

-> start

start -> start [^]

start -> C     [X]
C -> CX        [m;s]
# C -> CCh       [ch]  # Ayacucho
C -> C         [X;^]
C -> V         [V]
CX -> start    [i:!]
# vowel is a for ch!
# CCh -> start   [a:!] # Ayacucho

start -> V     [V]
V -> C         [X;^]
V -> V         [V]
# m -> n after vowel
V -> VX        [n:m;s]  # [ch] in Ayacucho
VX -> start    [:!]

start ->
C ->
V ->

