### GENITIVE SUFFIX $: -q, -pa
### precedes evid and ni, so ! and ^ must be included

-> start

start -> start [!;^]

start -> C     [X]
C -> C$        [p:$]
C$ -> start    [a:]
C -> C         [X;^]
C -> V         [V]
C -> start     [!]

start -> V     [V]
V -> C         [X;^]
V -> V         [V]     # is this possible?
V -> start     [q:$]

start ->
C ->
V ->
