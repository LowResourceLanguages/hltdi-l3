# ':` before last vowel

-> start

start -> start  [X;Q-` ]

## insert a ' ...
start -> A      [':]
## ... before a vowel (to be accented)
# but this could be a diphthong, starting with i or u
A -> iu.         [i;u]
iu. -> AV       [a;e;o;á;é;ó;O;E]
# or a diphthong ending in i or u
A -> V.         [a;e;o;á;é;ó;O;E]
V. -> AV        [i;u]
# or a single vowel that can't start a diphthong
A -> AV         [a;e;o;á;é;ó;O;E]
### ... followed by possibly another '
##AV -> AV        [']
# ... and a consonant or VV boundary or nothing
AV -> AVC       [X;_;:]
# ... or if the vowel is i or u, there must be something
iu. -> AVC      [X;_]
# ... and possibly other consonants
AVC -> AVC      [X;Q-`]
# ... there can be an i or u if this is a diphthong
AVC -> AVCv     [i;u;:]
# ... finally a `, which gets deleted (transferring accent back)
AVCv -> AVC`    [:`]
# a vowel has to follow ` (actually it must be e or a)
AVC` -> start   [a;e]

## cases where no change is made
# a vowel ...
start -> V      [V]
# ... possibly followed by another vowel, ', or a space
V -> V          [V;']
# ... followed by a consonant or VV boundary
V -> VC0        [X;_]
# ... and possibly one or two other consonsants
VC0 -> VC       [X;:]
VC0 -> VC1      [X]
VC1 -> VC       [X]
VC -> start     [V;Q-`]
VC -> A         [':]

start ->
V ->
VC ->
