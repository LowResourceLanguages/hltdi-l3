# V(h)_u -> V(h)ú when accented, V(h)u otherwise
# V(h)_i -> V(h)í when accented, V(h)i otherwise

-> start

start -> start  [X;V;Q-_]

## accented
start -> _      [:_]          # delete the _
_ -> A          [í:i;ú:u]     # accent the i or u
# last vowel, accented 
A -> end        [X-n,s]       # this never happens with verbs (except -d)?
A -> AC         [X]
AC -> AC        [X]
# next vowel is last; must be unaccented
AC -> ACV       [V0]
# ... and followed by nothing or consonant other than s,n
ACV -> end      [s;n;:]
# following vowel must be accented; delete the '
_ -> _'         [:']
_' -> start     [í:i;ú:u]     # accent the i or u

# unaccented
_ -> iu         [i;u]         # don't accent the i or u
# last vowel, unaccented
iu -> end       [s;n;:]
# next vowel accented (no consonant)
iu -> start     [';V1]
# C not end of word
iu -> iuC       [X]
iuC -> iuC      [X]
# CV unaccented
iuC -> iuCV     [V0]
# CV accented
iuC -> start    [V1;']
iuCV -> start   [V1;']
# one syllable more ending in consonant other than s, n
iuCV -> end     [X-n,s]
# two or more syllables more
iuCV -> iuCVC   [X]
iuCVC -> iuCVC  [X;Q]
iuCVC -> start  [V]

# any other following vowel or consonant
_ -> start      [V-i,u;X;Q-']

start ->
end ->
