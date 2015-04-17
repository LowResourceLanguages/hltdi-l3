# u_V -> úV when accented, uV otherwise
# i_V -> íV when accented, iV otherwise

-> start

start -> start   [X;V-i,u;Q]

## accented
start -> A      [í:i;ú:u]     # accent the i or u
A -> A_         [:_]          # delete the _
# unaccented vowel must follow; it's the last vowel
A_ -> A_V       [V0]
# ... followed by s, n, or nothing
A_V -> end      [s;n;:]

## unaccented
start -> iu     [i;u]         # don't accent the i or u
iu -> iu_       [:_]          # delete the _
# ' or accented vowel
iu_ -> start    [';V1]
# unaccented vowel, not final
iu_ -> iu_V     [V0]
# another vowel could follow
iu_V -> start   [';V1]
iu_V -> iu_VC   [X]
iu_VC -> iu_VC  [X]
# some other vowel or '
iu_VC -> start  [V;']

# other occurrences of i and u
iu -> start     [X;V;Q-_]

start ->
end ->
iu ->
