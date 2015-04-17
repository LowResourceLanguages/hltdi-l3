# drop 'V in one-syllable words
# doesn't handle cases where pre-clitics precede one-syllable words with '

-> start

start -> start   [X]
# first vowel; delete any ', but no ' also possible
start -> '.V     [:;:']
'.V -> 'V.       [V]
'V. -> 'V.       [V]
# C at end of first syllable
'V. -> C         [X]

# don't delete '
start -> V0      [V;']
V0 -> V0         [V]
# vowels in separate syllables could be separated by ' as well as C
V0 -> C0         [X;']
C0 -> end        [X;';V]
end -> end       [X;';V]

'V. ->
C ->
end ->
