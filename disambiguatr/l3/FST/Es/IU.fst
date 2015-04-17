# I -> i when there is another vowel and it's not i, e otherwise
# U -> O when there is no other vowel
# IE -> ! / E

-> start

start -> start  [X;V-I,U;Q]

start -> Ii     [i:I;U]
# one or more consonants or _
Ii -> IiC       [X;_]
IiC -> IiC      [X]
# a vowel other than i, not accented(?)
IiC -> start    [V2-i,í]
IiC -> Ie       [e:I]
# i followed by ...
IiC -> IiCi     [i]
# ... another vowel or accent
IiCi -> start   [V2;']

start -> Ie     [e:I;O:U]
# s, n or nothing else ends the word
Ie -> end       [s;n;:]
# two or more additional syllables
Ie -> IeC       [X;_]
# ' can precede the vowel
IeC -> IeC      [X;']
# the next vowel is i
IeC -> IeCi     [i;í]
# ía a possibility
IeCi -> IeCi    [a]
IeC -> Ii       [i:I]
# and that's followed by a consonant or nothing
IeCi -> start   [X]
IeCV -> IeCVC   [X]

# words like sentir; IE -> ! / E
start -> I!     [!:I]
I! -> Ii        [:E]
start -> Id     [:I]
Id -> Ie        [E]

start ->
end ->
IeCi ->
