# O -> ue when accented, o otherwise
# E -> ie when accented, e otherwise
# ! -> ie when accented, i otherwise
# U -> ue when accented, u otherwise

-> start

start -> start  [X;V-O,E,!,U;Q-']

## explicitly accented O, E, !, U
start -> ac     [:']
# make a diphthong...
ac -> acV.e     [u:O;i:E;i:!;u:U]
# ... putting the accent before the e
acV.e -> start  <'e:>

## explicitly accented other vowels
start -> AC     [']
AC -> start     [V2]

## unexplicitly accented O, E, !, U
start -> V.e    [u:O;i:E;i:!;u:U]
V.e -> Ve       [e:]
Ve -> end       [X-n,s]       # this never happens with verbs (except -d)?
Ve -> VeC       [X]
VeC -> VeC      [X]
# next vowel is last, unaccented
VeC -> VeCV     [V0]
# ... and followed by nothing or consonant other than s,n
VeCV -> end     [s;n;:]

## unaccented O, E, !, U
start -> V      [o:O;e:E;i:!;u:U]
V -> end        [s;n;:]
V -> VC         [X]
VC -> VC        [X]
# the following vowel could be explicitly accented (cocer: cOZ'er)
VC -> AC        [']
# ... or not
VC -> VCV       [V4]
# more than one vowel possible
VCV -> VCV      [V4]
# accented vowel
VC -> start     [V1]
VCV -> start    [V1;']
# one syllable more ending in consonant other than s, n
VCV -> end      [X-n,s]
# two or more syllables more
VCV -> VCVC     [X]
VCVC -> VCVC    [X]
VCVC -> start   [V;']

start ->
end ->
