# 'V -> V+acc unless naturally accented

-> start

start -> start  [X;V;Q-']

# just delete the ' because the syllable is already accented
start -> D'     [:']
D' -> D'V       [V0]
D'V -> D'V      [V]
D'V -> end      [X-n,s]
D'V -> D'VC     [X]
D'VC -> D'VC    [X]
# next vowel is last, unaccented
D'VC -> D'VCV   [V0]
# there may be more than one vowel
D'VCV -> D'VCV  [V0]
# ... and followed by nothing or consonant other than s,n
D'VCV -> end    [s;n;:]

# delete the ' and accent the following vowel
D' -> D'Vx        [á:a;é:e;í:i;ó:o;ú:u]
D' -> D'iu        [i;u]
D'iu -> D'Vx      [á:a;é:e;ó:o]
# possible a second unaccented vowel (i, u)
D'Vx -> D'Vx      [i;u]
# last syllable
D'Vx -> end       [s;n;:]
# another consonant (or possibly none if the next vowel is 'e' or 'o'?)
D'Vx -> D'VxC     [X;:]
D'VxC -> D'VxC    [X]
D'VxC -> D'VxCV   [V]
D'VxCV -> D'VxCV  [V]
# one syllable more ending in consonant other than s, n
D'VxCV -> end     [X-n,s]
# two or more syllables more
D'VxCV -> D'VxCVC  [X]
D'VxCVC -> D'VxCVC [X]
D'VxCVC -> start   [V]

# next vowel already has an accent on it
D' -> start        [V1]

start ->
# D'V ->
end ->
