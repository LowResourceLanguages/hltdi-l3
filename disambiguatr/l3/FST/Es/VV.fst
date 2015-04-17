# vowel sequences

-> start

start -> start  [X;V-a,I;Q]

# delete a before o and e
start -> adel   [:a]
adel -> start   [o;e]
start -> a      [a]
a -> start      [X;Q;e;i] # other vowels possible?

# delete e before o
#start -> edel   [:e]
#edel -> start   [o]
#start -> e      [e]
#e -> start      [X;Q;e;i] # other vowels possible?
#e -> edel       [:e]
#a -> edel       [:e]

# delete I before o
start -> idel   [:I]
idel -> start   [o] 
start -> i      [I]
i -> start      [X;Q;E]   # E the only vowel that can occur here?

start ->
a ->
#e ->
i ->
