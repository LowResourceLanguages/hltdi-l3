########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2012, 2013
#   The HLTDI L^3 Team <gasser@cs.indiana.edu>
#   
#   This program is free software: you can redistribute it and/or
#   modify it under the terms of the GNU General Public License as
#   published by the Free Software Foundation, either version 3 of
#   the License, or (at your option) any later version.
#   
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#   GNU General Public License for more details.
#   
#   You should have received a copy of the GNU General Public License
#   along with this program. If not, see <http://www.gnu.org/licenses/>.
#
#    Author: Michael Gasser <gasser@cs.indiana.edu>
#
# Semantic "verb" lexicon
#
# 2012.11.14

#### Templates
### Intransitive processes with no subcat constraint on arg1
# vars: %lex%, %class%
**intrans
-  word: %lex%
   classes: [PROC_I, %class%]

### Intransitive processes with subcat constraint on arg1
# vars: %lex%, %class%, %cat%
**intrans_subcat
-  word: %lex%
   classes: [PROC_I, %class%]
   sem:
      govern: {arg1: [cat, %cat%]}

### Transitive processes with no subcat constraints
# vars: %lex%, %class%
**trans_nosubcat
-  word: %lex%
   classes: [PROC_T, %class%]

### Transitive processes with subcat constraint on arg1
# vars: %lex%, %class%, %cat1%
**trans
-  word: %lex%
   classes: [PROC_T, %class%]
   sem:
      govern: {arg1: [cat, %cat1%]}

### Transitive processes with subcat constraint on arg2
# vars: %lex%, %class%, %cat1%, %cat2%
**trans_subcat
-  word: %lex%
   classes: [PROC_T, %class%]
   sem:
      govern: {arg2: [cat, %cat2%],
               arg1: [cat, %cat1%]}

#### Entries
## Intransitive

&& **intrans
%lex%: DIE
%class%: COS

&& **intrans
%lex%: LIVE
%class%: COS

&& **intrans
%lex%: COME
%class%: COS

&& **intrans_subcat
%lex%: SPEAK
%class%: COS
%cat%: 1

&& **intrans_subcat
%lex%: FLOW
%class%: COS
%cat%: 2

&& **intrans_subcat
%lex%: BE_CONTAMINATED
%class%: STATE
%cat%: 2

&& **intrans_subcat
%lex%: COLLAPSE
%class%: COS
%cat%: 2

# break the ice
&& **intrans_subcat
%lex%: ALLEVIATE_SOCIAL_TENSION
%class%: COS
%cat%: 1

&& **intrans
%lex%: DIRTY
%class%: STATE

&& **intrans_subcat
%lex%: TIRED
%class%: STATE
%cat%: 1

&& **intrans_subcat
%lex%: BORED
%class%: STATE
%cat%: 1

&& **intrans_subcat
%lex%: SICK
%class%: STATE
%cat%: 1

&& **intrans_subcat
%lex%: REMEMBER_I
%class%: STATE
%cat%: 1

&& **intrans_subcat
%lex%: BE_ETHIOPIAN
%class%: STATE
%cat%: 1

&& **intrans_subcat
%lex%: BE_UNITED_STATESIAN
%class%: STATE
%cat%: 1

&& **intrans_subcat
%lex%: BE_PARAGUAYAN
%class%: STATE
%cat%: 1

## Transitive COS

&& **trans_subcat
%lex%: PLANT_V
%class%: COS
%cat1%: 1
%cat2%: 2

&& **trans_subcat
%lex%: RENT_V
%class%: COS
%cat1%: 1
%cat2%: 2

&& **trans_subcat
%lex%: CLEAN
%class%: COS
%cat1%: 1
%cat2%: 2

&& **trans_subcat
%lex%: CURE
%class%: COS
%cat1%: 1
%cat2%: 1

&& **trans_subcat
%lex%: BUY
%class%: COS
%cat1%: 1
%cat2%: 2

&& **trans_subcat
%lex%: BREAK
%class%: COS
%cat1%: 1
%cat2%: 2

&& **trans_subcat
%lex%: FILTER
%class%: COS
%cat1%: 1
%cat2%: 2

&& **trans
%lex%: SEE
%class%: COS
%cat1%: 1

## Transitive states

&& **trans_nosubcat
%lex%: BE_IN
%class%: STATE

&& **trans_nosubcat
%lex%: BE_ON
%class%: STATE

&& **trans
%lex%: FEAR
%class%: STATE
%cat1%: 1

&& **trans
%lex%: REMEMBER
%class%: STATE
%cat1%: 1

&& **trans
%lex%: FORGET
%class%: STATE
%cat1%: 1

# suffer from a disease (have/padecer/tener)
&& **trans_subcat
%lex%: SUFFER
%class%: STATE
%cat1%: 1
%cat2%: 2

# not for "possessing" a brother, etc.
&& **trans_subcat
%lex%: POSSESS
%class%: STATE
%cat1%: 1
%cat2%: 2
