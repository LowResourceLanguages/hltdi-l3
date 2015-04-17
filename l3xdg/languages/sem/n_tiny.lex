########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2012
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
#   Author: Michael Gasser <gasser@cs.indiana.edu>
#
# THING lexical entries
#
# 2012.11.12

### Templates
## Common things, including masses
**common
# non-predicate / referential
-  word: %lex%
   classes: [%class%]
   sem:
      agrs: {pers: [[0,0]]}
# predicate
-  word: %lex%_PRED
   classes: [THING_PRED]
   sem:
      agrs: {pers: [[0,0]]}
      govern: {arg1: [cat, %cat%]}
## Names
**name
# referential/non-predicate
-  word: %lex%
   classes: [%class%]
   sem:
      outs: {dem: 0, poss: 0}
      agrs: {def: 1, pers: [[0,0]], num: 1}

&& **common
%lex%: HOUSE
%class%: PHYSOBJ
%cat%: 2

&& **common
%lex%: FLOWER
%class%: PHYSOBJ
%cat%: 2

&& **common
%lex%: CITY
%class%: PHYSOBJ
%cat%: 2

&& **common
%lex%: HILL
%class%: PHYSOBJ
%cat%: 2

&& **common
%lex%: TELESCOPE
%class%: PHYSOBJ
%cat%: 2

&& **common
%lex%: CORN
%class%: MASS
%cat%: 2

&& **common
%lex%: WATER
%class%: MASS
%cat%: 2

&& **common
%lex%: ICE
%class%: MASS
%cat%: 2

&& **common
%lex%: WOMAN
%class%: HUMAN
%cat%: 1

&& **common
%lex%: MAN
%class%: HUMAN
%cat%: 1

&& **common
%lex%: PERSON
%class%: HUMAN
%cat%: 1

&& **common
%lex%: CHILD
%class%: HUMAN
%cat%: 1

&& **common
%lex%: BOY
%class%: HUMAN
%cat%: 1

&& **common
%lex%: GIRL
%class%: HUMAN
%cat%: 1

&& **common
%lex%: DOCTOR
%class%: HUMAN
%cat%: 1

&& **common
%lex%: TEACHER
%class%: HUMAN
%cat%: 1

&& **common
%lex%: ETHIOPIAN
%class%: HUMAN
%cat%: 1

&& **common
%lex%: PARAGUAYAN
%class%: HUMAN
%cat%: 1

&& **common
%lex%: UNITED_STATESIAN
%class%: HUMAN
%cat%: 1

&& **name
%lex%: ESTHER
%class%: HUMAN

&& **name
%lex%: PETER
%class%: HUMAN

&& **name
%lex%: JOHN
%class%: HUMAN

&& **name
%lex%: ASUNCIÓN
%class%: PLACE

&& **name
%lex%: ADDIS_ABEBA
%class%: PLACE

#-  word: INFLUENZA
#   classes: [CONDITION]
