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
# English noun lexical entries
#
# 2012.12.13

#### Templates

## names
# vars: %lex%, %sem%

**name
-  word: %lex%
   classes: [N_NAME]
   cross:
      sem:
         lex: %sem%
#      am:
#         lex: "'astEr"

## count nouns
# vars: %lex%, %sem%, %sing%, %plur%

**count
-  lexeme: %lex%
   shared:
      classes: [N_C]
      cross:
         sem:
         -  lex: %sem%
            idsem:
               agree: [[def, def], [num, num]]
               ldend: {dem: [det], poss: [det]}
#, coref: [antec]}
         -  revempty: true
            inslex: '%DET'
            arc: det
#         am:
#         -  lex: %am%
#            idid:
#               agree: [[def, def], [num, num]]
#         -  revempty: true
#            elex: zero
#            inslex: '%DET'
#            arc: det
   partition:
   -  morph: %sing%
      classes: [N_SG]
   -  morph: %plur%
      classes: [N_PL]

## mass nouns
# vars: %lex%, %sem%

**mass
-  word: %lex%
   classes: [N_MS]
   cross:
      sem:
         lex: %sem%
         idsem:
            agree: [[def, def]]
            ldend: {dem: [det], poss: [det]}
#, coref: [antec]}

#### Entries

&& **name
%lex%: Esther
%sem%: ESTHER

&& **count
%lex%: ~N~boy
%sem%: BOY
%sing%: boy
%plur%: boys

&& **count
%lex%: ~N~person
%sem%: PERSON
%sing%: person
%plur%: people

&& **count
%lex%: ~N~woman
%sem%: WOMAN
%sing%: woman
%plur%: women

&& **count
%lex%: ~N~girl
%sem%: GIRL
%sing%: girl
%plur%: girls

&& **count
%lex%: ~N~doctor
%sem%: DOCTOR
%sing%: doctor
%plur%: doctors

&& **count
%lex%: ~N~child
%sem%: CHILD
%sing%: child
%plur%: children

&& **count
%lex%: ~N~teacher
%sem%: TEACHER
%sing%: teacher
%plur%: teachers

&& **count
%lex%: ~N~house
%sem%: HOUSE
%sing%: house
%plur%: houses

&& **count
%lex%: ~N~city
%sem%: CITY
%sing%: city
%plur%: cities

&& **count
%lex%: ~N~hill
%sem%: HILL
%sing%: hill
%plur%: hills

&& **count
%lex%: ~N~telescope
%sem%: TELESCOPE
%sing%: telescope
%plur%: telescopes

&& **count
%lex%: ~N~American
%sem%: UNITED_STATESIAN
%sing%: American
%plur%: Americans

&& **count
%lex%: ~N~Ethiopian
%sem%: ETHIOPIAN
%sing%: Ethiopian
%plur%: Ethiopians

&& **mass
%lex%: water
%sem%: WATER

&& **mass
%lex%: ice
%sem%: ICE
