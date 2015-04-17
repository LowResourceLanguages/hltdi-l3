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
# Amharic noun lexicon
#
# 2012.12.12

#### Templates

**common
# vars: %lex%, %sem%, %gen%
# non-possessive
- lexeme: %lex%
  classes: [N_C]
  root: %lex%
  id:
    agrs: {png: [[0,0,0,%gen%],[0,0,1]],
           poss: 0}
  cross:
    sem:
      lex: %sem%
      idsem:
        mod: {dem: [nhead]}
        # when this is "head" of relative clause
        ldend: {coref: [antec]}
#        arg: {coref: [sb, ob]}
        agree: [[def, def], [num, num]]
# possessive
- lexeme: %lex%
  classes: [N_C]
  empty: ['@POSS']
  root: %lex%
  id:
    outs: {poss: '!'}
    agrs: {png: [[0,0,0,%gen%],[0,0,1]],
           def: 1,
           poss: [[1,0,0],[0,1,0,0],[0,1,0,1],[0,0,0,0],[0,0,0,1],[1,0,1],[0,1,1],[0,0,1]]}
    agree: [[poss, poss, png]]
#  lp:
#    outs: {detf: 0}
  cross:
    sem:
      lex: %sem%
      idsem:
        mod: {dem: [nhead]}
        # when this is "head" of relative clause
        ldend: {coref: [antec]}
#        arg: {coref: [sb, ob]}
        ldend: {poss: [poss]}
        agree: [[def, def], [num, num]]

**name
# vars: %lex%, %sem%, %gen%
- lexeme: %lex%
  classes: [N_NAME]
  root: %lex%
  id:
    agrs: {png: [[0,0,0,%gen%]]}
  cross:
    sem:
      lex: %sem%
      idsem:
        agree: [[def, def], [num, num]]

## Common nouns with different possible genders, like ሀኪም
**mult_gen
# vars: %lex%, %sem_m%, %sem_f%
# non-possessive
- lexeme: %lex%
  classes: [N_C]
  root: %lex%
  id:
    agrs: {png: [[0,0,0,0],[0,0,1]], poss: 0}
  cross:
    sem:
      lex: %sem_m%
      idsem:
        mod: {dem: [nhead]}
        # when this is "head" of relative clause
        ldend: {coref: [antec]}
#        arg: {coref: [sb, ob]}
        agree: [[def, def], [num, num]]
- lexeme: %lex%
  classes: [N_C]
  root: %lex%
  id:
    agrs: {png: [[0,0,0,1],[0,0,1]], poss: 0}
  cross:
    sem:
      lex: %sem_f%
      idsem:
        mod: {dem: [nhead]}
        # when this is "head" of relative clause
        ldend: {coref: [antec]}
#        arg: {coref: [sb, ob]}
        agree: [[def, def], [num, num]]
# possessive
- lexeme: %lex%
  classes: [N_C]
  empty: ['@POSS']
  root: %lex%
  id:
    outs: {poss: '!'}
    agrs: {png: [[0,0,0,0],[0,0,1]],
           def: 1,
           poss: [[1,0,0],[0,1,0,0],[0,1,0,1],[0,0,0,0],[0,0,0,1],[1,0,1],[0,1,1],[0,0,1]]}
    agree: [[poss, poss, png]]
  cross:
    sem:
      lex: %sem_m%
      idsem:
        mod: {dem: [nhead]}
        # when this is "head" of relative clause
        ldend: {coref: [antec]}
#        arg: {coref: [sb, ob]}
        ldend: {poss: [poss]}
        agree: [[def, def], [num, num]]
- lexeme: %lex%
  classes: [N_C]
  empty: ['@POSS']
  root: %lex%
  id:
    outs: {poss: '!'}
    agrs: {png: [[0,0,0,1],[0,0,1]],
           def: 1,
           poss: [[1,0,0],[0,1,0,0],[0,1,0,1],[0,0,0,0],[0,0,0,1],[1,0,1],[0,1,1],[0,0,1]]}
    agree: [[poss, poss, png]]
  cross:
    sem:
      lex: %sem_f%
      idsem:
        mod: {dem: [nhead]}
        # when this is "head" of relative clause
        ldend: {coref: [antec]}
#        arg: {coref: [sb, ob]}
        ldend: {poss: [poss]}
        agree: [[def, def], [num, num]]

#### Entries

# common nouns
&& **common
%lex%: bEt
%sem%: HOUSE
%gen%: 0

&& **common
%lex%: sEt
%sem%: WOMAN
%gen%: 1

&& **common
%lex%: wend
%sem%: MAN
%gen%: 0

&& **common
%lex%: wha
%sem%: WATER
%gen%: 0

&& **common
%lex%: korebta
%sem%: HILL
%gen%: 0

&& **common
%lex%: ketema
%sem%: CITY
%gen%: 1

&& **common
%lex%: "'ityoP_yawi"
%sem%: ETHIOPIAN
%gen%: 0

&& **common
%lex%: "'ityoP_yawit"
%sem%: ETHIOPIAN
%gen%: 1

&& **mult_gen
%lex%: hakim
%sem_m%: DOCTOR
%sem_f%: DOCTOR

&& **mult_gen
%lex%: "'astemari"
%sem_m%: TEACHER
%sem_f%: TEACHER

&& **mult_gen
%lex%: lj
%sem_m%: BOY
%sem_f%: GIRL

&& **name
%lex%: "'astEr"
%gen%: 1
%sem%: ESTHER

&& **name
%lex%: yohan_s
%gen%: 0
%sem%: JOHN

