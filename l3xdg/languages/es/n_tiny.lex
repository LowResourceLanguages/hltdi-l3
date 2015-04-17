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
#    Author: Michael Gasser <gasser@cs.indiana.edu>
#
# Spanish noun lexicon
#
# 2012.11.13

#### Templates

## Numerables
**num
# vars: %sing%, %plur%, %pers%, %gen%, %sem%
# singular, referencial
- word: %sing%
  classes: [N_SG, %pers%]
  id:
    ins: {npred: 0}
    agrs: {gen: %gen%}
  cross:
    sem:
    - revempty: true
      inslex: '%DET'
      arc: det
    - lex: %sem%
      idsem:
        agree: [[def, def], [num, num]]
        # coref if this is the head of a relative clause
        # arg1 if this is a predicate nominal
        ldend: {dem: [det], poss: [det], coref: [antec]}
# singular, predicativo
- word: %sing%
  classes: [N_SG, %pers%]
  id:
    ins: {npred: '!', sj: 0, ojd: 0, oji: 0, pcomp: 0}
    agrs: {gen: %gen%, tam: [[0], [1]]}
  cross:
    sem:
    - revempty: true
      inslex: '%DET'
      arc: det
    - revempty: true
      inslex: '%ser'
      arc: npred
      rel: [mother]
    - lex: %sem%_PRED
      idsem:
        agree: [[def, def], [num, num], [reltime, tam]]
        # coref if this is the head of a relative clause
        ldend: {dem: [det], poss: [det], coref: [antec]}
        arg: {arg1: [sj]}
# plural, referencial
- word: %plur%
  classes: [N_PL, %pers%]
  id:
    ins: {npred: 0}
    agrs: {gen: %gen%}
  cross:
    sem:
    - revempty: true
      inslex: '%DET'
      arc: det
    - lex: %sem%
      idsem:
        agree: [[def, def], [num, num]]
        # coref if this is the head of a relative clause
        # arg1 if this is a predicate nominal
        ldend: {dem: [det], poss: [det], coref: [antec]}
# plural, predicativo
- word: %plur%
  classes: [N_PL, %pers%]
  id:
    ins: {npred: '!', sj: 0, ojd: 0, oji: 0, pcomp: 0}
    agrs: {gen: %gen%, tam: [[0], [1]]}
  cross:
    sem:
    - revempty: true
      inslex: '%DET'
      arc: det
    - revempty: true
      inslex: '%ser'
      arc: npred
      rel: [mother]
    - lex: %sem%_PRED
      idsem:
        agree: [[def, def], [num, num], [reltime, tam]]
        # coref if this is the head of a relative clause
        # arg1 if this is a predicate nominal
        ldend: {dem: [det], poss: [det], coref: [antec]}
        arg: {arg1: [sj]}

### No numerables
**nonum
# vars: %sing%, %gen%, %sem%
# referencial, definido
- word: %sing%
  classes: [N_M, N_DEF]
  id:
    ins: {npred: 0}
    agree: [[det, def, def],[det, gen, gen],[det, num, num]]
    agrs: {gen: %gen%}
  cross:
    sem:
    - revempty: true
      inslex: '%DET'
      arc: det
    - lex: %sem%
      idsem:
        agree: [[def, def]]
        # coref if this is the head of a relative clause
        # arg1 if this is a predicate nominal
        ldend: {dem: [det], poss: [det], coref: [antec]}
# predicativo, definido
- word: %sing%
  classes: [N_M, N_DEF]
  id:
    ins: {npred: '!', sj: 0, ojd: 0, oji: 0, pcomp: 0}
    agrs: {gen: %gen%, tam: [[0], [1]]}
  cross:
    sem:
    - revempty: true
      inslex: '%DET'
      arc: det
    - revempty: true
      inslex: '%ser'
      arc: npred
      rel: [mother]
    - lex: %sem%_PRED
      idsem:
        agree: [[def, def], [reltime, tam]]
        # coref if this is the head of a relative clause
        ldend: {dem: [det], poss: [det], coref: [antec]}
        arg: {arg1: [sj]}
# referencial, indefinido
- word: %sing%
  classes: [N_M, N_INDEF]
  id:
    ins: {npred: 0}
    outs: {det: 0}
    agrs: {gen: %gen%}
  cross:
    sem:
    - lex: %sem%
      idsem:
        agree: [[def, def]]
        # coref if this is the head of a relative clause
	# poss is here to *prevent* it from appearing spuriously in semantics
        ldend: {coref: [antec], poss: [det]}

# predicativo, indefinido
- word: %sing%
  classes: [N_M, N_INDEF]
  id:
    ins: {npred: '!', sj: 0, ojd: 0, oji: 0, pcomp: 0}
    outs: {det: 0}
    agrs: {gen: %gen%, tam: [[0], [1]]}
  cross:
    sem:
    - revempty: true
      inslex: '%ser'
      arc: npred
      rel: [mother]
    - lex: %sem%_PRED
      idsem:
        agree: [[def, def], [reltime, tam]]
        # coref if this is the head of a relative clause
	# poss is here to *prevent* it from appearing spuriously in semantics
        ldend: {coref: [antec], poss: [det]}
        arg: {arg1: [sj]}

### Nombres
**nombre
# vars: %lex%, %pers%, %gen%, %sem%
- word: %lex%
  classes: [N_NAME, %pers%]
  id:
    agrs: {gen: %gen%}
  cross:
    sem:
    - lex: %sem%
      idsem:
        # coref if this is the head of a relative clause
	# poss is here to *prevent* it from appearing spuriously in semantics
        ldend: {coref: [antec], poss: [det]}

#### Entries

# Names
&& **nombre
%lex%: Ester
%pers%: N_PERS
%gen%: 1
%sem%: ESTHER

&& **nombre
%lex%: Pedro
%pers%: N_PERS
%gen%: 0
%sem%: PETER

&& **num
%sing%: mujer
%plur%: mujeres
%pers%: N_PERS
%gen%: 1
%sem%: WOMAN

&& **num
%sing%: muchacho
%plur%: muchachos
%pers%: N_PERS
%gen%: 0
%sem%: BOY

&& **num
%sing%: muchacha
%plur%: muchachas
%pers%: N_PERS
%gen%: 1
%sem%: GIRL

&& **num
%sing%: casa
%plur%: casas
%pers%: N_IMPERS
%gen%: 1
%sem%: HOUSE

&& **num
%sing%: ciudad
%plur%: ciudades
%pers%: N_IMPERS
%gen%: 1
%sem%: CITY

&& **num
%sing%: colina
%plur%: colinas
%pers%: N_IMPERS
%gen%: 1
%sem%: HILL

&& **num
%sing%: paraguayo
%plur%: paraguayos
%pers%: N_PERS
%gen%: 0
%sem%: PARAGUAYAN

&& **num
%sing%: paraguaya
%plur%: paraguayas
%pers%: N_PERS
%gen%: 1
%sem%: PARAGUAYAN

&& **num
%sing%: telescopio
%plur%: telescopios
%pers%: N_IMPERS
%gen%: 0
%sem%: TELESCOPE

&& **num
%sing%: flor
%plur%: flores
%pers%: N_IMPERS
%gen%: 1
%sem%: FLOWER

&& **nonum
%sing%: maíz
%gen%: 0
%sem%: CORN

#- word: gripe
#  classes: [N_SG, N_IMPERS]
#  id:
#    agrs: {gen: [[1]], def: [[0]]}
#  cross:
#    sem:
#      lex: INFLUENZA
