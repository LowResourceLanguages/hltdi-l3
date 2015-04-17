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

####  Guarani nouns

### Templates

## Common noun template
# vars: lex, nas, an, sem
**común
# non-predicate
- lexeme: %lex%
  classes: [N_COM]
  root: %lex%
  id:
    agrs: {nas: %nas%, an: %an%, pn: [[0,0]]}
  cross:
    sem:
    - lex: %sem%
      idsem:
#        mod: {dem: [nhead]}
        ldend: {dem: [det], poss: [det], coref: [antec]}
        agree: [[num, num],[def, def]]
# predicate
- lexeme: %lex%
  classes: [N_COM]
  root: %lex%
  id:
    ins: {root: '!', sj: 0, oj: 0, pcomp: 0}
    outs: {sj: '!'}
    agrs: {nas: %nas%, an: 1, tmp: 0, rel: 0,
           num: [[1],[2]], pn: [[0,0]]}
  lp:
    ins: {root: '!', preargf: 0, postargf: 0, pcompf: 0}
    outs: {preargf: '!'}
    order: [[preargf, ^]]
  idlp:
    ldend: {preargf: [sj]}
  cross:
    sem:
    - lex: %sem%_PRED
      idsem:
#        mod: {dem: [nhead]}
        ldend: {dem: [det], poss: [det], coref: [antec], precf: [sj]}
        agree: [[num, num],[def, def],[reltime,tmp]]

## Mass noun template
# vars: lex, nas, sem
**masa
# non-predicate
- lexeme: %lex%
  classes: [N_COM]
  root: %lex%
  id:
    agrs: {nas: %nas%, an: 0, num: 1, pn: [[0,0]]}
  cross:
    sem:
    - lex: %sem%
      idsem:
#        mod: {dem: [nhead]}
        ldend: {dem: [det], poss: [det], coref: [antec]}
        agree: [[num, num],[def, def]]
# predicate
- lexeme: %lex%
  classes: [N_COM]
  root: %lex%
  id:
    ins: {root: '!', sj: 0, oj: 0, pcomp: 0}
    outs: {sj: '!'}
    agrs: {nas: %nas%, an: 1, tmp: 0, rel: 0,
           num: 1, pn: [[0,0]]}
  lp:
    ins: {root: '!', preargf: 0, postargf: 0, pcompf: 0}
    outs: {preargf: '!'}
    order: [[preargf, ^]]
  idlp:
    ldend: {preargf: [sj]}
  cross:
    sem:
    - lex: %sem%_PRED
      idsem:
#        mod: {dem: [nhead]}
        ldend: {dem: [det], poss: [det], coref: [antec], precf: [sj]}
        agree: [[num, num],[def, def],[reltime,tmp]]

## Name template
# vars: lex, nas, an, sem
**nombre
- word: %lex%
  classes: [N_NAME]
  id:
    agrs: {nas: %nas%, an: %an%, pn: [[0,0]]}
  cross:
    sem:
      lex: %sem%

### Entries

&& **común
%lex%: <hóga
%nas%: 0
%an%: 0
%sem%: HOUSE

&& **masa
%lex%: avati
%nas%: 0
%sem%: CORN

&& **común
%lex%: yvoty
%nas%: 0
%an%: 0
%sem%: FLOWER

&& **común
%lex%: kuña
%nas%: 1
%an%: 1
%sem%: WOMAN

&& **nombre
%lex%: Ester
%nas%: 0
%an%: 1
%sem%: ESTHER

&& **nombre
%lex%: Peru
%nas%: 0
%an%: 1
%sem%: PETER
