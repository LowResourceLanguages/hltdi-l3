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

# Guarani verbs lexicon
#
# 2012.11.14

#### Templates

## Intransitive
# vars: lex, pos, sem
**intrans
- lexeme: %lex%
  pos: %pos%
  classes: [V_I]
  root: %lex%
  cross:
    sem:
      lex: %sem%
      idsem:
        lbstart: {arg1: [sj]}
        agree: [[reltime, tmp]]

## Intransitive with postposition specified
# vars: lex, pos, posp (postposition), pospi (posposition index), sem
**intrans_posp
- lexeme: %lex%
  pos: %pos%
  classes: [V_I]
  root: %lex%
  id:
    govern: {pmod: [[pp, %pospi%]]}
  cross:
    sem:
    - lex: %sem%
      idsem:
        lbstart: {arg1: [sj]}
        arg: {arg2: [pcomp]}
        agree: [[reltime, tmp]]
    - revempty: true
      inslex: %posp%
      arc: pmod

## Transitive with inanimate object
# vars: lex, pos?, sem
**trans_inan
- lexeme: %lex%
  pos: %pos%
  classes: [V_T_OJ]
  root: %lex%
  cross:
    sem: 
      lex: %sem%
      idsem:
        lbstart: {arg1: [sj], arg2: [oj]}
#        ldend: {arg2: [oj]}
        agree: [[reltime, tmp]]

## Transitive with animate objects
**trans_anim
- lexeme: %lex%
  pos: %pos%
  classes: [V_T_OJP]
  root: %lex%
  cross:
    sem: 
    - lex: %sem%
      idsem:
        lbstart: {arg1: [sj], arg2: [oj]}
#        lbstart: {arg2: [ojp]}
        agree: [[reltime, tmp]]
    - revempty: true
      inslex: '%OJP'
      arc: ojp

## Transitive with both kinds of objects
**trans
- lexeme: %lex%
  pos: %pos%
  classes: [V_T_OJP]
  root: %lex%
  cross:
    sem: 
    - lex: %sem%
      idsem:
        lbstart: {arg1: [sj]}
        lbstart: {arg2: [ojp]}
        agree: [[reltime, tmp]]
    - revempty: true
      inslex: '%OJP'
      arc: ojp
- lexeme: %lex%
  pos: %pos%
  classes: [V_T_OJ]
  root: %lex%
  cross:
    sem: 
      lex: %sem%
      idsem:
        lbstart: {arg1: [sj], arg2: [oj]}
#        ldend: {arg2: [oj]}
        agree: [[reltime, tmp]]

#### Entries

&& **intrans
%lex%: mano
%pos%: va
%sem%: DIE

&& **intrans
%lex%: "ñe'ẽ"
%pos%: va
%sem%: SPEAK

&& **intrans
%lex%: ju
%pos%: va
%sem%: COME

&& **intrans_posp
%lex%: "mandu'a"
%pos%: vc
%sem%: REMEMBER
%posp%: rehe
%pospi%: 6

&& **intrans_posp
%lex%: <hesarái
%pos%: vc
%sem%: FORGET
%posp%: gui
%pospi%: 2

&& **trans_inan
%lex%: ñoty
%pos%: va
%sem%: PLANT_V

&& **trans_inan
%lex%: "ky'a'o"
%pos%: va
%sem%: CLEAN

&& **trans_inan
%lex%: reko
%pos%: va
%sem%: POSSESS

&& **trans
%lex%: <hecha
%pos%: va
%sem%: SEE
