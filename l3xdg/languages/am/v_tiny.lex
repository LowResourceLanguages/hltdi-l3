#######################################################################
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

# Amharic verb lexical entries
#
# 2012.12.13

#### Templates

**intrans
# vars: %lex%, %root%, %der%, %sem%
# non-relative
- lexeme: %lex%
  classes: [V_I]
  root: %root%
  id:
    agrs: {der: [%der%]}
  cross:
    sem:
      lex: %sem%
      idsem:
        lbstart: {arg1: [sb]}
        agree: [[reltime, tm]]
#- lexeme: %lex%
#  classes: [V_I, V_INDEP_RELSB]
#  root: %root%
#  id:
#    agrs: {der: [%der%]}
#  cross:
#    sem:
#      lex: %sem%
#      idsem:
#        lbstart: {arg1: [sb]}
#        agree: [[reltime, tm]]
#- lexeme: %lex%
#  classes: [V_I, V_REL_SB]
#  root: %root%
#  id:
#    agrs: {der: [%der%]}
#  cross:
#    sem:
#      lex: %sem%
#      idsem:
#        lbstart: {arg1: [sb]}
#        agree: [[reltime, tm]]

**trans
# vars: %lex%, %root%, %der%, %sem%
- lexeme: %lex%
  classes: [V_T]
  root: %root%
  id:
    agrs: {der: [%der%]}
  cross:
    sem:
      lex: %sem%
      idsem:
        lbstart: {arg1: [sb], arg2: [ob]}
#        arg: {arg1: [sb]}
        agree: [[reltime, tm]]

**impers
# later fix tense/aspect/reltime
# vars: %lex%, %root%, %der%, %sem%
- lexeme: %lex%
  classes: [ANIM_STATE]
  root: %root%
  id:
    agrs: {der: [%der%]}
  cross:
    sem:
      lex: %sem%
      idsem:
        lbstart: {arg1: [top]}
      sem:
        agrs: {reltime: [[0]]}

#### Entries

## intransitive

&& **intrans
%lex%: tebekele
%root%: bk_l
%der%: [2,1]
%sem%: BE_CONTAMINATED

&& **intrans
%lex%: mote
%root%: mwt
%der%: [1,1]
%sem%: DIE

&& **intrans
%lex%: ferese
%root%: frs
%der%: [1,1]
%sem%: COLLAPSE

&& **intrans
%lex%: tameme
%root%: "'mm"
%der%: [2,1]
%sem%: SICK

## transitive

&& **trans
%lex%: Terege
%root%: Trg
%der%: [1,1]
%sem%: CLEAN

&& **trans
%lex%: "'aye"
%root%: "'y*"
%der%: [1,1]
%sem%: SEE

&& **trans
%lex%: "'aTelele"
%root%: Tl_l
%der%: [3,1]
%sem%: FILTER

&& **trans
%lex%: "'adane"
%root%: "d'n"
%der%: [3,1]
%sem%: CURE

&& **trans
%lex%: tekeraye
%root%: "kray*"
%der%: [2,1]
%sem%: RENT_V

&& **impers
%lex%: dekeme
%root%: dkm
%der%: [1,1]
%sem%: TIRED

&& **impers
%lex%: selece
%root%: slc
%der%: [1,1]
%sem%: BORED
