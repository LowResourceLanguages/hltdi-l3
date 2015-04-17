#########################################################################
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
#   Author: Michael Gasser <gasser@cs.indiana.edu>
#
#
# Léxico de verbos españoles
#
# 2012.11.14

#### Templates
# Note: others needed for special case mappings: gustar, acordarse de, etc.

### Reflexive
# vars: %lex%, %sem%
**refl
- lexeme: %lex%
  classes: [V_REFLX, V_FINITENESS]
  root: %lex%
  cross:
    sem:
      - revempty: true
        inslex: '%PRON_OJR'
        arc: ojr
      - lex: %sem%
        idsem:
          labs: {arg1: [sj]}
          agree: [[reltime, tam]]
### Intransitive
# vars: %lex%, %sem%
**intrans
- lexeme: %lex%
  classes: [V_I, V_FINITENESS]
  root: %lex%
  cross:
    sem:
      lex: %sem%
      idsem:
        labs: {arg1: [sj]}
        agree: [[reltime, tam]]
### Transitive with inanimate object
# vars: %lex%, %sem%
**trans_inan
- lexeme: %lex%
  classes: [V_T, V_FINITENESS]
  root: %lex%
  cross:
    sem: 
      lex: %sem%
      idsem:
        labs: {arg1: [sj]}
        ldend: {arg2: [ojd]}
        agree: [[reltime, tam]]
### Transitive with animate object
# vars: %lex%, %sem%
**trans_anim
- lexeme: %lex%
  classes: [V_T, V_FINITENESS]
  root: %lex%
  cross:
    sem: 
      - lex: %sem%
        idsem:
          labs: {arg1: [sj]}
          lbstart: {arg2: [ojdp]}
          agree: [[reltime, tam]]
      - revempty: true
        inslex: '%OJDP'
        arc: ojdp
### Transitive with both animate and inanimate objects
# vars: %lex%, %sem%
**trans
- lexeme: %lex%
  classes: [V_T_IMPERS, V_FINITENESS]
  root: %lex%
  cross:
    sem: 
      lex: %sem%
      idsem:
        labs: {arg1: [sj]}
        ldend: {arg2: [ojd]}
        agree: [[reltime, tam]]
- lexeme: %lex%
  classes: [V_T_PERS, V_FINITENESS]
  root: %lex%
  cross:
    sem: 
      - lex: %sem%
        idsem:
          labs: {arg1: [sj]}
          lbstart: {arg2: [ojdp]}
          agree: [[reltime, tam]]
      - revempty: true
        inslex: '%OJDP'
        arc: ojdp

#### Entries

&& **refl
%lex%: morir
%sem%: DIE

&& **refl
%lex%: acordar
%sem%: REMEMBER_I

&& **intrans
%lex%: hablar
%sem%: SPEAK

&& **intrans
%lex%: venir
%sem%: COME

&& **intrans
%lex%: vivir
%sem%: LIVE

&& **trans_inan
%lex%: plantar
%sem%: PLANT_V

&& **trans_inan
%lex%: limpiar
%sem%: CLEAN

# tener = POSSESS only
&& **trans_inan
%lex%: tener
%sem%: POSSESS

&& **trans_anim
%lex%: curar
%sem%: CURE

&& **trans
%lex%: ver
%sem%: SEE

&& **trans
%lex%: recordar
%sem%: REMEMBER

