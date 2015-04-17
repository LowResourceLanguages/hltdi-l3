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
#
# English lexical entries
#
# 2012.12.13

#### Templates

## Intransitive
# vars: %lex%, %sem%, %stem%, %past%, %pres%, %prespart%

**intrans
-  lexeme: %lex%
   shared:
      classes: [V_I]
      cross:
         sem:
            lex: %sem%
            idsem:
               arg: {arg1: [sb]}
               agree: [[reltime, tns]]
#         am:
#            lex: %am%
#            idid:
#               arg: {sb: [sb]}
#               agree: [[tm, tns]]
   partition:
   -  morph: %past%
      classes: [V_PS]
   -  morph: %pres%
      classes: [V_3SG]
   -  morph: %stem%
      classes: [V_NON3SG]
   -  morph: %prespart%
      classes: [V_PRSPART]

## Transitive
# vars: %lex%, %sem%, %stem%, %past%, %pres%, %prespart%

**trans
-  lexeme: %lex%
   shared:
      classes: [V_T]
      cross:
         sem:
            lex: %sem%
            idsem:
               ldend: {arg2: [ob]}
               arg: {arg1: [sb]}
               agree: [[reltime, tns]]
   partition:
   -  morph: %past%
      classes: [V_PS]
   -  morph: %pres%
      classes: [V_3SG]
   -  morph: %stem%
      classes: [V_NON3SG]
   -  morph: %prespart%
      classes: [V_PRSPART]

#### Entries

&& **intrans
%lex%: ~V~die
%sem%: DIE
%stem%: die
%pres%: dies
%past%: died
%prespart%: dying
#%am%: mote

&& **intrans
%lex%: ~V~come
%sem%: COME
%stem%: come
%pres%: comes
%past%: came
%prespart%: coming

&& **intrans
%lex%: ~V~speak
%sem%: SPEAK
%stem%: speak
%pres%: speaks
%past%: spoke
%prespart%: speaking

&& **intrans
%lex%: ~V~flow
%sem%: FLOW
%stem%: flow
%pres%: flows
%past%: flowed
%prespart%: flowing

&& **trans
%lex%: ~V~filter
%sem%: FILTER
%stem%: filter
%pres%: filters
%past%: filtered
%prespart%: filtering

&& **trans
%lex%: ~V~clean
%sem%: CLEAN
%stem%: clean
%pres%: cleans
%past%: cleaned
%prespart%: cleaning

&& **trans
%lex%: ~V~buy
%sem%: BUY
%stem%: buy
%pres%: buys
%past%: bought
%prespart%: buying

&& **trans
%lex%: ~V~cure
%sem%: CURE
%stem%: cure
%pres%: cures
%past%: cured
%prespart%: curing

&& **trans
%lex%: ~V~see
%sem%: SEE
%stem%: see
%pres%: sees
%past%: saw
%prespart%: seeing
# %am%: "'aye"

&& **trans
%lex%:  ~V~break
%sem%: BREAK
%stem%: break
%pres%: breaks
%past%: broke
%prespart%: breaking
