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
# English adjective lexical entries
#
# 2012.12.13

#### Templates

## adjectives 
# vars: %lex%, %sem%

**adj
-  word: %lex%
   classes: [ADJ]
   cross:
      sem:
      -  lex: %sem%
         idsem:
            arg: {arg1: [sb]}
            agree: [[reltime, tns]]
      -  revempty: true
         inslex: '%COP_FIN'
         arc: padj
         rel: [mother]

#### Entries

&& **adj
%lex%: dirty
%sem%: DIRTY

&& **adj
%lex%: tired
%sem%: TIRED

&& **adj
%lex%: American
%sem%: BE_UNITED_STATESIAN

&& **adj
%lex%: Ethiopian
%sem%: BE_ETHIOPIAN
