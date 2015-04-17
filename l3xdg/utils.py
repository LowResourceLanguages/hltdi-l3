########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2012 The HLTDI L^3 Team <gasser@cs.indiana.edu>
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
#########################################################################

"""
Some utility functions and constants needed in different places in l3xdg.
"""

PARSE = 1
GENERATE = 2
TRANSLATE = 3

LEN_THRESH = 10

# Dimension names
# All possible dimension abbreviations

DIMENSIONS = {'arc': {'id', 'lp', 'pa', 'syn', 'sem'},
              'if': {'idlp', 'idsem', 'synsem', 'synsyn', 'idid'},
              'transfer': {'idid'},
              # between languages and semantics
              'semif': {'idsem', 'idpa', 'synsem'}, 
              # between languages
              'crossif': {'idid', 'synsyn'},
              'surface': {'id', 'syn'},
              'order': {'lp', 'syn'},
              'semantics': {'sem', 'pa'}}
ALL_DIMENSIONS = {'id', 'lp', 'pa', 'idlp', 'idsem', 'idpa', 'syn', 'sem', 'synsem', 'synsyn', 'idid'}

#def print_long(collection):
#    for c in list(collection)[:LEN_TRESH]:
#        print(c)
#    if len(collection) > LEN_THRESH:
#        print('...')
        


