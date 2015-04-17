########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010 The HLTDI L^3 Team <gasser@cs.indiana.edu>
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
# Semantics
#
# 2011.01.28
#

from ... import language

SEMANTICS = {'': language.Language('semantics', 'sem', morph_processing=False, seg_units=None, 
                                   eos_chars=['STATEMENT', 'QUESTION', 'EXCLAMATION'],
                                   labels={'sem': ['arg1', 'arg2', 'arg3', 'del', 'vmod', 'nmod',
                                                   'loc', 'coref', 'root']}
                                   ), 
            'water': language.Language('semantics', 'sem', morph_processing=False, seg_units=None, 
                                       labels={'sem': ['arg1', 'arg2', 'arg3',
                                                       'del', 'vmod', 'nmod', 'loc', 'coref', 'root']}, 
                                       lexicon_name='water'), 
            'tiny': language.Language('semantics', 'sem', morph_processing=False, seg_units=None, 
                                      eos_chars=['STATEMENT', 'QUESTION', 'EXCLAMATION'],
                                      labels={'sem': ['arg1', 'arg2', 'arg3',
#                                                      'instr', 'loc',
                                                      'perif',
                                                      # Added 11.12.03; subordinate clause verbs
                                                      # or PREP modifiers of N
                                                      'sub',
                                                      # Added 12.08.13; semantic demonstratives
                                                      'dem',
                                                      # Added 12.08.27; possessives
                                                      'poss',
                                                      # Added 12.09.21; for relative clauses (at least)
                                                      'coref',
                                                      'del', 'root']}, 
                                      lexicon_name='tiny')
            }
