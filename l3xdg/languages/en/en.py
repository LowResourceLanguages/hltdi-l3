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
# English greatly simplified
#
# 2009.10.31
# Added groups: 'had an argument', 'BREAK the ice'
#
# 2010.01.05
# Added id and lp dimensions
#
# 2013.03.21
# Added chunk grammar to grammar dict for English

from ... import language

## English agrs features
## case(rl):  one value (nom=0, acc=1, to=2, in=3, on=4, others=5)

ENGLISH = {'': language.Language('English', 'en', morph_processing=False,
                                 labels={'en-id':  ['adj', 'adv', 'comp', 'det', 'iob', 'ob', 'part',
                                                    'pmod', 'pob1', 'pob2', 'prpc', 'rel',
                                                    'sub', 'sb', 'vbse', 'vinf', 'vpspt',
                                                    # Beyond diss grammar
                                                    'vprog',  # Progressive -ing
                                                    'padj',   # Predicate adjective
                                                    'del', 'root'],
                                         'en-lp':  ['adjf', 'compf', 'detf', 'fadvf', 'lbf', 'mf1', 'mf2',
                                                    'nf', 'padjf', 'padvf', 'prpcf', 'rbf', 'relf',
                                                    'rprof', 'tadvf', 'vf', 'vvf',
                                                    'del', 'root']
                                         }
                                 ),
           'chunk': language.Language('English', 'en', morph_processing=False,
                                      labels={'en-syn':  [# NP
                                                          'det', 'adj',
                                                          # PP
                                                          'pcomp',
                                                          # V
                                                          'arg',
                                                          # other
                                                          'root', 'del'
                                                         ]
                                              },
                                      lexicon_name='chunk'
                                      ), 
           'water': language.Language('English', 'en', morph_processing=False,
                                      labels={'en-id':  ['adj', 'adv', 'comp', 'det', 'iob', 'ob', 'part',
                                                         'pmod', 'pob1', 'pob2', 'prpc', 'rel',
                                                         'sub', 'sb', 'vbse', 'vinf', 'vpspt',
                                                         'vprog', 'padj', 'del', 'root'],
                                              'en-lp':  ['adjf', 'compf', 'detf', 'fadvf', 'lbf', 'mf1', 'mf2',
                                                         'nf', 'padjf', 'padvf', 'prpcf', 'rbf', 'relf',
                                                         'rprof', 'tadvf', 'vf', 'vvf',
                                                         'del', 'root']
                                              },
                                      lexicon_name='water'
                                      ), 
            'tiny': language.Language('English', 'en', morph_processing=False,
                                      labels={'en-id': ['det', 'ob', 'sb', 'del', 'vmain',
                                                        # Added 11.09.14
                                                        'padj',
                                                        # Added 11.12.03 (for prepositions)
                                                        'pmod', 'pcomp',
                                                        # Added 12.04.14 (attributive adjectives)
                                                        'adj',
                                                        'root'], 
                                              'en-lp': ['detf',
                                                        # mf2: ob, predadj, prednom, vf: sb
                                                        'mf2', 'vf',
                                                        # lbf: main verb following AUX
                                                        'lbf',
                                                        # Added 11.12.03 (for prepositions)
                                                        'pcompf', 'padvf', 'padjf',
                                                        # Added 12.04.14 (attributive adjectives)
                                                        'adjf',
                                                        'del', 'root']
                                              }, 
                                      lexicon_name='tiny'
                                      )
            }
