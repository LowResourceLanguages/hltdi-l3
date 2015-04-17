########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2013, 2014
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
# 2013.11.05
# -- Created.
#    Learn lexical entries or crosslexes.

from .xdg import *

class Learner:

    def __init__(self, 
                 # Source and target languages
                 source=None, target=None,
                 # Semantics or None
                 semantics=None,
                 # Grammar to use for the language(s)
                 grammar='chunk')
        self.grammar = grammar
        self.source = source
        self.target = target
        self.bitext = True if target else False
        self.semantics = semantics

    def __repr__(self):
        return 'Learner:{}{}'.format(self.source.abbrev, self.target.abbrev if self.target else '')

    def mono(self, language, sentence, solutions, novel):
        """Given (possibly incomplete) solutions for sentence and one or more novel nodes,
        attempt to add the words to the lexicon."""
        print("Attempting to learn new entries for novel nodes {}".format(novel))
        for cls in language.lexicon.classes.values():
            for entry in cls.entries:
                pass

    def bi(self, slex, tlex):
        """Given lexical entries in source and target, learn
        a crosslex associating them."""
        pass
