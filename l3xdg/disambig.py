# Implementation of disambiguators
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2012, 2013, 2014
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
# =========================================================================
#
# 2012.11.07
# -- created
# 2013.06.22
# -- started on LexDisambig ...
# 2013.10.29
# -- Arc disambiguation should also constrain *possible* arcs out of nodes
#    on the basis of the distance to possible daughters. (Labels need
#    maximum distances for this.)
#########################################################################

class Disambiguator:
    """Abstract class for disambiguators.

    A function that updates the scores of node entries based on other node entries
    and their scores."""

    def __init__(self, xdg, node, dim):
        """
        Assign xdg, node, and dimension
        """
        self.xdg = xdg
        self.node = node
        self.dim = dim

    def update(self):
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

class ArcDisambig(Disambiguator):
    """Disambiguator that uses required or possible arcs to reward or punish entries."""

class ArcExcludeDisambig(ArcDisambig):
    """Disambiguator that excludes an entry because a required in or out arc is not possible
    among other nodes."""

    def __init__(self, xdg, node, dim, out=True):
        Disambiguator.__init__(self, xdg, node, dim)
        self.out = out
        # Set of possible arc labels in opposite direction from/to
        # nodes other than self.node
        self.set_possible_labels()
        # List of required arcs for each entry of node
        self.set_required_labels()

    def __repr__(self):
        return 'ArcDA {}/{}/{}'.format(self.node, self.dim.abbrev, 'out' if self.out else 'in')

    def set_possible_labels(self):
        """Assign possible labels for other nodes on this dimension
        in the other direction from self.out."""
        arcs = set()
        for node in self.xdg.get_nodes():
            if node == self.node:
                continue
            arcs1 = node.get_possible_labels(self.dim, not self.out)
            arcs.update(arcs1)
        self.possible = arcs

    def set_required_labels(self):
        """Assign required labels for each entry in self.node."""
        self.required = [self.node.get_required_labels(e, self.dim, self.out) for e in self.node.entries]

    def update(self, verbosity=0):
        """Update scores for each entry. Return True if score changed."""
        if verbosity:
            print('Running {}'.format(self))
        change = False
        # For each node, check to see whether its required arcs are included in the possible list.
        for index, (entry, required, score) in enumerate(zip(self.node.entries, self.required, self.node.scores)):
            if score >= 0:
                # Only update scores for entries that haven't been excluded
                if not set(required).issubset(self.possible):
                    if verbosity:
                        print('Required ({}) is not a subset of possible ({}) on {}'.format(required, self.possible, ))
                        print('Penalizing entry {} for {}'.format(index, self.node))
                    self.node.scores[index] = -1
                    change = True
        return change

class LexDisambig(Disambiguator):
    """Disambiguator that ranks entries based on their frequency and context."""

    def __init__(self, xdg, node, dim):
        Disambiguator.__init__(self, xdg, node, dim)

    def __repr__(self):
        return 'LexDA {}'.format(self.node)

    def update(self, verbosity=0):
        """Update scores for each entry. Return True if score changed."""
        if verbosity:
            print('Running {}'.format(self))
        change = False
        # Update (once) based on frequencies
        for index, entry in enumerate(self.node.entries):
            if self.node.scores[index] >= 0:
                # Ignore any entry with a negative score
                pass
        return change
