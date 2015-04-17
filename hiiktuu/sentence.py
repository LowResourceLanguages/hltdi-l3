#   
#   Hiiktuu sentences and how to parse and translate them.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2014, HLTDI <gasser@cs.indiana.edu>
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

# 2014.04.15
# -- Created.
# 2014.04.19-20
# -- Group matching. GInst, GNode, and SNode classes.
# 2014.04.22
# -- Solution class.
# 2014.04.26-7
# -- Translation class and realization.
# 2014.04.28
# -- Variables for sentence analysis.
# 2014.04.29-30
# -- Fixed some constraints and initial variables values.
# 2014.05.01
# -- Handling source words that aren't "covered" (no group candidate matches them):
#    variables and source constraints.
# 2014.05.02
# -- Uncovered source words: target ordering constraints.
#    Introduced "chunks": target output units that are not connected.
# 2014.05.04-5
# -- New agreement variables and constraints.
# 2014.05.09
# -- Fixed output ordering so that order between nodes in merged groups
#    is right: all nodes in outer group before merged node must
#    precede all nodes in inner group, and all nodes in outer group
#    after merged node must follow all nodes in inner group.
# 2014.05.11
# -- Tree variables for unselected groups get removed from essential
#    variable list so the list of undetermined essential variables can
#    end up empty when it should be.
# 2014.05.15
# -- Fixed how group trees are worked out: using the snode->gnodes variables
#    rather than merger-related variables and tree variables.
# -- Search in group selection and output ordering.
# 2014.05.16
# -- Fixed a bug in how SL snodes with no corresponding TL snodes are
#    handled during node merging.
# 2014.05.18
# -- Target-language within-group agreement ("GIVES them a piece of HER/HIS mind")
# 2014.05.19
# -- all_sols argument to solve() and other methods that search finds all
#    solutions without querying user.
# -- Alignments is inferred from lexicon if not explicit.

import itertools, copy
from .ui import *
from .cs import *

class Sentence:
    """A sentence is a list of words (or other lexical tokens) that gets
    assigned a set of variables and constraints that are run during
    parsing or translation."""

    id = 0
    word_width = 10

    def __init__(self, raw='', language=None,
                 tokens=None, analyses=None,
                 nodes=None, groups=None, target=None,
                 verbosity=0):
        self.set_id()
        # A string representing the raw sentence
        self.raw = raw
        # Source language: a language object
        self.language = language
        # Target language: a language object or None
        self.target = target
        # A list of SNode objects, one for each token
        self.nodes = nodes or []
        # A list of candidate groups (realized as GInst objects) found during lexicalization
        self.groups = groups or []
        # Control messages
        self.verbosity = verbosity
        # GNodes in GInsts
        self.gnodes = []
        # Indices of covered SNodes
        self.covered_indices = []
        # A list of constraints to run
        self.constraints = []
        # Root domain store for variables
        self.dstore = DStore(name="S{}".format(self.id))
        # A dict of sentence-level variables
        self.variables = {}
        # Solver to find solutions
        self.solver = Solver(self.constraints, self.dstore,
                             description='group selection', verbosity=verbosity)
        # Solutions found during parsing
        self.solutions = []
        if verbosity:
            print("Created Sentence object {}".format(self))

    def set_id(self):
        self.id = Sentence.id
        Sentence.id += 1

    def __repr__(self):
        """Print name."""
        if self.raw:
            return '|| ({}) {} ||'.format(self.id, self.raw)
        else:
            return '|| {} sentence {} ||'.format(self.language, self.id)

    def display(self, show_all_sols=True, show_trans=True,
                word_width=0):
        """Show the sentence and one or more solutions in terminal."""
        s = "   "
        word_width = word_width or Sentence.word_width
        for node in self.nodes:
            s += "{}".format(node.token).center(word_width)
        print(s)
        solutions = self.solutions if show_all_sols else self.solutions[:1]
        for solution in solutions:
            solution.display(word_width=word_width)

#    def parse(self, verbosity=0, all_sols=False):
#        print("Attempting to parse {}".format(self))
#        if self.initialize(verbosity=verbosity):
#            self.solve(verbosity=verbosity, all_sols=all_sols)

    def initialize(self, verbosity=0):
        """Things to do before running constraint satisfaction."""
        if verbosity:
            print("Initializing {}".format(self))
        self.tokenize(verbosity=verbosity)
        self.lexicalize(verbosity=verbosity)
        if not self.groups:
            print("No groups found for {}".format(self))
            return False
        else:
            self.create_variables(verbosity=verbosity)
            self.create_constraints(verbosity=verbosity)
            return True

    def solve(self, translate=True, all_sols=False, verbosity=0):
        """Generate solutions and translations."""
        generator = self.solver.generator(test_verbosity=verbosity,
                                          expand_verbosity=verbosity)
        try:
            proceed = True
            while proceed:
                succeeding_state = next(generator)
                solution = self.create_solution(dstore=succeeding_state.dstore, verbosity=verbosity)
                if verbosity:
                    print('FOUND ANALYSIS', solution)
                if translate:
                    solution.translate(verbosity=verbosity, all_sols=all_sols)
                else:
                    # Display the parse
                    self.display()
                if all_sols:
                    continue
                if not input('SEARCH FOR ANOTHER ANALYSIS? [yes/NO] '):
                    proceed = False
        except StopIteration:
            if verbosity:
                print('No more solutions')
        if not self.solutions:
            print("NO SOLUTIONS FOUND for {}".format(self))

    def tokenize(self, verbosity=0):
        """Segment the sentence string into tokens, analyze them morphologically,
        and create a SNode object for each."""
        if verbosity:
            print("Tokenizing {}".format(self))
        if not self.nodes:
            # (Otherwise it's already done.)
            # Split at spaces by default (later allow for dedicated language-specific tokenizers).
            tokens = self.raw.split()
            self.nodes = []
            index = 0
            for token in tokens:
                # Look up token in language.forms
                if token not in self.language.forms:
                    # Not found, just use the raw string
                    self.nodes.append(SNode(token, index, None, self))
                    index += 1
                else:
                    # A dict, for unambiguous forms, or a list of dicts, for ambiguous forms
                    formdict = self.language.forms[token]
                    if isinstance(formdict, dict):
                        # A single entry
                        if 'seg' in formdict:
                            segs = formdict['seg']
                            for seg in segs:
                                tok, analysis = seg
                                self.nodes.append(SNode(tok, index, analysis, self))
                                index += 1
                        else:
                            self.nodes.append(SNode(token, index, formdict, self))
                            index += 1
                    else:
                        # Multiple dicts: ambiguity; let node handle it
                        self.nodes.append(SNode(token, index, formdict, self))
                        index += 1

    def lexicalize(self, verbosity=0):
        """Find and instantiate all groups that are compatible with the tokens in the sentence."""
        if verbosity:
            print("Lexicalizing {}".format(self))
        if not self.nodes:
            print("Tokenization must precede lexicalization.")
            return
        candidates = []
        for node in self.nodes:
            # Get keys into lexicon for this node
            keys = {node.token}
            anal = node.analyses
            if anal:
                if isinstance(anal, list):
                    for a in anal:
                        keys.add(a.get('root'))
                else:
                    keys.add(anal.get('root'))
            # Look up candidate groups in lexicon
            for k in keys:
                if k in self.language.groups:
                    for group in self.language.groups[k]:
#                        print("Checking group {} for {}".format(group, node))
                        # Reject group if it doesn't have a translation in the target language
                        if self.target and not group.get_translations(self.target.abbrev):
                            print("No translation for {}".format(group))
                            continue
                        candidates.append((node.index, group))
        # Now filter candidates to see if all words are present in the sentence
        # For each group, save a list of list of sentence token indices that correspond
        # to the group's words
        groups = []
        for head_i, group in candidates:
            # Matching snodes, along with root and unified features if any
            if verbosity > 1:
                print("Matching group {}".format(group))
            snodes = group.match_nodes(self.nodes, head_i)
            if not snodes:
                # This group is out
                if verbosity > 1:
                    print("Failed to match")
                continue
            if verbosity > 1:
                print('Group {} matches snodes {}'.format(group, snodes))
            groups.append((head_i, snodes, group))
        # Create a GInst object and GNodes for each surviving group
        self.groups = [GInst(group, self, head_i, snodes, index) for index, (head_i, snodes, group) in enumerate(groups)]
        # Assign sentence-level indices to each GNode; store gnodes in list
        sent_index = 0
        for group in self.groups:
            for gnode in group.nodes:
                gnode.sent_index = sent_index
                self.gnodes.append(gnode)
                sent_index += 1
        # Number of GNodes
        self.ngnodes = sent_index
        # Record uncovered snodes
        covered = {}
        for gnode in self.gnodes:
            si = gnode.snode_indices
            for i in si:
                if i not in covered:
                    covered[i] = []
                covered[i].append(gnode.sent_index)
        for snode in self.nodes:
            gnodes = covered.get(snode.index, [])
            snode.gnodes = gnodes
            if gnodes:
                self.covered_indices.append(snode.index)

    ## Create IVars and (set) Vars with sentence DS as root DS

    def ivar(self, name, domain, ess=False):
        self.variables[name] = IVar(name, domain, rootDS=self.dstore,
                                    essential=ess)

    def svar(self, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[name] = Var(name, lower, upper, lower_card, upper_card,
                                  essential=ess, rootDS=self.dstore)

    def create_variables(self, verbosity=0):
        # All abstract (category) and instance (word or lexeme) gnodes
        catnodes = set()
        instnodes = set()
        for group in self.groups:
            for node in group.nodes:
                if node.cat:
                    catnodes.add(node.sent_index)
                else:
                    instnodes.add(node.sent_index)
#        # Snodes that are merged with catnodes
#        merged_snodes = set()
#        for gn_index in catnodes:
#            gn = self.gnodes[gn_index]
#            merged_snodes.update(gn.snode_indices)

        self.svar('groups', set(), set(range(len(self.groups))),
                  # At least 1, at most all groups
                  1, len(self.groups),
                  ess=True)
        self.svar('gnodes', set(), set(range(self.ngnodes)),
                  # At least size of smallest group, at most all
                  min([len(g.nodes) for g in self.groups]),
                  self.ngnodes)
        # covered snodes
        covered_snodes = {sn.index for sn in self.nodes if sn.gnodes}
        self.variables['snodes'] = DetVar('snodes', covered_snodes)
        # Category (abstract) nodes
        self.svar('catgnodes', set(), catnodes)
#        # Instance gnodes that are merged with catnodes
#        self.svar('merged_gnodes', set(), instnodes, 0, len(catnodes))
#        # Snodes that involve merger of gnodes (that have two associated gnodes)
#        self.svar('merged_snodes', set(), merged_snodes, 0, len(catnodes))
        # Position pairs
        pos_pairs = set()
        for group in self.groups:
            pos_pairs.update(group.pos_pairs())
        self.svar('gnode_pos', set(), pos_pairs)
        ## Create variables for SNodes, GInsts, and GNodes
        for snode in self.nodes:
            snode.create_variables()
        for ginst in self.groups:
            ginst.create_variables()
        for gnode in self.gnodes:
            gnode.create_variables()

    def create_constraints(self, verbosity=0):
        if verbosity:
            print("Creating constraints for {}".format(self))
        # Relation among abstract, concrete, and all gnodes for each snode
        for snode in self.nodes:
            if snode.gnodes:
                # Only do this for covered snodes
                self.constraints.extend(Union([snode.variables['gnodes'],
                                               snode.variables['cgnodes'],
                                               snode.variables['agnodes']]).constraints)
        # Constraints involved groups with category (abstract) nodes
        for group in self.groups:
            if group.nanodes > 0:
                # Only do this for groups with abstract nodes
                # For each group, the set of snodes is the union of the concrete and abstract nodes
                self.constraints.extend(Union([group.variables['gnodes_pos'],
                                               group.variables['agnodes_pos'],
                                               group.variables['cgnodes_pos']]).constraints)
                # For each group, the set of groups merged with it + itself is the union of the
                # set of groups merged with it and the set consisting of its index
#                self.constraints.extend(Union([group.variables['merged_groups_incl'],
#                                               group.variables['merged_groups_excl'],
#                                               DetVar('g{}'.format(group.index), {group.index})]).constraints)
                # The set of merged gnodes for the group is the union of the merged nodes for all
                # abstract gnodes in the group
#                self.constraints.append(UnionSelection(group.variables['merged_gnodes'],
#                                                       group.variables['agnodes'],
#                                                       [gn.variables['merge_cgn'] for gn in self.gnodes]))
                # The set of groups merged with the group is the union of groups associated with the
                # gnodes that are merged with the group's abstract nodes
#                self.constraints.append(UnionSelection(group.variables['merged_groups_excl'],
#                                                       group.variables['merged_gnodes'],
#                                                       [DetIVar("gn{}->g".format(gn.sent_index), gn.ginst.index) for gn in self.gnodes]))
                # The tree under this group consists of the union of the snodes associated with this group
                # and those merged with it
#                self.constraints.append(UnionSelection(group.variables['tree'],
#                                                       group.variables['merged_groups_incl'],
#                                                       [g.variables['gnodes_pos'] for g in self.groups]))
#                for gnode in group.nodes:
#                    if gnode.cat:
#                        # The gnodes that this abstract merges with must be in the set of selected gnodes
#                        self.constraints.extend(Inclusion([gnode.variables['merge_cgn'],
#                                                           self.variables['gnodes']]).constraints)
        # The set of category (abstract) nodes used is the union of the category nodes of the groups used
        self.constraints.append(UnionSelection(self.variables['catgnodes'],
                                               self.variables['groups'],
                                               [g.variables['agnodes'] for g in self.groups]))
        # The set of merged gnodes used is the union of the merged nodes of the selected category nodes
#        self.constraints.append(UnionSelection(self.variables['merged_gnodes'],
#                                               self.variables['catgnodes'],
#                                               [gn.variables['merge_cgn'] for gn in self.gnodes]))
        # The set of merged gnodes used is the union of the merged gnodes of all merging snodes
#        self.constraints.append(UnionSelection(self.variables['merged_gnodes'],
#                                               self.variables['merged_snodes'],
#                                               [sn.variables['mgnodes'] for sn in self.nodes]))
        # The set of category gnodes used is the union of the category nodes associated with all merged snodes
#        self.constraints.append(UnionSelection(self.variables['catgnodes'],
#                                               self.variables['merged_snodes'],
#                                               [sn.variables['agnodes'] for sn in self.nodes]))
        # The set of category gnodes used is the union of the category nodes associated with all merged gnodes
#        self.constraints.append(UnionSelection(self.variables['catgnodes'],
#                                               self.variables['merged_gnodes'],
#                                               [gn.variables['merge_agn'] for gn in self.gnodes]))
        # The set of merged snodes used is the union of the snodes associated with all category nodes used
#        self.constraints.append(UnionSelection(self.variables['merged_snodes'],
#                                               self.variables['catgnodes'],
#                                               [gn.variables['merge_cw'] for gn in self.gnodes]))
        # The set of merged snodes used is the union of the snodes associated with all merged gnodes
#        self.constraints.append(UnionSelection(self.variables['merged_snodes'],
#                                               self.variables['merged_gnodes'],
#                                               [gn.variables['merge_aw'] for gn in self.gnodes]))
        # The set of merged gnodes must be a subset of the set of used gnodes
#        self.constraints.extend(Inclusion([self.variables['merged_gnodes'],
#                                           self.variables['gnodes']]).constraints)
        # All snodes must have distinct category nodes
        self.constraints.extend(Disjoint([sn.variables['agnodes'] for sn in self.nodes]).constraints)
        # All snodes must have distinct concrete merged nodes nodes
#        self.constraints.extend(Disjoint([sn.variables['mgnodes'] for sn in self.nodes]).constraints)
        # All concrete gnodes must have distinct category nodes
#        self.constraints.extend(Disjoint([gn.variables['merge_agn'] for gn in self.gnodes]).constraints)
        # All position constraints for snodes
        self.constraints.append(PrecedenceSelection(self.variables['gnode_pos'],
                                                    [gn.variables['snodes'] for gn in self.gnodes]))
        # Position constraint pairs are the group position pairs for all groups used
        self.constraints.append(UnionSelection(self.variables['gnode_pos'],
                                               self.variables['groups'],
                                               [DetVar("g{}pos".format(g.index), g.pos_pairs()) for g in self.groups]))
        # Union selection on gnodes for each snode:
        #  the union of the snode indices associated with the gnodes of an snode is the snode's index
        gn2s = [gn.variables['snodes'] for gn in self.gnodes]
        s2gn = [s.variables['gnodes'] for s in self.nodes]
        for snode in self.nodes:
            if snode.gnodes:
                # Only for covered snodes
                self.constraints.append(UnionSelection(DetVar("sn{}".format(snode.index), {snode.index}),
                                                       snode.variables['gnodes'],
                                                       gn2s))
        # Union of all gnodes used for snodes is all gnodes used
        self.constraints.append(UnionSelection(self.variables['gnodes'],
                                               self.variables['snodes'],
                                               s2gn))
        # Union of all gnodes for groups used is all gnodes used
        self.constraints.append(UnionSelection(self.variables['gnodes'],
                                               self.variables['groups'],
                                               [g.variables['gnodes'] for g in self.groups]))
        # Union of all snodes for gnodes used is all snodes
        self.constraints.append(UnionSelection(self.variables['snodes'],
                                               self.variables['gnodes'],
                                               [gn.variables['snodes'] for gn in self.gnodes]))
        # Complex union selection by groups on positions of all concrete gnodes in each selected group
        self.constraints.append(ComplexUnionSelection(selvar=self.variables['groups'],
                                                      selvars=[g.variables['cgnodes_pos'] for g in self.groups],
                                                      seqvars=[s.variables['cgnodes'] for s in self.nodes],
                                                      mainvars=[g.variables['cgnodes'] for g in self.groups]))
        # Complex union selection by groups on positions of all category gnodes in each selected group
        self.constraints.append(ComplexUnionSelection(selvar=self.variables['groups'],
                                                      selvars=[g.variables['agnodes_pos'] for g in self.groups],
                                                      seqvars=[s.variables['agnodes'] for s in self.nodes],
                                                      mainvars=[g.variables['agnodes'] for g in self.groups]))
#        # Complex union selection by groups on positions of merged gnodes (concrete nodes that are merged with
#        # category nodes in this group) in each selected group
#        self.constraints.append(ComplexUnionSelection(selvar=self.variables['groups'],
#                                                      selvars=[g.variables['agnodes_pos'] for g in self.groups],
#                                                      seqvars=[s.variables['mgnodes'] for s in self.nodes],
#                                                      mainvars=[g.variables['merged_gnodes'] for g in self.groups]))
#        # Complex union selection by groups on positions of all gnodes in each selected group
#        self.constraints.append(ComplexUnionSelection(selvar=self.variables['groups'],
#                                                      selvars=[g.variables['gnodes_pos'] for g in self.groups],
#                                                      seqvars=[s.variables['gnodes'] for s in self.nodes],
#                                                      mainvars=[g.variables['gnodes'] for g in self.groups]))
#        # Set convexity (projectivity) within each group tree
#        self.constraints.append(ComplexSetConvexity(self.variables['groups'],
#                                                    [g.variables['tree'] for g in self.groups]))
        # Agreement
#        print("snode variables")
#        for sn in self.nodes:
#            print(' {} variables: {}'.format(sn, sn.variables))
        if any([g.variables.get('agr') for g in self.groups]):
            self.constraints.append(ComplexAgrSelection(selvar=self.variables['groups'],
                                                        seqvars=[gn.variables['snodes'] for gn in self.gnodes],
                                                        featvars=[sn.variables['features'] for sn in self.nodes],
                                                        selvars=[g.variables.get('agr', EMPTY) for g in self.groups]))

#    def run(self, verbosity=0):
#        """Run constraint satisfaction on constraints, for now without search if
#        no solution is found."""
#        self.solver.run(verbosity=verbosity)
#        if verbosity:
#            print("Solver status after run: {}".format(self.solver.status))
#        return self.solver.status

    @staticmethod
    def make_tree(group_dict, group_i, tree):
        """Make a tree (a set of snode indices) for the group with index group_i
        by searching for merged groups and their trees in group_dict."""
        if not group_dict[group_i][1]:
            return
        else:
            for mgi in group_dict[group_i][1]:
                tree.update(group_dict[mgi][0])
                Sentence.make_tree(group_dict, mgi, tree)

    def create_solution(self, dstore=None, verbosity=0):
        """Assuming essential variables are determined in a domain store, make a Solution object."""
        dstore = dstore or self.dstore
        # Get the indices of the selected groups
        groups = self.variables['groups'].get_value(dstore=dstore)
        ginsts = [self.groups[g] for g in groups]
        s2gnodes = []
        for node in self.nodes:
            gnodes = list(node.variables['gnodes'].get_value(dstore=dstore))
            s2gnodes.append(gnodes)
        # Create trees for each group
        tree_attribs = {}
        for snindex, sg in enumerate(s2gnodes):
            for gn in sg:
                gnode = self.gnodes[gn]
                gn_group = gnode.ginst.index
                if gn_group not in tree_attribs:
                    tree_attribs[gn_group] = [[], []]
                tree_attribs[gn_group][0].append(snindex)
            if len(sg) == 2:
                # Record group merger when an snode is associated with two gnodes
                gn0, gn1 = self.gnodes[sg[0]], self.gnodes[sg[1]]
                group0, group1 = gn0.ginst.index, gn1.ginst.index
                if gn0.cat:
                    # Group for gnode0 is merged with group for gnode1
                    tree_attribs[group0][1].append(group1)
                else:
                    tree_attribs[group1][1].append(group0)
#        print("Tree attribs {}".format(tree_attribs))
        for gindex, sn in tree_attribs.items():
            # First store the group's own tree as a set of sn indices
            sn.append(set(sn[0]))
            # Next check for mergers
            Sentence.make_tree(tree_attribs, gindex, sn[2])
#        print("Tree attribs {}".format(tree_attribs))
        # Convert the dict to a list and sort by group indices
        trees = list(tree_attribs.items())
        trees.sort(key=lambda x: x[0])
        # Just keep the snode indices in each tree
        trees = [x[1][2] for x in trees]
        # Get the indices of the GNodes for each SNode
        solution = Solution(self, ginsts, s2gnodes, len(self.solutions), trees=trees)
        self.solutions.append(solution)
        return solution

class SNode:
    """Sentence token and its associated analyses and variables."""

    def __init__(self, token, index, analyses, sentence):
        # Raw form in sentence (possibly result of segmentation)
        self.token = token
        # Position in sentence
        self.index = index
        # List of analyses
        if analyses and not isinstance(analyses, list):
            analyses = [analyses]
        self.analyses = analyses
        # Back pointer to sentence
        self.sentence = sentence
        # We'll need these for multiple matchings
        self.cats = self.get_cats()
        # Indices of candidate gnodes for this snode found during lexicalization
        self.gnodes = None
        # Dict of variables specific to this SNode
        self.variables = {}
        ## Tokens in target language for this SNode
        self.translations = []

    def __repr__(self):
        """Print name."""
        return "*{}:{}".format(self.token, self.index)

    ## Create IVars and (set) Vars with sentence DS as root DS

    def ivar(self, key, name, domain, ess=False):
        self.variables[key] = IVar(name, domain, rootDS=self.sentence.dstore,
                                   essential=ess)

    def svar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = Var(name, lower, upper, lower_card, upper_card,
                                  rootDS=self.sentence.dstore, essential=ess)

    def lvar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = LVar(name, lower, upper, lower_card, upper_card,
                                   rootDS=self.sentence.dstore, essential=ess)

    def create_variables(self, verbosity=0):
        if not self.gnodes:
            # Nothing matched this snode; all variables empty
            self.variables['gnodes'] = EMPTY
            self.variables['cgnodes'] = EMPTY
            self.variables['agnodes'] = EMPTY
#            self.variables['mgnodes'] = EMPTY
            self.variables['features'] = EMPTY
        else:
            # GNodes associated with this SNode: 0, 1, or 2
            self.svar('gnodes', "w{}->gn".format(self.index), set(),
                      set(range(self.sentence.ngnodes)),
                      0, 2, ess=True)
            # Concrete GNodes associated with this SNode: must be 1
            self.svar('cgnodes', "w{}->cgn".format(self.index), set(),
                      {gn.sent_index for gn in self.sentence.gnodes if not gn.cat},
                      1, 1)
            # Abstract GNodes associated with this SNode: 0 or 1
            self.svar('agnodes', "w{}->agn".format(self.index), set(),
                      {gn.sent_index for gn in self.sentence.gnodes if gn.cat},
                      0, 1)
            # Merged concrete GNodes associated with this SNode: 0 or 1
#            self.svar('mgnodes', "w{}->mgn".format(self.index), set(),
#                      {gn.sent_index for gn in self.sentence.gnodes if not gn.cat},
#                      0, 1)
            # Features
            features = self.get_features()
            if len(features) > 1:
                self.lvar('features', 'w{}f'.format(self.index),
                          [], features, 1, 1)
            else:
                # Only one choice so features are determined for this SNode
                self.variables['features'] = DetLVar('w{}f'.format(self.index), features)

    def get_cats(self):
        """The set of categories for the node's token, or None."""
        if not self.analyses:
            return None
        cats = set()
        for analysis in self.analyses:
            if 'cats' in analysis:
                cats.update(analysis['cats'])
        return cats

    def get_features(self):
        """The list of possible Features objects for the SNode."""
        features = []
        if self.analyses:
            for analysis in self.analyses:
                if 'features' in analysis:
                    features.append(analysis['features'])
                else:
                    features.append(Features({}))
        return features

    def match(self, item, features, verbosity=0):
        """Does this node match the group item (word, lexeme, category) and
        any features associated with it?"""
        if verbosity:
            print('   SNode {} with features {} trying to match item {} with features {}'.format(self, self.analyses, item, features))
        # If item is a category, don't bother looking at token
        if Entry.is_cat(item):
            if verbosity:
                print('    Cat item, looking in {}'.format(self.cats))
            if self.cats and item in self.cats:
#                print("   Token {} is in cat {}".format(self.token, item))
                if not self.analyses or not features:
                    # Match; failure would be False
                    return None
                else:
                    for analysis in self.analyses:
                        node_features = analysis.get('features')
                        if node_features:
                            u_features = node_features.unify(features)
                            if u_features != 'fail':
                                return analysis.get('root'), u_features
#                        print("   Matching group features {} and sentence features {}".format(features, node_features))
#                        if node_features and node_features.unify(features) != 'fail':
#                            return True
                    # None succeeded
                    return False
        elif self.token == item:
            # item matches this node's token; features are irrelevant
            return None
        elif self.analyses:
            # Check each combination of root and analysis features
            for analysis in self.analyses:
                root = analysis.get('root', '')
                node_features = analysis.get('features')
#                print("   SNode features {}".format(node_features))
                if root == item:
                    if not features:
                        return root, node_features
#                        return True
                    elif not node_features:
                        return root, features
#                        return True
                    else:
                        u_features = node_features.unify(features)
                        if u_features != 'fail':
                            return root, u_features
#                    elif node_features.unify(features) != 'fail':
#                        return True
        return False

class GInst:

    """Instantiation of a group; holds variables and GNode objects."""

    def __init__(self, group, sentence, head_index, snode_indices, index):
        # The Group object that this "instantiates"
        self.group = group
        self.sentence = sentence
        self.target = sentence.target
        # Index of group within the sentence
        self.index = index
        # Index of SNode associated with group head
        self.head_index = head_index
        # List of GNodes
        self.nodes = [GNode(self, index, indices) for index, indices in enumerate(snode_indices)]
        # Dict of variables specific to this group
        self.variables = {}
        # List of target language groups
        self.translations = []
        self.ngnodes = len(self.nodes)
        # Number of abstract nodes
        self.nanodes = len([n for n in self.nodes if n.cat])
        # Number of concrete nodes
        self.ncgnodes = self.ngnodes - self.nanodes

    def __repr__(self):
        return '<<{}:{}>>'.format(self.group.name, self.group.id)

    def display(self, word_width=10, s2gnodes=None):
        """Show group in terminal."""
        s = '<{}>'.format(self.index)
        n_index = 0
        n = self.nodes[n_index]
        ngnodes = len(self.nodes)
        for gn_indices in s2gnodes:
            if n.sent_index in gn_indices:
                i = '*{}*' if n.head else "{}"
                s += i.format(n.index).center(word_width)
                n_index += 1
                if n_index >= ngnodes:
                    break
                else:
                    n = self.nodes[n_index]
            else:
                s += ' '*word_width
        print(s)

    def pos_pairs(self):
        """Return position constraint pairs for gnodes in the group."""
        gnode_pos = [gn.sent_index for gn in self.nodes]
        return set(itertools.combinations(gnode_pos, 2))

    def gnode_sent_index(self, index):
        """Convert gnode index to gnode sentence index."""
        return self.nodes[index].sent_index

    def get_agr(self):
        """Return agr constraints for group, converted to tuples."""
        result = []
        if self.group.agr:
            for a in copy.deepcopy(self.group.agr):
                feats = [tuple(pair) for pair in a[2:]]
                a[2:] = feats
                # Convert gnode positions to sentence positions
                a[0] = self.gnode_sent_index(a[0])
                a[1] = self.gnode_sent_index(a[1])
                result.append(tuple(a))
        return set(result)

    ## Create IVars and (set) Vars with sentence DS as root DS

    def ivar(self, key, name, domain, ess=False):
        self.variables[key] = IVar(name, domain, rootDS=self.sentence.dstore,
                                   essential=ess)

    def svar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = Var(name, lower, upper, lower_card, upper_card,
                                  rootDS=self.sentence.dstore,
                                  essential=ess)

    def create_variables(self, verbosity=0):
        ngroups = len(self.sentence.groups)
        nsnodes = len(self.sentence.nodes)
        cand_snodes = self.sentence.covered_indices
#        print("Creating variables for {}, # abs nodes {}".format(self, self.nanodes))
        # GNode indices for this GInst (determined)
        self.variables['gnodes'] = DetVar('g{}->gnodes'.format(self.index), {gn.sent_index for gn in self.nodes})
        # Abstract GNode indices for GInst (determined)
        if self.nanodes:
            self.variables['agnodes'] = DetVar('g{}->agnodes'.format(self.index), {gn.sent_index for gn in self.nodes if gn.cat})
            # Concrete GNode indices for GInst (determined)
            self.variables['cgnodes'] = DetVar('g{}->cgnodes'.format(self.index), {gn.sent_index for gn in self.nodes if not gn.cat})
        else:
            self.variables['agnodes'] = EMPTY
            self.variables['cgnodes'] = self.variables['gnodes']
        # SNode positions of GNodes for this GInst
        self.svar('gnodes_pos', 'g{}->gnodes_pos'.format(self.index),
                  set(), set(cand_snodes), self.ngnodes, self.ngnodes)
        # , ess=True)
#                  set(), set(range(nsnodes)), self.ngnodes, self.ngnodes)
        # SNode positions of abstract GNodes for this GInst
        if self.nanodes == 0:
            # No abstract nodes
            self.variables['agnodes_pos'] = EMPTY
            # SNode positions of concrete GNodes for this GInst
            self.variables['cgnodes_pos'] = self.variables['gnodes_pos']
        else:
            # Position for each abstract node in the group
            self.svar('agnodes_pos', 'g{}->agnodes_pos'.format(self.index),
                      set(), set(cand_snodes), self.nanodes, self.nanodes)
#                      set(), set(range(nsnodes)), self.nanodes, self.nanodes)
            # Position for each concrete node in the group
            self.svar('cgnodes_pos', 'g{}->cgnodes_pos'.format(self.index),
                      set(), set(cand_snodes), self.ncgnodes, self.ncgnodes)
#                      set(), set(range(nsnodes)), self.ncgnodes, self.ncgnodes)
        # Other GInsts merged with this one, excluding and including itself
#        if self.nanodes == 0:
#            # No abstract nodes, so this is a determined variable with one value (its own index)
#            self.variables['merged_groups_incl'] = DetVar('g{}->mgroups_in'.format(self.index), {self.index})
#            self.variables['merged_groups_excl'] = EMPTY
#            self.variables['merged_gnodes'] = EMPTY
#        else:
#            self.svar('merged_groups_incl', 'g{}->mgroups_in'.format(self.index),
#                      {self.index}, set(range(ngroups)), 1, self.nanodes+1)
#            self.svar('merged_groups_excl', 'g{}->mgroups_ex'.format(self.index),
#                      set(), set(range(ngroups)) - {self.index}, 0, self.nanodes)
            # Set of all gnodes that are merged with abstract gnodes in this group
            # upper bound is all gnodes not in this group
#            self.svar('merged_gnodes', 'g{}->mgnodes'.format(self.index),
#                      set(), set(range(len(self.sentence.gnodes))) - {gn.sent_index for gn in self.nodes})
        # Trees under GInst head (including self)
#        if self.nanodes == 0:
#            # No abstract gnodes, so same as gnodes
#            v = self.variables['gnodes_pos']
#            self.variables['tree'] = v
#            # Make this an essential variable
#            v.essential=True
#            self.sentence.dstore.ess_undet.append(v)
#        else:
#            self.svar('tree', 'g{}->tree'.format(self.index),
#                      # at least as long as the number of self's nodes
#                      set(), set(cand_snodes), self.ngnodes, len(cand_snodes))
##, ess=True)
##                      set(), set(range(nsnodes)), self.ngnodes, nsnodes, ess=True)
        # Determined variable for within-source agreement constraints, gen: 0}
        agr = self.get_agr()
        if agr:
            self.variables['agr'] = DetVar('g{}agr'.format(self.index), agr)
        
    def set_translations(self, verbosity=0):
        """Find the translations of the group in the target language."""
        translations = self.group.get_translations(self.target.abbrev, False)
        # If alignments are missing, add default alignment
        for i, t in enumerate(translations):
            if len(t) == 1:
                translations[i] = [t[0], {'align': list(range(len(self.nodes)))}]
#        print("Translations for {}: {}".format(self, translations))
        ntokens = len(self.group.tokens)
        for tgroup, s2t_dict in translations:
#            print("TGroup {}', s2t_dict {}".format(tgroup, s2t_dict))
            # If there's no explicit alignment, it's the obvious default
            alignment = s2t_dict.get('align', list(range(ntokens)))
            if isinstance(tgroup, str):
                # First find the target Group object
                tgroup = self.target.groupnames[tgroup]
            # Make any TNodes required
            nttokens = len(tgroup.tokens)
            tnodes = []
            if nttokens > ntokens:
                # Target group has more nodes than source group.
                # Indices of groups that are not empty.
                full_t_indices = set(alignment)
                empty_t_indices = set(range(nttokens)) - full_t_indices
                for i in empty_t_indices:
                    empty_t_token = tgroup.tokens[i]
                    empty_t_feats = tgroup.features[i] if tgroup.features else None
                    tnodes.append(TNode(empty_t_token, empty_t_feats, self, i))
            # Deal with individual gnodes in the group
            gnodes = []
            for gn_index, gnode in enumerate(self.nodes):
                # Align gnodes with target tokens and features
                tokens = tgroup.tokens
                features = tgroup.features
                targ_index = alignment[gn_index]
                if targ_index < 0:
                    # This means there's no target language token
                    continue
                agrs = s2t_dict['agr'][gn_index] if 'agr' in s2t_dict else None
                token = tokens[targ_index]
                feats = features[targ_index] if features else None
                gnodes.append((gnode, token, feats, agrs, targ_index))
            self.translations.append((tgroup, gnodes, tnodes, self))

class GNode:

    """Representation of a single node (word, position) within a GInst object."""

    def __init__(self, ginst, index, snodes):
        self.ginst = ginst
        self.index = index
        self.sentence = ginst.sentence
        self.snode_indices = [s[0] for s in snodes]
        self.snode_anal = [s[1] for s in snodes]
        # Whether this is the head of the group
        self.head = index == ginst.group.head_index
        # Group word, etc. associated with this node
        self.token = ginst.group.tokens[index]
        # Whether the associated token is abstract (a category)
        self.cat = Entry.is_cat(self.token)
        # Features associated with this group node
        groupfeats = ginst.group.features
        if groupfeats:
            self.features = groupfeats[index]
        else:
            self.features = None
        self.variables = {}
        # List of target-language token and features associated with this gnode
#        self.translations = []

    def __repr__(self):
        return "{}|{}".format(self.ginst, self.token)

    ## Create IVars and (set) Vars with sentence DS as root DS

    def ivar(self, key, name, domain, ess=False):
        self.variables[key] = IVar(name, domain, rootDS=self.sentence.dstore,
                                   essential=ess)

    def svar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = Var(name, lower, upper, lower_card, upper_card,
                                  rootDS=self.sentence.dstore,
                                  essential=ess)

    def create_variables(self, verbosity=0):
        nsnodes = len(self.sentence.nodes)
        # SNode index for this GNode
        self.ivar('snodes', "gn{}->w".format(self.sent_index), set(self.snode_indices))
#        if self.cat:
#            # Concrete nodes merged with this abstract node
#            self.svar('merge_cgn', 'gn{}_cgmerge'.format(self.sent_index),
#                      set(), {gn.sent_index for gn in self.sentence.gnodes if not gn.cat},
#                      0, 1)
#            self.svar('merge_cw', 'gn{}_cwmerge'.format(self.sent_index),
#                      set(), set(range(nsnodes)),
#                      0, 1)
#            self.variables['merge_agn'] = EMPTY
#            self.variables['merge_aw'] = EMPTY
#        else:
#            # Abstract nodes merged with this concrete node
#            self.svar('merge_agn', 'gn{}_agmerge'.format(self.sent_index),
#                      # indices of all abstract nodes
#                      set(), {gn.sent_index for gn in self.sentence.gnodes if gn.cat},
#                      0, 1)
#            self.svar('merge_aw', 'gn{}_awmerge'.format(self.sent_index),
#                      set(), set(range(nsnodes)),
#                      0, 1)
#            self.variables['merge_cgn'] = EMPTY
#            self.variables['merge_cw'] = EMPTY

class TNode:

    """Representation of a node within a target language group that doesn't
    have a corresponding node in the source language group that it's the
    translation of."""

    def __init__(self, token, features, ginst, index):
        self.token = token
        self.features = features
        self.ginst = ginst
        self.sentence = ginst.sentence
        self.index = index

    def generate(self, verbosity=0):
        """Generate forms for the TNode."""
        print("Generating form for target token {} and features {}".format(self.token, self.features))
        if Entry.is_lexeme(self.token):
#        if self.features:
            return self.sentence.target.generate(self.token, self.features)
        else:
            return [self.token]

    def __repr__(self):
        return "~{}|{}".format(self.ginst, self.token)

class Solution:
    
    """A non-conflicting set of groups for a sentence, at most one instance
    GNode for each sentence token, exactly one sentence token for each obligatory
    GNode in a selected group. Created when a complete variable assignment.get('features'))
    is found for a sentence."""

    def __init__(self, sentence, ginsts, s2gnodes, index, trees=None):
        self.sentence = sentence
        # List of sets of gnode indices
        self.s2gnodes = s2gnodes
        self.ginsts = ginsts
        self.trees = trees
        self.index = index
        # A list of pairs for each snode: (gnodes, features)
        self.snodes = []
        # List of Translation objects; multiple translations are possible
        # for a given solution because of multiple translations for groups
        self.translations = []

    def __repr__(self):
        return "|< {} >|({})".format(self.sentence.raw, self.index)

    def display(self, word_width=10):
        """Show solution groups (GInsts) in terminal."""
        for g in self.ginsts:
            g.display(word_width=word_width, s2gnodes=self.s2gnodes)

    def translate(self, verbosity=0, all_sols=False):
        """Do everything you need to create the translation."""
        self.merge_nodes(verbosity=verbosity)
        for ginst in self.ginsts:
            ginst.set_translations(verbosity=verbosity)
        self.make_translations(verbosity=verbosity, all_sols=all_sols)

    def make_translations(self, verbosity=0, display=True, all_sols=False):
        """Combine GInsts for each translation in translation products, and
        separate gnodes into a dict for each translation."""
        if verbosity:
            print("Making translations for {}".format(self))
        translations = itertools.product(*[g.translations for g in self.ginsts])
        for index, translation in enumerate(translations):
            t = Translation(self, translation, index, trees=copy.deepcopy(self.trees), verbosity=verbosity)
            t.initialize(verbosity=verbosity)
            t.realize(verbosity=verbosity, display=display, all_sols=all_sols)
#            if display:
#                t.display_all()
            self.translations.append(t)
            if all_sols:
                continue
            if not input('SEARCH FOR ANOTHER TRANSLATION FOR THIS ANALYSIS? [yes/NO] '):
                return
        if verbosity:
            print("No more translations for analysis")

    def merge_nodes(self, verbosity=0):
        """Merge the source features of cat and inst GNodes associated with each SNode."""
        if verbosity:
            print("Merging target nodes for {}".format(self))
        for snode, gn_indices in zip(self.sentence.nodes, self.s2gnodes):
            # gn_indices is either one or two ints indexing gnodes in self.gnodes
            gnodes = [self.sentence.gnodes[index] for index in gn_indices]
            features = []
            for gnode in gnodes:
#                print("gnode {}, snode_anal {}".format(gnode, gnode.snode_anal))
                snode_indices = gnode.snode_indices
                snode_index = snode_indices.index(snode.index)
                snode_anal = gnode.snode_anal[snode_index]
                if snode_anal:
#                    print("snode_anal {}".format(snode_anal))
                    features.append(snode_anal[1])
            # Could this fail??
            features = Features.unify_all(features)
            self.snodes.append((gnodes, features))

class Translation:
    """Representation of a single translation for an input sentence (with
    multiple possible orders and morphological realizations of individual
    words). Multiple translations are possible with a single Solution."""

    def __init__(self, solution, attribs, index, trees=None, verbosity=0):
        self.solution = solution
        self.index = index
        self.sentence = solution.sentence
        self.verbosity = verbosity
        # Create GNode dict and list of target group, gnodes and tnodes
        # from attributes
        self.gnode_dict = {}
        self.group_attribs = []
        for tgroup, tgnodes, tnodes, ginst in attribs:
#            print('tgroup {}, tgnodes {}, tnodes {}, ginst {}'.format(tgroup, tgnodes, tnodes, ginst))
            for tgnode, tokens, feats, agrs, t_index in tgnodes:
                self.gnode_dict[tgnode] = (tgroup, tokens, feats, agrs, t_index)
            self.group_attribs.append((tgroup, tnodes, ginst, tgroup.agr))
        # form list / order constraint pairs for each sentence position
        self.nodes = []
        # Ordered units: merged groups or uncovered words
        self.chunks = []
        # Merged group indices
        self.mergers = []
        # pairs of node indices representing order constraints
        self.order_pairs = []
        # Source-sentence indices for tgroup trees
        self.trees = trees
        # Root domain store for variables
        self.dstore = DStore(name="T{}".format(self.index))
        # Order variables for each node, tree variables for groups
        self.variables = {}
        # Order and disjunction constraints
        self.constraints = []
        # Translation needs a solver to figure out positions of words
        self.solver = Solver(self.constraints, self.dstore,
                             description='target realization',
                             verbosity=verbosity)
        # These are produced in self.build()
        self.node_features = None
        self.group_nodes = None
        self.agreements = None
        # Final outputs; different ones have alternate word orders
        self.outputs = []

    def __repr__(self):
        return "{}[{}] ->".format(self.solution, self.index)

    def display(self, index):
        print("{}  {}".format(self, self.out_string(index)))

    def display_all(self):
        for index in range(len(self.outputs)):
            self.display(index)

    def out_string(self, index):
        '''Convert output to a string for pretty printing.'''
        l = []
        for word_list in self.outputs[index]:
            if len(word_list) == 1:
                l.append(word_list[0])
            else:
                l.append('|'.join(word_list))
        return ' '.join(l)

    def initialize(self, verbosity=0):
        """Set up everything needed to run the constraints and generate the translation."""
        if verbosity:
            print("Initializing translation {}".format(self))
        self.build(verbosity=verbosity)
        self.generate_words(verbosity=verbosity)
        self.set_chunks(verbosity=verbosity)
        self.make_order_pairs(verbosity=verbosity)
        self.create_variables(verbosity=verbosity)
        self.create_constraints(verbosity=verbosity)

    def build(self, verbosity=0):
        """Unify translation features for merged nodes, map agr features from source to target,
        generate surface target forms from resulting roots and features."""
        if verbosity:
            print('Building {}'.format(self))
        tginsts, tgnodes, trans_index = self.group_attribs, self.gnode_dict, self.index
#        print("Tginsts {}, tgnodes {}, trans_index {}".format(tginsts, tgnodes, trans_index))
        # Figure out the target forms for each snode
#        print('tgnodes {}'.format(tgnodes))
        # Dictionary mapping source node indices to initial target node indices
        tnode_index = 0
        node_index_map = {}
        node_features = []
        agreements = {}
        group_nodes = {}
        for snode, (gnodes, features) in zip(self.sentence.nodes, self.solution.snodes):
#            print(" Snode {}, gnodes {}, features {}, tnode_index {}".format(snode, gnodes, features, tnode_index))
            if not gnodes:
                # snode is not covered by any group
                node_index_map[snode.index] = tnode_index
                node_features.append((snode.token, None, []))
                tnode_index += 1
            else:
                t_indices = []
                if len(gnodes) > 1:
                    # There are two gnodes for this snode; only the concrete node
                    # can have translations
                    # Check with there is no translation for one or the other; if so, skip this snode
                    if gnodes[0] not in tgnodes or gnodes[1] not in tgnodes:
#                        print("No translation for {}".format(snode))
                        continue
                    gn0, gn1 = tgnodes[gnodes[0]], tgnodes[gnodes[1]]
#                    print(" gn0 {}, gn1 {}".format(gn0, gn1))
                    tgroups, tokens, targ_feats, agrs, t_index = zip(gn0, gn1)
                    token = False
                    i = 0
                    # Find the token that's not a cat
                    while not token:
                        t = tokens[i]
                        if not Entry.is_cat(t):
                            token = t
                        i += 1
                    targ_feats = Features.unify_all(targ_feats)
                    # Merge the agreements
                    agrs = Translation.combine_agrs(agrs)
                    t_indices.append((tgroups[0], gn0[-1]))
                    t_indices.append((tgroups[1], gn1[-1]))
                    ## Record this node and its groups in mergers
                    tg = list(zip(tgroups, gnodes))
                    # Sort the groups by which is the "outer" group in the merger
                    tg.sort(key=lambda x: x[1].cat)
                    tg = [x[0] for x in tg]
                    self.mergers.append([snode.index, tg])
#                    print(' tgroups {}, token {}, t_indices {}'.format(tgroups, token, t_indices))
                else:
                    gnode = gnodes[0]
                    if gnode not in tgnodes:
#                        print(' snode {} / gnode {} has no translation'.format(snode, gnode))
                        continue
                    else:
                        gnode = gnodes[0]
                        tgroup, token, targ_feats, agrs, t_index = tgnodes[gnode]
                        if len(tgroup.tokens) > 1:
                            t_indices.append((tgroup, t_index))
#                    print(' tgroup {}, token {}, t_index {}'.format(tgroup, token, t_index))
                            
                # Make target and source features agree as required
                if not targ_feats:
                    targ_feats = Features({})
                if agrs:
#                    print("Feature agree, targ feats {}, agrs {}".format(targ_feats, agrs))
                    features.agree(targ_feats, agrs)
                node_index_map[snode.index] = tnode_index
                tnode_index += 1
                node_features.append((token, targ_feats, t_indices))
                for t_index in t_indices:
                    group_nodes[t_index] = (token, targ_feats)
#        print("S->T index mapping {}".format(node_index_map))
#        print('Trees {}'.format(self.trees))
        # Fix indices in tgroup trees
        trees = []
        for t in self.trees:
            tree = []
            for src_index in t:
                if src_index in node_index_map:
                    tree.append(node_index_map[src_index])
            trees.append(tree)
        self.trees = trees
#        print('Mapped tree indices {}'.format(self.trees))
        # Add TNode elements
        tgnode_elements = []
        for ginst_i, (tginst, tnodes, ginst, agr) in enumerate(tginsts):
            if agr:
                agreements[tginst] = agr
            if tnodes:
                for tnode in tnodes:
                    features = tnode.features or Features({})
                    src_index = len(node_features)
#                    print('TG {}, tnode {}, sindex {}, ginst {}'.format(tginst, tnode, src_index, ginst))
                    self.trees[ginst_i].append(src_index)
                    index = [(tginst, tnode.index)]
                    node_features.append((tnode.token, features, index))
                    group_nodes[index[0]] = (tnode.token, features)
#        if agreements:
#            print("Agreements {}".format(agreements))
#        print("Node features: {}".format(node_features))
        self.node_features = node_features
        self.group_nodes = group_nodes
        self.agreements = agreements

    def generate_words(self, verbosity=0):
        """Do inter-group agreement constraints, and generate wordforms for each target node."""
        for group, agr_constraints in self.agreements.items():
            for agr_constraint in agr_constraints:
                i1, i2 = agr_constraint[0], agr_constraint[1]
                feature_pairs = agr_constraint[2:]
                # Find the sentence nodes for the agreeing group nodes in the group_nodes dict
                agr_node1 = self.group_nodes[(group, i1)]
                agr_node2 = self.group_nodes[(group, i2)]
#                print("Found node1 {} and node2 {} for constraint {}".format(agr_node1, agr_node2, feature_pairs))
                agr_feats1, agr_feats2 = agr_node1[1], agr_node2[1]
                agr_feats1.mutual_agree(agr_feats2, feature_pairs)
        generator = self.sentence.target.generate
        for token, features, index in self.node_features:
#            print("Token {}, features {}".format(token, features))
            output = generator(token, features)
            self.nodes.append((output, index))
            if verbosity:
                print("Generating target node {}: {}".format(index, output))

    def set_chunks(self, verbosity=0):
        """Find output chunks: a list of sets of snode indices."""
        chunk_attribs = []
        for index, (tokens, constraints) in enumerate(self.nodes):
            # Is this an uncovered node/token
            if not constraints:
                chunk_attribs.append((tokens[0], {index}))
            else:
                # Groups that the node belongs to
                for g in [c[0] for c in constraints]:
                    # Find previous chunk list if it exists
                    found = False
                    for c, i in chunk_attribs:
                        if c == g:
                            i.add(index)
                            found = True
                            break
                    if not found:
                        chunk_attribs.append((g, {index}))
        # Merge chunks that share nodes
        for index, (label, indices) in enumerate(chunk_attribs):
            if self.chunks and indices.intersection(self.chunks[-1]):
                # merged this chunk with the last
                self.chunks[-1].update(indices)
            else:
                self.chunks.append(indices)

    @staticmethod
    def combine_agrs(agr_list):
        """Merge agr dicts in agr_list into a single agr dict."""
        result = {}
        for agr in agr_list:
            if not agr:
                continue
            for k, v in agr.items():
                if k in result:
                    if result[k] != v:
                        print("Warning: agrs in {} failed to merge".format(agr_list))
                        return 'fail'
                    else:
                        continue
                else:
                    result[k] = v
        return result

    def make_order_pairs(self, verbosity=0):
        """Convert group/index pairs to integer (index) order pairs.
        Constrain chunks to appear in source-language order.
        Constrain order in merged groups."""
        tgroup_dict = {}
        for index, (forms, constraints) in enumerate(self.nodes):
#            print('  index {}, forms {}, constraints {}'.format(index, forms, constraints))
            for tgroup, tg_index in constraints:
                if tgroup not in tgroup_dict:
                    tgroup_dict[tgroup] = []
                tgroup_dict[tgroup].append((index, tg_index))
#        print('tgroup dict {}'.format(tgroup_dict))
        for pairs in tgroup_dict.values():
#            print(' pairs {}'.format(pairs))
            for pairpair in itertools.combinations(pairs, 2):
                pairpair = list(pairpair)
#                print('  pairpair {}'.format(pairpair))
                # Sort by the target index
                pairpair.sort(key=lambda x: x[1])
                self.order_pairs.append([x[0] for x in pairpair])
        # Chunks
        for ci, indices in enumerate(self.chunks[:-1]):
            next_indices = self.chunks[ci+1]
            for index in indices:
                for next_index in next_indices:
                    self.order_pairs.append([index, next_index])
        # Order nodes within merged groups
        for node, (inner, outer) in self.mergers:
            # Indices (input, tgroup) in inner and outer groups
            inner_nodes = tgroup_dict[inner]
            outer_nodes = tgroup_dict[outer]
            # Get the tgroup index for the merge node
#            print("node {}, inner nodes {}, outer nodes {}".format(node, inner_nodes, outer_nodes))
            merge_tg_i = dict(outer_nodes)[node]
#            print("pos of merge node in outer group: {}".format(merge_tg_i))
            # Get input indices for outer groups units before and after the merged node
            prec_outer = [n for n, i in outer_nodes if i < merge_tg_i]
            foll_outer = [n for n, i in outer_nodes if i > merge_tg_i]
#            print("outer nodes before {} / after {} merger node".format(prec_outer, foll_outer))
            if prec_outer or foll_outer:
                # Get input indices for inner group nodes other than the merge node
                other_inner = [n for n, i in inner_nodes if n != node]
#                print('inner nodes other than merge node: {}'.format(other_inner))
                # Each outer group node before the merge node must precede all inner group nodes,
                # and each outer group node after the merge node must follow all inner group nodes.
                # Add order pair constraints (using input indices) for these constraints.
                for o in prec_outer:
                    for i in other_inner:
                        self.order_pairs.append([o, i])
                for o in foll_outer:
                    for i in other_inner:
                        self.order_pairs.append([i, o])
#        print('Order pairs: {}'.format(self.order_pairs))

    def svar(self, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=True):
        return Var(name, lower, upper, lower_card, upper_card,
                   essential=ess, rootDS=self.dstore)

    def create_variables(self, verbosity=0):
        """Create an IVar for each translation node and variables for each group tree."""
        nnodes = len(self.nodes)
        self.variables['order_pairs'] = DetVar("order_pairs", set([tuple(positions) for positions in self.order_pairs]))
        self.variables['order'] = [IVar("o{}".format(i), set(range(nnodes)), rootDS=self.dstore, essential=True) for i in range(nnodes)]
        # target-language trees
        self.variables['tree_sindices'] = []
        self.variables['trees'] = []
        for i, t in enumerate(self.trees):
#            print('Tree {}: {}'.format(i, t))
            if len(t) > 1:
                # Only make a variable if the tree has more than one node.
                self.variables['tree_sindices'].append(DetVar("tree{}_sindices".format(i), set(t)))
                self.variables['trees'].append(self.svar("tree{}".format(i), set(), set(range(nnodes)), len(t), len(t), ess=False))

    def create_constraints(self, verbosity=0):
        """Make order and disjunction constraints."""
        if verbosity:
            print("Creating constraints for {}".format(self))
        ## Order constraints
        order_vars = self.variables['order']
#        for first, second in self.order_pairs:
#            self.constraints.append(SetPrecedence([order_vars[first], order_vars[second]]))
#        print("Order pairs {}".format(self.variables['order_pairs']))
        self.constraints.append(PrecedenceSelection(self.variables['order_pairs'],
                                                    order_vars))
        self.constraints.append(Order(order_vars))
#        self.constraints.extend(Disjoint(order_vars).constraints)
        ## Tree constraints
        for i_var, tree in zip(self.variables['tree_sindices'], self.variables['trees']):
            self.constraints.append(UnionSelection(tree, i_var, order_vars))
#            i_var.pprint()
#            tree.pprint()
#            print("Tree union {}".format(self.constraints[-1]))
            # Convexity (projectivity)
            self.constraints.append(SetConvexity(tree))
#        for c in self.constraints:
#            print(c)

    def realize(self, verbosity=0, display=True, all_sols=False):
        """Run constraint satisfaction on the order and disjunction constraints,
        and convert variable values to sentence positions."""
        generator = self.solver.generator(test_verbosity=verbosity,
                                          expand_verbosity=verbosity)
        try:
            proceed = True
            while proceed:
                succeeding_state = next(generator)
                order_vars = self.variables['order']
                positions = [list(v.get_value(dstore=succeeding_state.dstore))[0] for v in order_vars]
                node_pos = list(zip([n[0] for n in self.nodes], positions))
                node_pos.sort(key=lambda x: x[1])
                self.outputs.append([n[0] for n in node_pos])
                if display:
                    self.display(len(self.outputs)-1)
                if verbosity:
                    print('FOUND REALIZATION {}'.format(self.outputs[-1]))
                if all_sols:
                    continue
                if not input('SEARCH FOR ANOTHER REALIZATION FOR TRANSLATION? [yes/NO] '):
                    proceed = False
        except StopIteration:
            if verbosity:
                print('No more realizations for translation')
