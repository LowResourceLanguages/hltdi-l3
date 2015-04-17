#   Implementation of Extensible Dependency Grammar, as described in
#   Debusmann, R. (2007). Extensible Dependency Grammar: A modular
#   grammar formalism based on multigraph description. PhD Dissertation:
#   Universität des Saarlandes.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010, 2011, 2012, 2013, 2014
#   by the HLTDI L^3 Team <gasser@cs.indiana.edu>
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
# 2010.08.21 (MG)
# -- Node in a separate module.
# -- Node has a dict of dimensions with dimension-specific variables.
# -- Almost all variable creation now handled by principles.
# 2010.09.13 (MG)
# -- initialize now includes inheritance.
# 2010.10.17 (MG)
# -- initialize now adds entries resulting from morphological analysis.
# 2010.10.18 (MG)
# -- Node constructor takes both the original word and possibly preprocessed
#    word (form). form is used for lexicalization.
# 2011.02.10
# -- EmptyNode, subclass of Node, created.
# 2011.04.10
# -- Empty nodes keep track of the index of their "source" (mother) node. Needed
#    for EmptyNode Principle.
# 2011.05.13
# -- New subclass of EmptyNode for the more complicated general language node mismatch
#    case, for examples, prepositions in Qu->Es.
# 2011.12.04
# -- Reverse ComplexEmptyNodes
# 2012.09.11
# -- Lexical entry indices may be constrained during initialization, using problem's (xdg)
#    lex_indices.
# 2013.10.29
# -- "Unknown" node; its 'name' is '*', that is, no lexical entry was found.
# 2014.02.04
# -- Nodes know how to use entries that are already morphologically analyzed and/or
#    have their crosslingual features already spelled out.

from .variable import *
from .utils import PARSE, GENERATE, TRANSLATE

class Node:

    def __init__(self, word, form, lexicon, problem, dstore, dims=None, agree=None,
                 index=0, process=0, analyses=None, lex=None, arcs=None, eos=False,
                 empty=False, verbosity=0):
        """
        form is the possibly preprocessed form of word. This is used for lexicalization
        during parsing.
        lex and arcs are non-None for generation.
        """
        self.word = word
        self.form = form
        self.lexicon = lexicon
        self.language = lexicon.language
        self.problem = problem
        # Whether this is an end-of-sentence node
        self.eos = eos
        ## parse, generate, or translate
        self.process = process or problem.process
        # target language abbreviations
#        self.languages = [language.abbrev for language in problem.languages]
        self.languages = problem.languages
        self.target_languages = self.languages
        # add semantics
        if problem.semantics:
            self.languages = [problem.semantics] + self.languages
        # Lexicons to use in inheritance
        # Whether to use transfer xlexes in inheritance
        self.transfer_xlex = problem.transfer_xlex
        # Possibly one or more wordforms for each language
        self.forms = {}
        # If translation languages have morphological analysis
        self.roots = {}
        self.dstore = dstore
        # Position
        self.index = index
        # For translation, nodes have different positions in different languages,
        # represented by variables that are created by OrderPrinciple
        self.positions = {}
        ## Generation
        # A tuple of lexicon key (word, lexeme, gram) and entry index
        self.lex = lex
        # dict of {dim: {'out': [(label, dest)], 'in': [(label, source)]}}
        self.arcs = arcs
        # Actual positions in multiple languages
        self.positions = {}
        self.analyses = analyses
        self.entries = []
        self.dims = dict((d, {}) for d in dims) if dims else {}
        # Agreement dimensions
        self.agree = agree
        ## Lexical entry
        # Create a variable for this
        self.lexvar = None
        # Variables for group IDs (set in GroupP)
        self.groupvars = {}
        # Empty nodes that are possible daughters of this node.
        # dict keeps track of the node and entry indices for each empty node entry:
        # {empty_entry: [empty_node, mother_entry_index1, ...]}
        if not empty:
            self.empty_nodes = {}
            self.empty = False
        else:
            self.empty = True
        # Determined SVar with this node's index as its value; called 'eq' by Debusmann
        self.dsvar = DetSVar('{}='.format(self.index), {self.index})
        self.initialize(dims, verbosity=verbosity)

    def __repr__(self):
        return '&{}{}'.format(self.index, self.word)

    def initialize(self, dimensions, verbosity=1):
        """Find lexical entries and create all variables."""
        lex_indices = self.problem.lex_indices[self.index]
        if lex_indices is None:
            lex_indices = set()
        elif not isinstance(lex_indices, set):
            lex_indices = {lex_indices}
        entries = self.lexicon.lexicalize(self.form, clone=True, indices=lex_indices, any_other=self.analyses,
                                          verbosity=verbosity)
#        print('{}/{} entries following lexicalization: {}'.format(self, self.form, entries))
        if self.analyses:
#            print('Morphological analyses for {}: {}'.format(self, self.analyses))
            if verbosity:
                print("Incorporating morphological analysis for", self)
            entries.extend(self.lexicon.incorp_analyses(self.analyses, self.agree,
                                                        word=self.form, problem=self.problem))
#        entries.extend(self.lexicon.lexicalize(self.form, clone=True, indices=lex_indices))

        print('Entries before crossling inh: {}'.format(entries))

        # For each entry, inherit properties from lexical classes.
        # For flattened lexicons, the only inheritance that happens is across languages.
        if self.languages or self.lexicon.hierarchical:
            unknown = None
            lang_abbrevs = [l.abbrev for l in self.target_languages]
            to_incorp = []
            for entry in entries:
                if entry.is_inherited(lang_abbrevs):
                    print('Entry {} is cross-inherited for {}'.format(entry, lang_abbrevs))
                    self.entries.append(entry)
                    continue
                # Any additional entries found from classes during inheritance
                add_entries = []
                # Accumulate entries to add
                self.lexicon.inherit(entry, [d.abbrev for d in dimensions],
                                     add_entries=add_entries, node=self,
                                     languages=self.languages,
                                     target_languages=self.target_languages,
                                     process=self.process,
                                     transfer_xlex=self.transfer_xlex,
                                     verbosity=verbosity)
                if add_entries:
#                    print('{} add entries {}, languages {}'.format(self, add_entries, lang_abbrevs))
                    for e in add_entries:
                        if any([e.is_unknown(l) for l in lang_abbrevs]):
#                            print('{} is unknown'.format(e))
                            unknown = e
                        else:
                            to_incorp.append(e)
#                            print('Add {} to entries'.format(e))
                            self.entries.append(e)
            # If there are no other entries, use the (last) unknown one
            if not self.entries and unknown:
#                print('No entries for {}, adding unknown'.format(self))
                self.entries = [unknown]
#                    # Add any new entries found to the node
#                    self.entries.extend(add_entries)
            
            # This is where new cross-lingual entries get created and stored.
            if self.languages and to_incorp:
                self.lexicon.incorp_cross_inh(self.word, to_incorp)

            # Set probabilities on the basis of lex xcounts
            if len(self.entries) > 1:
                if verbosity:
                    print("Setting probabilities for {} entries".format(len(self.entries)))
                total = sum([e.xcount for e in self.entries])
                for e in self.entries:
                    e.prob = e.xcount / total

        else:
            self.entries = entries
            # Set entry probabilities on the basis of lex counts
            if len(entries) > 1:
                if verbosity:
                    print("Setting probabilities for {} entries".format(len(entries)))
                # Set probabilities for different analyses
                total = sum([e.count for e in entries])
                for e in entries:
                    e.prob = e.count / total

#        for e in self.entries:
#            if e.crosslexes:
#                print('Removing crosslexes from {}'.format(e))
#                e.crosslexes = {}

        # Assign entry scores
        self.scores = [0 for e in self.entries]

        if not self.entries:
            print('NO ENTRIES FOR {}!'.format(self))

    def finalize(self, verbosity=1):
        """Set lexical variable and normalize probabilities."""
        ## Variable for node's entries
        lexvar_name = '{}{}'.format(self.index, self.word)
        if len(self.entries) == 1:
            # Determine the variable now if there's no ambiguity
            self.lexvar = DetIVar(lexvar_name, 0)
        else:
            # Normalize the probabilities
            prob_total = sum([e.prob for e in self.entries])
            for e in self.entries:
                e.prob /= prob_total
            for e in self.entries:
                if verbosity:
                    print(' {} prob: {}'.format(e, e.prob))
#            total = sum([e.count for e in self.entries])
#            for e in self.entries:
#                e.prob *= e.count / total
#                print(' {}: count {}, prob {}'.format(e, e.count, e.prob))
            self.lexvar = IVar(lexvar_name,
                               range(len(self.entries)),
                               problem=self.problem, rootDS=self.dstore)

    def rank(self, verbosity=0):
        """Rank and sort entries by score, eliminating those with negative scores."""
        entries_scores = list(zip(self.entries, self.scores))
        entries_scores.sort(key=lambda e_s: e_s[1], reverse=True)
#        for e, s in entries_scores:
#            if s < 0:
#                print('Entry {} eliminated'.format(e))
        self.entries = [e for e, s in entries_scores if s >= 0]

    def is_novel(self):
        """Is this a node for an unknown word?"""
        if len(self.entries) == 1 and self.entries[0].name == '*':
            return True
        return False

    ## Debugging methods for examining various node variables

    def exam_vars(self, dim_abbrev='', vartype='', var=''):
        dimD = self.dims
        varD = None
        for dim, vars in dimD.items():
            if dim.abbrev == dim_abbrev:
                varD = vars
        if varD:
            if vartype:
                vars = varD.get(vartype)
                if var and vars:
                    return vars.get(var)
                elif vars:
                    return vars
#                v = vars.get(var)
#                if v: v.pprint()
#                return v
            else:
#                for v in vars: v.pprint()
                return varD

    def exam_valency(self, dim_abbrev='', outs=True, var=''):
        return self.exam_vars(dim_abbrev=dim_abbrev,
                              vartype = 'outvars' if outs else 'invars',
                              var=var)

    def exam_agr(self, dim_abbrev='', var=''):
        return self.exam_vars(dim_abbrev=dim_abbrev,
                              vartype = 'agrvars',
                              var=var)

    def exam_lex(self, dstore=None):
        self.lexvar.pprint(dstore=dstore)
        return self.lexvar

    def get_possible_labels(self, dim, out=True):
        """Assign list of labels for possible in and out arcs for each dimension.
        Used in arc disambiguation."""
        labels = set()
        for entry, score in zip(self.entries, self.scores):
            if score >= 0:
                # Only record labels for entries that have not been excluded
                entry_dim = entry.dims.get(dim.abbrev)
                if entry_dim:
                    arcs = entry_dim.attribs.get('outs' if out else 'ins', {})
                    for label, attrib in arcs.items():
                        if attrib is not 0:
                            labels.add(label)
        return labels

    def get_required_labels(self, entry, dim, out=True):
        """Assign list of required out or in labels for a given entry on a dimension.
        Used in arc disambiguation.
        """
        d = entry.dims.get(dim.abbrev)
        if d:
            arcs = d.attribs.get('outs' if out else 'ins')
            if arcs:
                return [label for label, attrib in arcs.items() if attrib in ('!', '+')]
        return []

    def get_dim_dict(self, abbrev):
        """Get the dimension dict associated with the dimension with abbreviation abbrev."""
        for dim, dct in self.dims.items():
            if dim.abbrev == abbrev:
                return dct
        return {}

class EmptyNode(Node):
    '''Empty nodes: no form, at least in some language. They may end up "used" (with non-del in arcs
    on the dimension where they are created), or "unused" (with del in arcs on the dimension where they
    are created).'''

    def __init__(self, lexicon, problem, dstore, entry_key, src_entry, src_node_index,
                 dims=None, verbosity=0, index=-1):
        # An empty node starts with an entry already created ...
#        self.entry = entry.clone()
        # ... and source (mother) entry that it came from
        self.src_entry = src_entry
        # ... and a source (mother) node.
        self.src_node_index = src_node_index
        self.complex = False
        Node.__init__(self, entry_key + str(src_node_index), entry_key, lexicon, problem, dstore,
                      dims=dims, index=index, empty=True, eos=False)
        print('Created empty node {}, source: {}'.format(self, src_entry))
#        Node.__init__(self, entry.name + str(src_node_index), '', lexicon, problem, dstore,
#                      dims=dims, index=index, empty=True, eos=False)

#    def __repr__(self):
#        return '&{}{}'.format(self.index, self.entry.name)

    def initialize(self, dimensions, verbosity=0):
        """Find lexical entries and create all variables."""
        self.entries = []
        entries = self.lexicon.lexicalize(self.form, word=False, clone=True)
#        print('Empty node entries found for {}: {}'.format(self.form, entries))

#        self.entries = []
#        entries = [self.entry]
        
        # For each entry, inherit properties from lexical classes
        if self.languages or self.lexicon.hierarchical:
            for entry in entries:
                # Any additional entries found from classes during inheritance
    #            print('Adding entries for empty node {} starting with {}'.format(self, entry))
                add_entries = []
                # Accumulate entries to add
                self.lexicon.inherit(entry, [d.abbrev for d in dimensions],
                                     add_entries=add_entries, node=self,
                                     languages=self.languages,
                                     target_languages=self.target_languages,
                                     process=self.process,
                                     transfer_xlex=self.transfer_xlex,
                                     verbosity=verbosity)
                if add_entries:
                    # Add any new entries found to the node
                    self.entries.extend(add_entries)
        else:
            self.entries = entries

#        if not self.entries:
#            print('NO ENTRIES FOR {}!'.format(self))

        # Assign entry scores
        self.scores = [0 for e in self.entries]

    def finalize(self, verbosity=1):
        n_entries = len(self.entries)
        if n_entries == 0:
            print("WARNING: NO ENTRIES FOUND FOR {}".format(self))
        lexvar_name = '{}{}'.format(self.index, self.word)
        if n_entries == 1:
            # Determine the variable now if there's no ambiguity
            self.lexvar = DetIVar(lexvar_name, 0)
        else:
        ## Variable for node's entries.
            self.lexvar = IVar(lexvar_name,
                               set(range(n_entries)),
                               problem=self.problem, rootDS=self.dstore)

    

class ComplexEmptyNode(EmptyNode):
    '''Empty node with entries in two different languages, one "zero", and a relationship, "mother"
    or "daughter", with another node.'''

    def __init__(self, lexicon, problem, dstore, entry,
                 src_entry, src_entry_index, src_node_index,
                 targ_entries=None,
                 targ_lexicon=None, rel=None,
                 dims=None, rev=False, if_dim='',
                 verbosity=0, index=-1):
#        print('Making complex empty node; empty entry {}, src entry {}, if dim {}'.format(entry, src_entry, if_dim))
        self.entry = entry
        self.target_entries = [e.clone() for e in targ_entries]
#        for e in self.target_entries:
#$            print('  {} names {}'.format(e, e.names))
        self.target_lexicon = targ_lexicon
        self.target_language = targ_lexicon.language.abbrev
        self.rel = rel or ['mother']
        self.rev = rev
        self.if_dim = if_dim
        # A hack to make sure the node's entry has the right 'name', etc.
        for e in self.target_entries:
            current_names = e.names.get(self.target_language, {})
            if self.target_language not in e.names:
                e.names[self.target_language] = current_names
            if e.word:
                current_names['word'] = e.word
            elif e.lexeme:
                current_names['lexeme'] = e.lexeme
            elif e.gram:
                current_names['gram'] = e.gram
            if e.pos:
                current_names['pos'] = e.pos
            if e.root:
                current_names['root'] = e.root

        EmptyNode.__init__(self, lexicon, problem, dstore, entry.name, src_entry, src_node_index,
                           dims=dims, verbosity=verbosity, index=index)
        self.complex = True
#        self.trigger_entry_index = src_entry_index

#    def __repr__(self):
#        return '&{}@{}'.format(self.index, self.target_entries[0].get_name())

    def initialize(self, dimensions, verbosity=0):
        """Find lexical entries and create all variables."""
        entries = self.lexicon.lexicalize(self.form, word=False, clone=True)
#        print('Empty node entries found for {}: {}'.format(self.form, entries))

        self.entries = []
#        add_entries = self.target_entries[:]
        dims = [d.abbrev for d in dimensions]

        src_language = self.problem.language

        add_entries = []

#        print('<<<<<Inheriting for', self, 'and',
#              self.target_entries, 'lexicon', self.target_lexicon)
        if self.languages or self.lexicon.hierarchical:
            for targ in self.target_entries:
    #            print('{} inheriting from {}, dims {}'.format(self, targ, dims))
    #            print('Names {}'.format(targ.names))
                add_entries = []

                self.target_lexicon.inherit(targ, dims, node=self,
                                            add_entries=add_entries,
                                            languages=self.languages,
                                            target_languages=self.target_languages,
                                            transfer_xlex=self.transfer_xlex,
                                            # If reverse is True, we'll inherit back from the target lexical
                                            # node to its translation in the source language instead of maintaining.
                                            # But will this work for non-chunk translation??
                                            reverse=False,
                                            process=self.process,
                                            src_language=src_language,
                                            verbosity=verbosity)
                self.entries.extend(add_entries)
            for e in self.entries:
    #            print(' Inheriting from lex {}'.format(self.entry))
    #            for d in dims:
    #                if 'synsyn' not in d:
    #                    if d in e.dims:
    #                        ins = e.dims[d].__dict__.get('attribs', {}).get('ins')
    #                        if ins:
    #                            print(' Ins for {}/{}: {}'.format(e, d, ins))
                self.lexicon.inherit(e, dims, node=self,
                                     classes=[[self.entry]],
                                     add_entries=add_entries,
                                     languages=self.languages,
                                     target_languages=self.target_languages,
                                     transfer_xlex=self.transfer_xlex,
                                     # reverse used to be True here too, but this doesn't work with
                                     # chunking
                                     reverse=False,
                                     process=self.process,
                                     src_language=src_language,
                                     verbosity=verbosity)
        else:
            self.entries = entries

#        self.entries = add_entries

#        if not self.rev:
#        add_entries = []
        
#            for targ in self.target_entries:
#                self.target_lexicon.inherit(self.entry, dims, node=self,
#                                            classes=[[self.entry]],
#                                            add_entries=add_entries,
#                                            languages=self.languages,
#                                            target_languages=self.target_languages,
#                                            transfer_xlex=self.transfer_xlex,
#                                            reverse=True, process=self.process,
#                                            src_language=src_language,
#                                            verbosity=verbosity)
#
#        if add_entries:
#            self.entries.extend(add_entries)

        # Assign entry scores
        self.scores = [0 for e in self.entries]

    def finalize(self, verbosity=1):
        lexvar_name = '{}{}'.format(self.index, self.word)
        if len(self.entries) == 1:
            # Determine the variable now if there's no ambiguity
            self.lexvar = DetIVar(lexvar_name, 0)
        else:
        ## Variable for node's entries.
            self.lexvar = IVar('{}{}'.format(self.index, self.word),
                               set(range(len(self.entries))),
                               problem=self.problem, rootDS=self.dstore)
#        print('{} has entries: {}'.format(self, self.entries))
        
