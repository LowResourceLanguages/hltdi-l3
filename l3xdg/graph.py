#   Implementation of Extensible Dependency Grammar, as described in
#   Debusmann, R. (2007). Extensible Dependency Grammar: A modular
#   grammar formalism based on multigraph description. PhD Dissertation:
#   Universität des Saarlandes.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of Extensible Dependency Grammar.
#
#   Copyright (C) 2011, 2011, 2012, 2013
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
# 2010.10.27
# -- Created graph.py for Graphs and Multigraphs.
#    Methods for creating daughter and agrs dicts and pretty printing.
# 2010.10.31
# -- When Graph language is output language for translation and Graph
#    dimension is language's surface dimension, Graph assembles the
#    output sentence. For each node, it either spits out the 'word'
#    attribute, or it finds the pos, root, and agr dictionary and
#    generates the wordform.
# -- Sentence generation moved to MultiGraph because it also needs
#    output positions, which are in a different dimension (Graph) than
#    the agrs that are needed for wordform generation.
# 2011.02.02
# -- Semantic node labels get output in Graph.pprint() for Semantics
#    dimension and in Multigraph.io().
# 2011.02.06
# -- Graph.pprint() prints out the right surface form for target languages.
# 2011.02.22
# -- Multigraph.var() a handy way to examine variables within a given solution (dstore).
# 2011.03.10
# -- Deleted and empty nodes are marked as such; deleted nodes can be skipped in io().
# 2011.04
# -- Graphs are drawn by default.
# 2013.09.04
# -- Agreement feature-values pretty-printed.

# Default feature value; ignore features with this value when printing out graph
from .dimension import DFLT_FV
import sys

DELCHAR = '*'
WORDSEP = 11
LINE = 100

class Graph(dict):
    """The graph for a sentence on a single dimension.
    A dict of form {node: {label: {daughter_nodes}}}."""

    def __init__(self, dimension, language=None, nodes=None, dstore=None,
                 entries=None, is_output=False):
        """A graph needs a set of nodes, a domain store, and a language to get the
        values of variables it needs to initialize itself. A graph is a dict
        with nodes as keys and a label-key dict of daughters as values.
        Mothers are saved in a an attribute dict."""
        self.dimension = dimension
        self.abbrev = dimension.abbrev
        self.language = language
        self.nodes = nodes
        self.dstore = dstore
        self.entries = entries
        self.is_output = is_output
        self.make_forms, self.make_order = False, False
        if is_output:
            self.make_forms = self.abbrev == self.language.surface_dim
            self.make_order = self.abbrev == self.language.order_dim
        # Agreement features
        self.agrs = {}
        # Feature names to be ignored in display
        self.hide_feats = language.hide_feats
        # Word forms if this is an output language
        self.forms = {}
        # Positions if this is an output language
        self.positions = {}
        # List of deleted (zero) nodes
        self.del_nodes = []
        # List of root nodes
        self.root_nodes = []
        # List of subordinate nodes
        self.sub_nodes = []
        # Dict of mothers
        self.mothers = {}
        if nodes and dstore:
            self.create()

    def __repr__(self):
        return "<G {}/{} {}>".format(self.abbrev, self.dstore.name, self.dstore.level)

    def pprint(self, show_del=True, show_agrs=True):
        print('Dimension {}'.format(self.dimension.abbrev))
        for node, arcs in self.items():
            if show_del or node not in self.del_nodes:
                print('  {}'.format(node), end='')
                if self.forms:
                    print(' / {}'.format(self.forms[node]), end='')
                print()
                if arcs:
                    # arcs dict could be empty
                    print('    Daughters:: ', end='')
                    for label, daughters in arcs.items():
                        print('{}:{} '.format(label, daughters), end='')
                    print()
                if node in self.agrs:
                    print('    Agrs:: ', end='')
                    for label, value in self.agrs[node].items():
                        if value:
                            # Ignore 0 values
                            print('{}:{} '.format(label, value), end='')
                    print()
                if self.positions:
                    print('    Position:: {}'.format(self.positions[node]))
                
    def create(self):
        """Enter dictionaries for each node that has daughters and find the value of agrs."""
        abbrev = self.dimension.abbrev
        lang_abbrev = self.language.abbrev if self.language else ''
        for node in self.nodes:
            self[node] = {}
            nodedimD = node.dims[self.dimension]
            # Get the daughters of this node for each arc label
            for label in self.dimension.labels:
                # Daughter variable for this arc label
                var = nodedimD['outvars'][label][0]
                # Value of the daughter variable: indices of daughters
                daugh_indices = var.get_value(dstore=self.dstore)
                if daugh_indices:
                    # Use the daughter nodes rather than indices
                    daughters = [self.nodes[index] for index in daugh_indices]
                    self[node][label] = set(daughters)
                    for daughter in daughters:
                        self.add_mother(daughter, node, label)
                    # If the label is del, record that the daughters are deleted
                    if label == 'del':
                        self.del_nodes.extend(daughters)
                    elif label == 'root':
                        self.root_nodes.extend(daughters)
                    elif label == 'sub':
                        self.sub_nodes.extend(daughters)
            agrs = nodedimD.get('agrvars')
            if agrs:
                for label, var in agrs.items():
                    value = var.get_value(dstore=self.dstore)
                    if value not in [()]: #, DFLT_FV]:
                        # Don't record empty or default tuple values
                        if node not in self.agrs:
                            self.agrs[node] = {}
                        self.agrs[node][label] = value
#                        print('agrs: node {}, label {}, value {}'.format(node, label, self.agrs[node][label]))
            # If this is an output language, get information relevant for the
            # output form, including morphological features
            if self.make_forms or lang_abbrev == 'sem':
                # Add a form to the forms list for this word
                entry = self.entries[node]
                names = entry.names.get(lang_abbrev, {})
                agrs = self.agrs.get(node)
#                if agrs:
#                    print('Agrs for node', agrs)
                if 'word' in names:
                    w = names['word']
#                    print("Setting form for {}, names {}, name {}, word {}".format(self, names, names.get('name'), w))
                    # If the translation is unknown, use ?name
                    if 'name' in names and w == '*':
                        self.forms[node] = '?' + names['name']
#                        print('Set form for {} to {}'.format(node, self.forms[node]))
                    else:
                        # Otherwise use word
                        self.forms[node] = w
                elif 'label' in names:
                    self.forms[node] = names['label']
                elif lang_abbrev == 'sem':
                    # Otherwise for semantics, use the value of 'lexeme' or 'gram'
                    self.forms[node] = names.get('lexeme') or names.get('gram')
                elif self.language.morph_processing and 'root' in names:
                    # The output word has to be generated from its root and agrs
                    if 'root' not in names or 'pos' not in names:
                        print('Node {} has only names {}'.format(node, names))
                    root = names['root']
                    pos = names['pos']
                    self.forms[node] = (pos, root, agrs)
#                    print('forms for {}: {}'.format(node, self.forms[node]))
                elif 'lexeme' in names:
                    form = names['lexeme']
#                    print('Form for node {}: {}'.format(node, form))
                    # Words with form 0 don't get generated
                    if agrs and form != '0':
                        form = form + str(agrs)
                    self.forms[node] = form
                else:
                    # Otherwise use 'word' attribute of the node
                    self.forms[node] = node.word
            # Order dimension
            if self.make_order:
                # Position variable for this node
                posvar = nodedimD.get('posvar')
                # Its value is a singleton set
                pos = posvar.get_value(dstore=self.dstore)
                if not pos:
                    # Something wrong: the node must have a position (value is empty set)
                    print('Warning: pos var {} has no value'.format(posvar))
                    print(posvar, posvar.dstores)
                self.positions[node] = list(pos)[0]

    def draw_sentence(self, word_sep=WORDSEP, file=sys.stdout):
        """Write the words in the sentence, spaced appropriately."""
#        nodes = list(self.keys())
#        nodes.sort(key=lambda node: node.index)
        translate = self.forms
        for node in self.nodes:
            if translate:
                string = self.node_string(node, string=self.forms[node], word_sep=word_sep)
            else:
                string = self.node_string(node, word_sep=word_sep)
            print(string.ljust(word_sep), end='', file=file)
        print(file=file)

    def add_mother(self, daughter, mother, arc):
        """Record that mother is a mother of daughter along an arc with label arc."""
        if daughter not in self.mothers:
            self.mothers[daughter] = {}
        if arc not in self.mothers[daughter]:
            self.mothers[daughter][arc] = set()
        self.mothers[daughter][arc].add(mother)

    def draw_roots_dels(self, word_sep=WORDSEP, file=sys.stdout):
        """Write deleted nodes and roots in word positions."""
        root_del_string = ''
        for index, node in enumerate(self.nodes):
            if node in self.del_nodes:
                root_del_string += 'X'.ljust(word_sep)
            elif node in self.root_nodes:
                root_del_string += 'ROOT'.ljust(word_sep)
            elif node in self.sub_nodes:
                root_del_string += 'SUB'.ljust(word_sep)
            else:
                root_del_string += ' ' * word_sep
        print(root_del_string, file=file)
        
    def node_string(self, node, string='', word_sep=WORDSEP):
        word = string or node.word
        if word == 'zero':
            return '0'
        if len(word) > word_sep - 2:
            return word[:word_sep-2] + '.'
        return word

    def draw_order(self, word_sep=WORDSEP, file=sys.stdout):
        """Write the positions of the words for an output sentence."""
        position_string = ''
        for index, node in enumerate(self.nodes):
            position_string += str(self.positions[node]).ljust(word_sep)
        print(position_string, file=file)

    def draw_agrs(self, word_sep=WORDSEP, infeats=None, file=sys.stdout):
        """Show selected agreement features and values for all nodes."""
        agrs = [list(self.agrs.get(node, {}).items()) for node in self.nodes]
        while any(agrs):
            s = ''
            for agr in agrs:
                any_fv = False
                while agr and not any_fv:
                    f, v = agr.pop(0)
                    # Don't display features with negative values
                    if len(v) == 1 and list(v)[0] < 0:
                        continue
                    if (infeats and f in infeats) or (f not in self.hide_feats):
                        any_fv = True
                        s += "{}".format(self.agr_string(f, v)).ljust(word_sep)
                if not any_fv:
                    s += "".ljust(word_sep)
            if s:
                print(s, file=file)

    def agr_string(self, feat, value):
        """Simplify value int tuple to string of ints."""
        vs = ''
        for v in value:
            vs += str(v)
        return "{}={}".format(feat, vs)

    def draw(self, word_sep=WORDSEP, show_agrs=True, show_order=True, file=sys.stdout):
        self.draw_sentence(word_sep=word_sep, file=file)
        if show_agrs:
            self.draw_agrs(word_sep=word_sep, file=file)
        if show_order and self.positions:
            self.draw_order(word_sep=word_sep, file=file)
        self.draw_roots_dels(word_sep=word_sep, file=file)
        for node, arcs in self.items():
            start = node.index
            if arcs:
                for label, daughters in arcs.items():
                    if label not in ['del', 'root', 'sub']:
                        for daughter in daughters:
                            end = daughter.index
                            self.draw_arc(start, end, label, word_sep, file=file)

    def draw_arc(self, start, end, label, word_sep=WORDSEP, file=sys.stdout):
        pos0 = start * word_sep
        pos1 = end * word_sep
        pos0 = pos0
        pos1 = pos1
        arrow_length = abs(pos1 - pos0)
        shaft = label.center(arrow_length-1, '-')
        if start < end:
            # Draw from start to end
            print('{}{}>'.format(' ' * pos0, shaft), file=file)
        else:
            print('{}<{}'.format(' ' * pos1, shaft), file=file)

class Multigraph(dict):
    """The multigraph for a sentence on all dimensions.
    A dict of form {dim: graph}."""

    def __init__(self, problem, arc_dims, if_dims, dstore, 
                 morf_verbosity=0):
        self.problem = problem
        self.sentence = problem.sentence
        self.sent_string = problem.name
        self.arc_dims = arc_dims
        self.if_dims = if_dims
        self.dstore = dstore
        self.nodes = problem.nodes + problem.empty_nodes
        self.language = problem.language
        # Make a dictionary for each output language: 'formgraph', 'posgraph', 'sentence'
        self.languages = {lang: {'sentence': [''] * len(self.sentence)} for lang in problem.languages}
        # Semantic "language" if there is one
        self.semantics = problem.semantics
        # For the representation of the semantic output
        self.semrep = []
        # To hold entries of nodes
        self.entries = {}
        if self.language and self.nodes and self.dstore:
            self.create(morf_verbosity=morf_verbosity)

    def __repr__(self):
        ds = self.dstore
        level = ds.level
        name = ''
        if level > 0:
            name = ds.name
        return "<MG {}: {}>".format(name, self.problem.name)
        
    def var(self, vname):
        """Returns the variable dict for the variable with name vname in this solution's dstore."""
        variable = self.problem.varsD.get(vname)
        if variable:
            return variable.get_value(dstore=self.dstore)
        
    def io(self, show_del=False, show_input=False, semantics=False):
        '''Show input and output sentences and semantics, if specified.'''
        if show_input:
            print('Input ({}): {}'.format(self.language.name, self.sent_string))
            return self.sent_string
        if not self.languages and (self.semantics and semantics):
            output = self.semrep
            if not show_del:
                output = [form for form in output if form and form[0] != DELCHAR]
            joined = ' '.join(output)
            print('Semantics: {}'.format(joined))
            return joined
        for language, attribs in self.languages.items():
            output = attribs['sentence']
            if not show_del:
                output = [form for form in output if form and form[0] != DELCHAR]
            joined = ' '.join(output)
            print('Output ({}): {}'.format(language.name, joined))
            return joined

    def display(self, draw=True, dims=None, line=LINE,
                show_del=True, show_agrs=True, show_order=True,
                file=sys.stdout):
        """Pretty-print or draw the multigraph, restricting the graphs to those
        in dims (a list of dimension abbreviations) if dims is not None."""
        self.multigraph_header(line=line, file=file)
        self.io(show_del=show_del)
        if self.groups:
            print('Groups')
            print(self.groups)
#            for group in self.groups.values():
#                print('  ', group)
        for dim in self.arc_dims:
            abbrev = dim.abbrev
            if not dims or abbrev in dims:
                self.graph_header(abbrev, line=line, file=file)
                graph = self[dim.abbrev]
                if draw:
                    graph.draw(show_agrs=show_agrs, file=file)
                else:
                    graph.pprint(show_del=show_del)

    @staticmethod
    def d(multigraphs, dims=None, draw=True, line=LINE, file=sys.stdout):
        """Draw each of a collection of multigraphs."""
        if not isinstance(multigraphs, list):
            multigraphs = [multigraphs]
        if dims and not isinstance(dims, list):
            dims = [dims]
        for graph in multigraphs:
            print(file=file)
            graph.display(draw=draw, dims=dims, line=line, file=file)
            
    def multigraph_header(self, line=LINE, file=sys.stdout):
        print('  SOLUTION {}  '.format(self.__repr__()).center(line, '='), file=file)

    def graph_header(self, abbrev, line=LINE, file=sys.stdout):
        print(' {} '.format(abbrev).center(line, '_'), file=file)

    def get_groups(self):
        """Multiword expressions."""
        groups = {}
        for node, entry in self.entries.items():
#            print('Getting groups for {}/{}; {}'.format(node, entry, entry.gid))
            gid = entry.gid
            if gid:                
                groups[gid] = groups.get(gid, []) + [node]
        return groups

    def get_semgraph(self):
        """The Graph for Semantics."""
        return self.get('sem')

    def create(self, morf_verbosity=0):
        # Set the node entries
        self.entries = {node: node.entries[node.lexvar.get_value(dstore=self.dstore)] for node in self.nodes}
        # Find groups (this should be by language)
        self.groups = self.get_groups()
        # Create the dimension graphs
        for dimension in self.arc_dims:
            language = dimension.language
            graph = Graph(dimension, language, self.nodes, self.dstore,
                          entries=self.entries,
                          is_output=(language and (self.language != language)))
            if graph.make_forms:
                self.languages[language]['formgraph'] = graph
            if graph.make_order:
                self.languages[language]['posgraph'] = graph
            self[dimension.abbrev] = graph
        # Create the output sentence(s) if there are output languages
        if self.languages:
            for language, attribs in self.languages.items():
                sentence = attribs['sentence']
                ordergraph = attribs['posgraph']
                formgraph = attribs['formgraph']
                del_nodes = formgraph.del_nodes
                for node in self.nodes:
                    position = ordergraph.positions[node]
                    # Sentence may not be long enough because target
                    # requires more words than source
                    if len(sentence) <= position:
                        sentence.extend([''] * (position - len(sentence) + 1))
#                        sentence.append('')
                    form = formgraph.forms[node]
                    if not isinstance(form, str):
                        # form is a tuple specifying inputs to morphological generation
                        pos, root, dct = form
                        if morf_verbosity:
                            print('Generating wordform: pos', pos, 'root', root, 'dct', dct,
                                  'formgraph', formgraph, 'form', form)
                        wordform = language.gen_word(pos, root, dct,
                                                     formgraph[node], formgraph.mothers.get(node),
                                                     formgraph.forms, del_nodes)
                        if wordform:
                            sentence[position] = wordform
                            # Replace the form with the generated wordform
                            formgraph.forms[node] = wordform
                        else:
                            # Use the root if it's impossible to generate the wordform
#                            sentence[position] = str(form)
                            sentence[position] = root
                    else:
                        sentence[position] = form
                # Do this later because a word may have been deleted in morphological generation
                for node in self.nodes:
                    position = ordergraph.positions[node]
                    if node in del_nodes:
                        # Nodes with no content; deleted in formgraph
                        sentence[position] = DELCHAR + sentence[position]
                    elif node in ordergraph.del_nodes:
                        # Contentful nodes with no output position
                        sentence[position] = '(' + sentence[position] + ')'
        # Create a semantic representation
        if self.semantics:
            # Create a representation for the semantic output
            semgraph = self.get_semgraph()
            for node in self.nodes:
                name = self.get_node_name('sem', node)
                # Mark deleted nodes
                if node in semgraph.del_nodes:
                    name = DELCHAR + name
                self.semrep.append(name)

    def get_node_name(self, lang_abbrev, node):
        entry = self.entries.get(node)
        if entry:
            names = entry.names.get(lang_abbrev)
            if names:
                return names.get('word') or names.get('lexeme') or names.get('gram') or entry.get_name()
        return ''

