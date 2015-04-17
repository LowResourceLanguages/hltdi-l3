#   
#   Python implementation of Extensible Dependency Grammar, as described in
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
# 2010.07.29 (MG)
#
# 2010.08.08 (MG)
# -- Valency and tree constraints seem to work, but there is apparently an error with
#    is_entailed() for some constraint types
# 2010.08.09 (MG)
# -- The problem wasn't is_entailed() but the way propagators were initialized
#    in new CSpaces. This is fixed now, and example sentences now work
#    for valency and tree constraints.
# 2010.08.11 (MG)
# -- Added order constraints, using new class in constraints.
#    But "john saw the saw" doesn't work yet.
# 2010.08.12 (MG)
# -- Can now analyze "jack (3) saw (2) the saw (2)" (12-way ambiguous) in .3 s!
#    but what happens with more arc labels (only 4 now) and multiple dimensions.
# 2010.08.13 (MG)
# -- Projectivity, using SetConvexity propagator; correctly causes failure for
#    "john the bought saw"
# -- Started agreement principle: agrs variables (one for each feature) and
#    agree variable for nodes; selection constraints for each
# 2010.08.17 (MG)
# -- Agreement principle works for Swahili examples 9 and 10.
#    Uses separate variables for daughter label/agreement feature combinations.
# 2010.08.21 (MG)
# -- Node in a separate module.
# -- XDG has dict of dimension instances and dimension-specific variables.
# -- Graph variables and constraints handled by TreePrinciple.
# 2010.09.04 (MG)
# -- XDG now has a dictionary for constraints (propsD) as well as for variables.
# -- Languages now loaded once for multiple sentences.
# 2010.09.24 (MG)
# -- Dimensions of XDG default to all in language.
# -- Input sentence can be string with no EOS character
#    (converted to list of strings; EOS char appended)
# 2010.10.17 (MG)
# -- Entries resulting from morphological analysis now incorporated into analysis.
# 2010.10.18 (MG)
# -- Pre-processing of sentences now happens separately from morphological analysis.
# 2010.10.26 (MG)
# -- Solution class to represent parsing (generation, translation) solutions
# -- XDG method solve() instantiates solver and returns list of Solution objects for
#    spaces (instances of CSpace) of solution nodes.
# 2010.10.27
# -- Graph and Multigraph classes created (in graph.py) to do the work of making
#    the output graphs for parsing and input graphs for generation.
# -- Got rid of Solutions, which are now redundant.
# -- XDG.solve() returns Multigraphs for each solution.
# 2010.10.28
# -- Added multiple languages to XDG constructor
# 2010.11.14
# -- reinit method allows re-parsing sentence.
# 2010.11.19
# -- Grammar name (e.g., 'water') can be passed to XDG constructor to override
#    default grammar for languages.
# 2010.12.23
# -- Changes in parameters for XDG constructor.
# 2011.01.12
# -- Solutions saved in XDG attribute.
# 2011.01.13
# -- XDG.diff_sols compares variable bindings in two solutions.
# 2011.01.29
# -- Semantics created only when called for (in XDG constructor).
# 2011.02.10
# -- XDG methods to create empty nodes.
# 2011.03.01
# -- Changed solve() so that it generates solutions individually,
#    using the new generators in search.py.
# 2011.03.26
# -- XDG constructor sorts variables.
# 2011.03.29
# -- Possible to have Semantics as the input language.
# 2011.05.17
# -- Both kinds of empty nodes created during initialization.
# 2011.10.05
# -- Fixed a problem with generation that was preventing 
#    interface dimensions from being instantiated.
# 2011.12.06
# -- Incorporated reverse ComplexEmptyNodes
# 2011.12-2012.02
# -- Projectors incorporated.
# 2012.04.04
# -- Rearranged order of loading languages, finalizing languages, loading
#    morphology and pickling languages, using Language.load_langs.
# 2012.09.07
# -- Added possibility of segmentation of words during tokenization phase
#    and morphological analysis.
# 2012.09.13
# -- Arcs can now be created before CS, either as part of tokenization
#    (through a .tok file) or morphological analysis (specified in a .gr
#    file)
# 2012.11.30
# -- Fixed a serious bug with tokenization that got the indices of words
#    after insertion wrong.
# 2013.08.05
# -- Complex crosslexes are checked for condition on creation of empty node.
# 2013.09.04
# -- Segmentation of words during tokenization fixed: analyze() and record_pre_arcs().
#    Form that remains is now generated (it may different from root because other affixes
#    may not be separated).
# 2014.02.04
# -- Method (record_solution()), which records occurrence of entries in a selected
#    solution.
#########################################################################

# imports search
from .solver import *
# imports variable
from .node import *
# imports lex, crosslex, and morphology
from .language import *
# imports constraint, which imports variable
from .dimension import *
from .graph import *
from .disambig import *
# For combinations
import itertools
# Type checking
import inspect

from .utils import PARSE, GENERATE, TRANSLATE

class XDG(CSP):
    """A subclass of CSP whose constraints represent the lexical and grammatical constraints
    within the words of a sentence. An XDG instance represents a sentence on one or more
    dimensions, usually including dimensions on multiple 'languages', where Semantics
    is considered a 'language'.
    """

    def __init__(self, sentence, lang='en', target=None, grammar='tiny',
                 lexicon=None, solver=None,
                 load_semantics=True, transfer_xlex=False,
                 # Arcs to be created before constraint satisfaction.
                 # Dict of dim abbrevs whose values are dicts of arc labels whose values are src, dest
                 # index tuples.
                 pre_arcs=None,
                 # Feature values to be assigned before constraint satisfaction.
                 # Dict of dim abbrevs whose values are dicts of agr features whose values are tuples
                 # of integers.
                 pre_agrs=None,
                 # list of principles, dimensions, languages whose constraints are to be weakened
                 weaken=None,
                 # if not None, only satisfy constraints on these dimensions
                 dims=None,
                 # if not None, only satisfy constraints for these principles
                 princs=None,
                 # whether to use projectors in CS
                 project=False,
                 process=0,
                 # If non-negative, trace inheritance for this node
                 trace_node_inh=-1,
                 pause=True,
                 # Whether to reload the lexicon even if it's been pickled
                 reload=False,
                 # Whether to flatten the loaded lexicon
                 flatten_lexicon=False,
                 # Whether to pickle a newly created (or flattened) lexicon
                 pickle=False,
                 # Whether to instantiate principles
                 create_princs=True,
                 distributor=None,
                 # Verbosity is for debugging; report is for top-level information
                 verbosity=0, report=1):
        """
        Assign language, lexicon, dimensions; create nodes; instantiate principles; run constructor for CSP.
        """
        
        ## Debugging
        self.verbosity = verbosity
        self.report = report
        ## Languages
        # lang and target could be language ids (strings) or Language instances
        if isinstance(lang, str):
            lang_ids = [lang]
            if target:
                lang_ids += target
            if load_semantics:
                lang_ids.append('sem')
            # load them
            languages = Language.load_langs(lang_ids, analysis=True, generation=True, lexicon=True,
                                            force=reload, pickle=pickle, flatten=flatten_lexicon,
                                            load_morpho=True, grammar=grammar, semantics=True,
                                            verbosity=verbosity)
        else:
            languages = [lang]
            if target:
                languages.append(target)
            if load_semantics:
                languages.append(semantics)
        self.language = languages[0]
        if load_semantics:
            self.semantics = languages[-1]
            self.languages = languages[1:-1]
        else:
            self.semantics = None
            self.languages = languages[1:]

        # Whether to access transfer xlexes
        self.transfer_xlex = transfer_xlex
        ## Type of processing: parse, generate, translate
        if process:
            self.process = process
        elif self.languages:
            self.process = TRANSLATE
        else:
            self.process = PARSE

        ## Sentence and nodes
        self.nodes = []
        self.empty = []
        self.sentence = self.make_sentence(sentence)
        self.name = ' '.join(self.sentence)

        ## Solving
        self.solver = None
        self.dstore = DStore(self.name)
        # To save solutions once solve is called
        self.solutions = []

        ## Lexicons
        self.lexicon = self.language.lexicon
        self.other_lexicons = [language.lexicon for language in self.languages]
#        if self.process == TRANSLATE:
#            self.crosslexicon = self.get_crosslexicon()

        ## Weakening
        self.weaken = weaken or []
            
        ## Dimensions
        # Get dimension classes for input language
        dim_classes = dims or self.get_dim_classes(self.language, not self.semantics and lang != 'sem',
                                                   transfer=self.transfer_xlex)
        # Separate them into arc vs. IF classes and syn vs. sem classes
        (arc_dim_classes1, arc_sem_classes), (if_dim_classes1, if_sem_classes) = self.sep_dim_classes(dim_classes)
        # Instantiate arc dimensions and create a dict for dimension-specific problem variables
        self.dims = {dim(language=self.language, problem=self, project=project): {} for dim in arc_dim_classes1}
#        print('Dims 1 {}'.format(self.dims))
        # Add arc dimensions from other languages, including semantics if load_semantics
        lang_if_dim_classes = []
        for language in self.languages + ([self.semantics] if self.semantics else []):
#            print('Making dims for language {}'.format(language))
            dim_classes = dims or self.get_dim_classes(language, not self.semantics and lang != 'sem',
                                                       transfer=self.transfer_xlex)
            (arc_dim_classes, arc_sem_classes0), (if_dim_classes, if_sem_classes0) = self.sep_dim_classes(dim_classes)
            weight = 0 if (language.abbrev in self.weaken) else 1
            self.dims.update({dim(language=language, problem=self, weight=weight, project=project): {} for dim in arc_dim_classes})
            lang_if_dim_classes.append(if_dim_classes)
            # Add new sem classes if they're not already included
            arc_sem_classes.update(arc_sem_classes0)
            if_sem_classes.update(if_sem_classes0)
            
        # Create arc semantic dimensions
        if load_semantics or lang == 'sem':
            l = self.semantics or self.language
            weight = 0 if ('sem' in self.weaken) else 1
            self.dims.update({dim(language=l, problem=self, weight=weight, project=project): {} for dim in arc_sem_classes})
        self.arc_dims = list(self.dims)
        # We need these when recording pre_arcs
        self.source_arc_dims = [d.abbrev for d in self.arc_dims if d.language == self.language]
        # Create IF dimensions for input language
        # Instantiate interface dimensions, searching for subdimensions among already instantiated arc dimensions
        if_dict, self.if_dims = self.make_if_dimensions(if_dim_classes1, self.arc_dims, self.language)
        # Create IF dimensions for other languages, though this should only be necessary if semantics
        # or some other language intervenes
        #        if not transfer:
        for language, if_classes in zip(self.languages, lang_if_dim_classes):
            dct, ls = self.make_if_dimensions(if_classes, self.arc_dims, language)
            if_dict.update(dct)
            self.if_dims.extend(ls)
        # Add IF semantic dimensions
        if load_semantics or lang == 'sem':
            l = self.semantics or self.language
            for if_classes in if_sem_classes:
                dct, ls = self.make_if_dimensions(if_classes, self.arc_dims, l)
                if_dict.update(dct)
                self.if_dims.extend(ls)
        # Add all IF dimension dicts to the dim dicts
        self.dims.update(if_dict)
        # List of instantiated dimensions
        self.dim_objs = list(self.dims.keys())
        # Put interface dimensions at the end so their principles get instantiated last.
        self.dim_objs.sort(key=lambda d: isinstance(d, IFDimension))
        
        ## Preprocessing, including morphological analysis
        # First load morphology
#        print("Loading languages' morphology")
#        self.language.load_morphology()
#        for language in self.languages:
#            language.load_morphology()
        self.proc_sentence = self.preprocess()
        # Keep lexicon entry indices here if they're available
        self.lex_indices = [None for x in range(len(self.sentence))]
        # Specs for arcs to be created before CS
        self.pre_arcs = pre_arcs or {}
        # Specs for feature values to be created before CS
        self.pre_agrs = pre_agrs or {}
        self.agree_dims = [d for d in self.dim_objs if AgreementP in d.princ_classes]
        # Do morphological if appropriate; assign self.analysis
#        self.analysis = self.analyze()
        self.analyze()

        ## Tokenize: split single words into multiple words, potentially changing
        ## sentence length
        self.tokenize()

        ## Variable and propagator dictionaries (only for debugging?)
        self.varsD = {}
        # We don't want propagators associated directly with determined variables,
        # which are mainly constants, so store them in a problem-specific dict:
        # {var: propagators}
        self.detvarsD = {}
        self.propsD = {}

        ## Values governing variable domains
        self.sentence_length = len(self.sentence)
        if self.eos == 'start':
            self.eos_index = 0
        else:
            self.eos_index = self.sentence_length - 1
        self.max_set = set(range(self.sentence_length))
#        self.positions = set(range(self.eos_index))

        if report:
            print('Creating nodes')
        ## Make nodes
        self.make_nodes(trace=trace_node_inh)
        self.make_empty_nodes(verbosity=verbosity)

        ## Additional values governing variable domains, when empty nodes are considered
        self.n_all_nodes = self.sentence_length + len(self.empty_nodes)
        empty_indices = set([node.index for node in self.empty_nodes])
        self.all_indices = self.max_set | empty_indices
        # Order constraints *can* refer to final punctuation
        self.positions = self.all_indices

        ## Run disambiguation to eliminate, punish, or favor particular entries.
        self.disambiguate(verbosity=verbosity)

        ## Instantiate principle variables and propagators
        # Save them (only for debugging?)
        self.principles = []
        if create_princs:
            if report:
                print('Instantiating principles')
            for dim in self.dim_objs:
                if princs:
                    dim.inst_principles(princs)
                else:
                    dim.instantiate_princs()
                # Create variables
                for princ in dim.principles:
                    self.principles.append(princ)
                    princ.make_variables()
            # Create constraints; among other things, this calls
            # make_constraints() in all principles
            CSP.__init__(self, self.name, self.dstore, distributor=distributor,
                         project=project, report=report)
            # Sort the variables to maintain consistency during search.
            # Later allow for smarter sorting.
            self.dstore.undetermined.sort(key=Variable.get_name)
##            if self.project:
##                # Set reexec events
##                for p in self.projectors:
##                    p.assign_reexec_events(self.dstore)

        if report:
            describe = 'Created XDG {}, {} propagators'
#, {} projectors'
            print(describe.format(self, len(self.propagators)))
#, len(self.projectors)))
# for grammar {}'.format(self, grammar))
#        if not self.semantics or self.transfer_xlex or self.weaken:
#            print('  Semantics: {}, transfer: {}, weakened: {}'.format(self.semantics, self.transfer_xlex, self.weaken))
            
    def reinit(self, distributor=None):
        '''Start over with new variables, constraints, and principle instances.'''
        self.dstore = DStore(self.name)
        self.varsD = {}
        self.propsD = {}
        for dim in self.dim_objs:
            dim.dstore = self.dstore
            for princ in dim.principles:
                princ.dstore = self.dstore
        for node in self.nodes:
            node.dstore = self.dstore
            node.groupvar = None
            node.initialize(self.dim_objs)
        for node in self.empty_nodes:
            node.dstore = self.dstore
            node.initialize(self.dim_objs)
        for dim in self.dim_objs:
            for princ in dim.principles:
                princ.make_variables()
        CSP.__init__(self, self.name, self.dstore,
                     distributor=distributor)

    def get_dim_classes(self, language, ign_semantics=False,
                        transfer=True):
        '''Find classes for language dimension abbreviations.'''
        dims = [dim.split('-')[-1] for dim in language.dimensions]
        dims_copy = dims[:]
        if ign_semantics:
            # Eliminate any interface dimensions with Semantics
            for dim in dims_copy:
                if dim in DIMENSIONS['semif']:
                    dims.remove(dim)
        # No target languages
        if not self.languages or not transfer:
            # Eliminate any interface dimensions with other languages
            for dim in dims_copy:
                if dim in DIMENSIONS['crossif']:
                    dims.remove(dim)
        return {DIM_ABBREV_DICT[abbrev] for abbrev in dims}

    def sep_dim_classes(self, classes):
        '''Separate a list of dimension classes into arc and IF dimension classes,
        separated in turn by whether they are syntactic or semantic classes.'''
        arc_syn_classes, if_syn_classes = [], []
        arc_sem_classes, if_sem_classes = set(), set()
        arc_classes, if_classes = [], []
        for cls in classes:
            if issubclass(cls, ArcDimension):
                if issubclass(cls, SemDimension):
                    arc_sem_classes.add(cls)
                else:
                    arc_syn_classes.append(cls)
            else:
                if issubclass(cls, SemDimension):
                    if_sem_classes.add(cls)
                else:
                    if_syn_classes.append(cls)
        return (arc_syn_classes, arc_sem_classes), (if_syn_classes, if_sem_classes)

    def make_if_dimensions(self, if_dim_classes, arc_dims, language):
        """Instantiate interface dimensions for language."""
        dim_list = []
        dim_dict = {}
        for dim in if_dim_classes:
            # Instantiate IF dimension
            weight = 0 if (language.abbrev in self.weaken) else 1
            ifdim = dim(language=language, problem=self, weight=weight)
            dimclass1, dimclass2 = ifdim.dimclass1, ifdim.dimclass2
            # Get dim1 and dim2 for the IFDimension from the already instantiated
            # ArcDimensions
            for d in arc_dims:
                # arc_dims could belong to multiple languages, including semantics
                if d.language == language or d.language == self.semantics:
                    if isinstance(d, dimclass1):
                        ifdim.dim1 = d
                    elif isinstance(d, dimclass2):
                        ifdim.dim2 = d
            # If this is a cross-linguistic IF dimension, dim2 may still not be
            # assigned.

            if not ifdim.dim2:
                for d in arc_dims:
                    if d.language != language and isinstance(d, dimclass2):
                        ifdim.dim2 = d
#            print('ifdim {}, dim1 {}, dim2 {}'.format(ifdim, ifdim.dim1, ifdim.dim2))

            # Check again to see if the dimension should be weakened
            if ifdim.dim1.language.abbrev in self.weaken or ifdim.dim2.language.abbrev in self.weaken:
                ifdim.weight = 0
                
            dim_dict[ifdim] = {}
            dim_list.append(ifdim)
#            print('Created', ifdim, 'with dim1', ifdim.dim1, 'dim2', ifdim.dim2)
        return dim_dict, dim_list
        
    def get_dimension(self, lg_abbrev, dim_type):
        """Get the dimension of dim_type for language."""
        for dim in self.dim_objs:
            if isinstance(dim, dim_type):
                if lg_abbrev:
                    lang = dim.language
                    if lang and lang.abbrev == lg_abbrev:
                        return dim
                else:
                    return dim
        
    def get_principle(self, lg_abbrev, dim_type, princ_type):
        """Find a principle for language of dimension type and principle type."""
        dimension = self.get_dimension(lg_abbrev, dim_type)
        if dimension:
            for princ in dimension.principles:
                if isinstance(princ, princ_type):
                    return princ

    def make_sentence(self, item):
        """Make a list of words from item if it's not already one, and add sentence-final word if needed."""
        if isinstance(item, str):
            item = item.split()
        if self.language.is_eos(item[0]):
            # The EOS word could be first
            self.eos = 'start'
        else:
            self.eos = 'end'
            if not self.language.is_eos(item[-1]):
                item.append(self.language.dflt_eos)
        return item

    def preprocess(self):
        """Preprocess sentence if language has a preproc function, storing
        the result in self.proc_sentence.
        Keep the original, tokenized sentence in self.sentence."""
        if self.language.preproc:
            return [self.language.preproc(word) for word in self.sentence]
        return self.sentence[:]

    @staticmethod
    def sem_dict2string(dct, arcs=None, agrs=None, head_pos=0, position=-1, top=True):
        '''Convert a semantic representation in dict form to a list of string, arcs, and agrs.
        {"": ["STATEMENT", {"root": ["SEE", {"arg1": "PETER",
                                             "arg2": ["WOMAN",
                                                      {"dem": "THIS"},
                                                      {"num": (1,)}]},
                                            {"reltime": (0,)}]}]}
        '''
        strings = []
        arcs = arcs or {}
        agrs = agrs or {}
        if top and not "" in dct:
            # No root (EOS) lex is specified; use STATEMENT
            dct = {"": ["STATEMENT", dct]}
        for arc, word in dct.items():
            position += 1
            if not isinstance(word, list):
                word = [word]
            w = word[0]
            ar = word[1] if len(word) > 1 else {}
            ag = word[2] if len(word) > 2 else {}
            strings.append(w)
            if arc:
                arcs[arc] = (head_pos, position)
            if ag:
                for a, f in ag.items():
                    if a in agrs:
                        agrs[a].append((position, f))
                    else:
                        agrs[a] = [(position, f)]
            if ar:
                s0, ar0, ag0, pos = XDG.sem_dict2string(ar, head_pos=position, position=position, top=False)
                strings.extend(s0)
                arcs.update(ar0)
                agrs.update(ag0)
                position=pos
        return strings, arcs, agrs, position

    def analyze(self):
        """Analyze words in the sentence, possibly creating new words in the process."""
        if self.language.morph_processing:
            if self.report:
                print('Doing morphological analysis')
            self.analysis = []
            segmentations = []
            for position, (word, form) in enumerate(zip(self.sentence, self.proc_sentence)):
                anals = []
                analyses = self.language.anal(word, form)
                new_word = word
                if analyses:
                    for root, grams in analyses[1]:
                        # Look for lexical entries for each analysis
                        anal_lexs = self.lexicon.lexicalize(root, word=False)
                        if anal_lexs:
                            anals.extend([(l, grams) for l in anal_lexs])
                    segs = analyses[2]
                    new_word = analyses[3]
                    if segs:
                        root = analyses[1][0][0]
                        if len(segs) > 1:
                            segs.sort(key=lambda x: x[0][0] == '_')
                        for seg in segs:
                            segmentations.append([position, (root, anals), seg, new_word])
#                    print('Analyses for {}: {}'.format(position, analyses))
#                    if new_word:
#                        print("New word for {}: {}".format(word, new_word))
                self.analysis.append(anals)
            # Do any insertions that resulted from segmentations during analysis
            for position, (root, anal), segments, new_word in reversed(segmentations):
                toks, indices, arcs = segments
                # Make a copy because we're going to mutate toks and don't
                # want it to apply to later sentences
                toks = toks[:]
                root_pos = toks.index('_')
                len_pre = root_pos
                len_post = len(toks) - root_pos - 1
                # Replace _ with the root
                toks[root_pos] = new_word if new_word else root
                anals = [[] for x in range(len_pre)] + [anal] + [[] for x in range(len_post)]
#                print('  segmentation pos {}, root {}, n tokens {}, n anals {}, len_pre {}, len_post {}'.format(position,
#                                                                                                                root, len(toks), len(anals),             
#                                                                                                                len_pre, len_post))
                self.record_tokenization(position, tokens=toks, lex_indices=indices,
                                         arcs=arcs, analyses=anals)
        else:
            self.analysis = [[] for x in range(len(self.sentence))]

    def tokenize(self):
        """Attempt to tokenize the sentence, possibly adding new words."""
        if not self.language.tokenization:
            if self.report:
                print("No tokenization data for {}".format(self.language))
            return
        tokenization = self.language.tokenization
        replacements = []
        for pos, (word, anal) in enumerate(zip(self.sentence, self.analysis)):
            if anal:
                # Don't tokenize words that have been analyzed morphologically
                continue
            toks = tokenization.get(word)
            if toks:
                if self.report:
                    print("Tokenizing {} as {}".format(word, toks))
                replacements.append([pos, toks])
        for position, tokens in reversed(replacements):
            toks, indices, arcs = tokens
            # Fix this later
#            indices = [{x} for x in indices]
            anals = [[] for x in range(len(toks))]
            self.record_tokenization(position, tokens=toks, lex_indices=indices,
                                     arcs=arcs, analyses=anals)

    def record_tokenization(self, position=0, tokens=None, lex_indices=None, arcs=None, analyses=None):
        """Record tokenization by modifying sentence representations
        and pre_arcs dict."""
#        print('Record tok {} {} {} {} {}'.format(position, tokens, lex_indices, arcs, analyses))
        self.replace(tokens, position, self.sentence)
        self.replace(tokens, position, self.proc_sentence)
        self.replace(lex_indices, position, self.lex_indices)
        self.replace(analyses, position, self.analysis)
        if arcs:
            self.record_pre_arcs(position, arcs)

    def replace(self, words, position, sentence):
        """Replace a word in the sentence with two or more words.
        replace(['they', 'are'], 0, "they're almost ready") =>
          "they are almost ready"
        """
        sentence[position:position+1] = words

    def record_pre_arcs(self, position, arcs):
        """Record pre_arcs given a position for the head."""
        n_nodes = len(arcs)
        positions = [i + position for i in range(len(arcs))]
#        print('Recording pre arcs {} for position {} in {}; source arc dims {}'.format(arcs, position, positions, self.source_arc_dims))
        for d in self.source_arc_dims:
            d_arcs = [a.get(d) for a in arcs]
            if any(d_arcs):
                a_p = dict(zip(d_arcs, positions))
                head = a_p.get('->')
                for arc, pos in a_p.items():
                    if arc == '->':
                        continue
                    if d not in self.pre_arcs:
                        self.pre_arcs[d] = {}
                    pre_arcsd = self.pre_arcs[d]
                    if arc not in pre_arcsd:
                        pre_arcsd[arc] = []
                    pre_arcsd[arc].append((head, pos))

    def generate1(self, root, feats):
        form = self.language.gen(root, feats)

    def add_variable(self, var):
        """Add variable to dictionary with its name as key."""
        self.varsD[var.name] = var
        
#    def remove_variable(self, var):
#        """Remove variable from dictionary."""
#        del self.varsD[var.name]

    def add_propagators(self):
        '''Create constraints based on principles.'''
        self.propagators = []
#        self.projectors = []
        # List of lists of expressions of different types
        # Constant Expressions, Variable Expressions, Complex Expressions
        self.expressions = [{}, {}, {}]
        for dim in self.dims.keys():
            not_apply = []
            for princ in dim.principles:
#                weight = self.weaken_princ(princ, weaken)
#                if weight != 1:
#                    print('  Weakening', princ)
                if princ.applies:
                    princ.make_constraints()
                else:
                    not_apply.append(princ)
            if not_apply:
                if self.report:
                    print("Principles not applying: {}".format(not_apply))
##        if self.project:
##            # Create compound projectors
##            for v in self.dstore.undetermined:
##                projs = v.projectors
##                if isinstance(v, IVar):
##                    cproj = []
##                    for p in projs:
##                        if p.recursive:
##                            self.projectors.append(p)
##                        else:
##                            cproj.append(p)
##                    cp = CompIntProj(v, [pj.right for pj in cproj])
###[p.right for p in projs],
###                                     recursive=any([p.recursive for p in projs]))
##                    if cp.right:
##                        v.comp_proj = cp
##                        self.projectors.append(cp)
##                else:
##                    for index, cls in enumerate([CompLowerProj, CompUpperProj, CompLCardProj, CompUCardProj]):
##                        subprojs = projs[index]
##                        if subprojs:
##                            csub = []
##                            for p in subprojs:
##                                if p.recursive:
##                                    self.projectors.append(p)
##                                else:
##                                    csub.append(p)
##                            cp = cls(v, [pj.right for pj in csub])
### [p.right for p in subprojs])
###                                     recursive=any([p.recursive for p in subprojs]))
##                            if cp.right:
##                                v.comp_proj[index] = cp
##                                self.projectors.append(cp)

    def add_derived_propagator(self, constraint, verbosity=0):
        """Constraint is a derived constraint; extend propagators list with
        basic constraints that are in its constraints attribute."""
##        if self.project:
##            projs = constraint.get_projectors()
##            self.projectors.extend(projs)
        for constr in constraint.constraints:
            self.add_propagator(constr, derived=True, verbosity=verbosity)

    def add_propagator(self, constraint, derived=False, verbosity=0):
        """Constraint is a basic propagator."""
        if verbosity > 1:
            print('Adding propagator {}'.format(constraint))
        self.propsD[constraint.name] = constraint
        self.propagators.append(constraint)
##        if not derived and self.project:
##            projs = constraint.get_projectors()
##            self.projectors.extend(projs)

    def make_nodes(self, trace=-1):
        """If trace is non-negative, trace that node when it is created."""
        self.nodes = [Node(name, form, self.lexicon, self, self.dstore,
                           index=i, process=self.process,
                           dims=self.dim_objs, agree=self.agree_dims, analyses=anal,
                           verbosity=2 if trace==i else self.verbosity,
                           # EOS node is treated specially
                           eos=(i == len(self.sentence) - 1)) \
                      for i, (name, form, anal) in enumerate(zip(self.sentence, self.proc_sentence, self.analysis))]
                      
    def make_empty_nodes(self, verbosity=0):
        '''Create empty nodes for all nodes whose entries have empty daughter entries.'''
        self.empty_nodes = []
        index = len(self.nodes)
        for node in self.nodes:
            # Keep track of complex empty nodes so we don't create extra ones for the same node
            cn_xlexes = []
            mother_node_index = node.index
            # For each empty entry, create only one empty node for each mother node, but
            # keep track of the mother entries in a dict
            for mother_entry_index, mother_entry in enumerate(node.entries):
#                print('Node {}, mother entry {} index {}'.format(node, mother_entry, mother_entry_index))
                # Create simple empty nodes
                for empty_entry in mother_entry.empty_daughs:
                    if empty_entry in node.empty_nodes:
                        node.empty_nodes[empty_entry].append(mother_entry_index)
                    else:
#                        if verbosity:
                        empty_node = self.make_empty_node(self.dim_objs, empty_entry, mother_entry,
                                                          index, mother_node_index)
                        index += 1
                        self.empty_nodes.append(empty_node)
                        node.empty_nodes[empty_entry] = [empty_node, mother_entry_index]
                # Create complex empty nodes
                complex_nodes = mother_entry.complex_empty_nodes
#                if complex_nodes:
#                    print('Complex nodes {}'.format(complex_nodes))
                for complex_node_xlex in complex_nodes:
                    # Check with complex crosslexes that are found are equivalent
                    # to ones already found
#                    print('Cn xlexes for {}: {}'.format(node, cn_xlexes))
                    if any([complex_node_xlex.equiv(x) for x in cn_xlexes]):
#                        print('Already created equivalent empty node')
                        continue
#                    print('Found complex node xlex', complex_node_xlex)
                    cn_xlexes.append(complex_node_xlex)
                    # First check to see if any conditions on the empty node are met
                    empty_cond = complex_node_xlex.empty_cond
                    if empty_cond:
                        cond_feat, cond_value = empty_cond
                        cond_dim = self.language.surface_dim
#                        print('{} has condition {} on {}'.format(complex_node_xlex, empty_cond, cond_dim))
                        entry_dim = mother_entry.dims.get(cond_dim)
                        entry_value = entry_dim.attribs.get('agrs', {}).get(cond_feat, set())
#                        print('entry value {}, cond value {}'.format(entry_value, cond_value))
                        if cond_value not in entry_value:
                            print("Empty node condition {} on entry {} not satisfied".format(empty_cond, mother_entry))
                            continue
                    if isinstance(complex_node_xlex, RevEmptyCrosslex):
                        empty_entry = complex_node_xlex.targ_lex
                        # This is a list of entries
                        targ_entry = complex_node_xlex.insert_lex
                        rel = complex_node_xlex.rel # ['daughter']
                        rev = True
#                        src_language = complex_node_xlex.source_lang
#                        targ_language = empty_entry[0].language
#                        print('Rev empty node: src lang {}, targ/ins lang {}'.format(src_language, targ_language))
#                        if not empty_entry:
#                            empty_entry = targ_language.lexicon[complex_node_xlex.targ_lex_key]
#                        print('   insert entry {}, empty {}'.format(ins_entry, empty_entry))
                    else:
                        empty_entry = complex_node_xlex.empty_lex
                        targ_entry = complex_node_xlex.targ_lex
                        rel = complex_node_xlex.rel
                        rev = False
#                    print('Complex xlex, mother {} targ {}, emp {}, rel {}'.format(mother_entry, targ_entry, empty_entry, rel))
                    targ_entries = targ_entry if isinstance(targ_entry, list) else [targ_entry]
                    targ_lexicon = targ_entries[0].lexicon
                    if_dim = complex_node_xlex.if_dim
#                    print('Complex xlex {}, targ entries {}, empty entry {}, if dim {}'.format(complex_node_xlex,
#                                                                                               targ_entries, empty_entry, if_dim))
#                    if verbosity > 0:
#                    print('Creating complex empty node for', complex_node_xlex,
#                          'trigger', mother_entry, 'empty entry', empty_entry, 'targ entries', targ_entries)
                    empty_node = self.make_complex_empty_node(self.dim_objs,
                                                              mother_entry, mother_entry_index, mother_node_index,
                                                              empty_entry,
                                                              targ_entries=targ_entries,
                                                              targ_lexicon=targ_lexicon,
                                                              index=index, rel=rel, rev=rev, if_dim=if_dim)
                    index += 1
                    self.empty_nodes.append(empty_node)

    def make_empty_node(self, dims, daughter_entry, mother_entry, index, src_node_index):
        '''Create an empty node with daughter_entry as only entry.'''
        return EmptyNode(self.lexicon, self, self.dstore, daughter_entry, mother_entry,
                         src_node_index,
                         index=index, dims=dims, verbosity=self.verbosity)

    def make_complex_empty_node(self, dims,
                                trigger_entry, trigger_entry_index, trigger_node_index, 
                                empty_entry,
                                targ_entries=None,
                                targ_lexicon=None,
                                index=0, rel=None, rev=False, if_dim=None):
        '''Create a complex empty node with empty_entry and targ_entry as entries
        and rel a constraint on the relationship to trigger_entry.'''
        return ComplexEmptyNode(self.lexicon, self, self.dstore, empty_entry,
                                trigger_entry, trigger_entry_index, trigger_node_index, 
                                targ_entries=targ_entries,
                                targ_lexicon=targ_lexicon, rel=rel,
                                index=index, dims=dims, rev=rev,
                                if_dim=if_dim, verbosity=self.verbosity)

    def get_nodes(self, eos=True, empty=True):
        '''Return sentence nodes, including EOS if eos and empty nodes if empty.'''
        nodes = self.nodes
        if not eos:
            nodes = nodes[:-1]
        if empty:
            nodes = nodes + self.empty_nodes
        return nodes

### Disambiguation

    def make_disambigs(self):
        """Create dict of disambiguators."""
        d_dict = {}
        for dim in self.dims:
            if dim.arc:
                disambigs = []
                # For now only create disambiguators for arc dimensions
                for node in self.get_nodes():
                    if len(node.entries) > 1:
                        d_out = ArcExcludeDisambig(self, node, dim, True)
                        d_in = ArcExcludeDisambig(self, node, dim, False)
                        disambigs.extend([d_out, d_in])
                d_dict[dim] = disambigs
        return d_dict

    def disambiguate(self, verbosity=0):
        """Update scores for each node's entries on a given dimension."""
        # Create disambiguators and disambig dict
        if self.report:
            print('Creating disambiguators')
        disambigs = self.make_disambigs()
        change = True
        it = 0
        if self.report:
            print('Running disambiguators')
        while change:
            if verbosity:
                print('Running disambiguators: iteration {}'.format(it))
            change = False
            for dim in self.dims:
                if dim in disambigs:
                    for disambig in disambigs[dim]:
                        change = disambig.update(verbosity=verbosity) or change
            it += 1
        if self.report:
            print('Ranking entries and finalizing nodes')
        for node in self.get_nodes():
            node.rank(verbosity=verbosity)
            node.finalize(verbosity=verbosity)

### Weaken principles

    def weaken_princ(self, princ, weaken=None):
        '''Whether principle princ is to be weakened, and if so, by how much(?).'''
        if weaken:
            # Weaken is a list of language abbrevs, principle classes, or constraints(?)
            for item in weaken:
                if isinstance(item, str):
                    # Assume item is a language abbrev;
                    # Weaken all principles whose dimensions include language
                    if princ.language.abbrev == item:
                        return 0
                    if isinstance(princ, IFPrinciple):
                        if princ.get_language1().abbrev == item or princ.get_language2().abbrev == item:
                            return 0
                elif inspect.isclass(item) and issubclass(item, Principle):
                    if isinstance(princ, item):
                        return 0
        return 1

### Variables and propagators

    def var(self, var_name):
        return self.varsD.get(var_name)
#        if variable:
#            dstores = variable.dstores
#            if dstore:
#                return dstores.get(dstore)
#            return dstores

    def prop(self, prop_name):
        return self.propsD.get(prop_name)

    def exam_prop(self, prop_name, dstore=None):
        p = self.prop(prop_name)
        if p:
            for v in p.variables:
                v.pprint(dstore=dstore)

    def exam_var(self, var_name, dstore=None):
        '''Examine one of the problem's variables.'''
        v = self.var(var_name)
        if v:
            if dstore:
                v.pprint(dstore)
            else:
                print(v, v.dstores)

### Solving

    def solve(self, tracevar=None, 
              # Different kinds of verbosity
              verbose=True, prop_verbosity=0, dist_verbosity=0, morf_verbosity=0, 
              search_algo=search.SmartSearch(),
              all_sols=True, timeit=False,
              save=True):
        '''Instantiate Solver with self as its problem; return multigraphs as
        solutions, one at a time.'''

        # Principles have to have been instantiated, and the propagators need
        # to have been created
        
        # Get the tracevars in case we're given only their names
        if tracevar:
            if not isinstance(tracevar, list):
                tracevar = [tracevar]
            for index, v in enumerate(tracevar):
                if isinstance(v, str):
                    tracevar[index] = self.varsD.get(v)
        else:
            tracevar = []

        multigraphs = []

        proceed = True
        solver = Solver(self, search_algo)

        # Find all solutions
        if all_sols:
            if self.report:
                print("Finding all solutions")
            solutions = solver.run(test_verbosity=prop_verbosity or verbose,
                                   expand_verbosity=dist_verbosity or verbose, 
                                   tracevar=tracevar, timeit=timeit)
            return [Multigraph(self, self.arc_dims, self.if_dims, solution.state.dstore,
                               morf_verbosity=morf_verbosity) \
                        for solution in solutions]

        # Generate individual solutions
        sol_gen = solver.make_gen(test_verbosity=prop_verbosity or verbose,
                                  expand_verbosity=dist_verbosity or verbose, 
                                  tracevar=tracevar)
        try:
            while proceed:
                solution = sol_gen.__next__()
                multigraph = Multigraph(self, self.arc_dims, self.if_dims, solution.state.dstore,
                                        morf_verbosity=morf_verbosity)
                if self.report:
                    print('FOUND SOLUTION', multigraph)
                multigraphs.append(multigraph)
                if not input('\nSEARCH FOR ANOTHER SOLUTION? [yes/NO] '):
                    proceed = False
        except StopIteration:
            if self:
                print('No more solutions')

        return multigraphs
        
    def diff_sols(self, sol_list, maximum=10):
        """Return a list of variables that differ in pairs of solutions from
        those in sol_list. Makes no more than maximum comparisons.
        A solution is either a domain store (DStore), a computation space (CSpace),
        or a multigraph."""
        # First copy sol_list because we're going to mutate it
        sol_list_copy = sol_list[:]
        # Get the DStores of the solutions if they're not already DStores
        for i, s in enumerate(sol_list):
            if not isinstance(s, DStore):
                sol_list_copy[i] = s.dstore
        n = 0
        for sol1, sol2 in itertools.combinations(sol_list_copy, 2):
            if n > maximum:
                return
            diffs = []
            for variable in self.varsD.values():
                val1 = variable.get_value(dstore=sol1)
                val2 = variable.get_value(dstore=sol2)
                if val1 != val2:
                    diffs.append([variable, val1, val2])
            print('{} ~ {}: {}'.format(sol1, sol2, diffs))
            n += 1

    def record_solution(self, solution):
        """Record various aspects of a solution (instance of Multigraph).
        """
        # Add 1 to the count for each solution's entry
        for entry in solution.entries.values():
            entry.count += 1
            if entry.names:
                # This is a multilingual entry
                entry.xcount += 1
                
        

