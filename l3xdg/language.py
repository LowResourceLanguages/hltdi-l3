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
# 2010.07.29 (MG)
#
# 2010.08.13 (MG)
# -- Agrs and agree features modified.
# 2010.08.15 (MG)
# -- Language keeps track of agreements features as
#    lexical entries are added: agrs features and values
#    and label/daughter feature combinations
# 2010.08.20 (MG)
# -- Reintroduced YAML representations and pickling.
#    Agreement feature values are not FeatStructs as before,
#    simplifying several things.
# 2010.08.21 (MG)
# -- Lexical attributes changed to 'attribs' dict within
#    LexDim.
# 2010.08.23 (MG)
# -- Language in separate module
# 2010.09.05 (MG)
# -- Languages now loaded once for multiple sentences.
# 2010.10.17 (MG)
# -- extract method replaces attribute (because lambda expressions
#    can't be pickled).
# -- End-of-sentence punctuation is automatically added to lexicon,
#    with ROOT as class (in set_lexicon).
# 2010.10.18 (MG)
# -- Language.anal() takes both raw words and pre-processed forms
#    so no longer does pre-preprocessing.
# 2010.10.19 (MG)
# -- Agr features to extract separated into own ('^') and daughter
#    features for each language: sublists in Language.extract_feats
# 2010.10.21 (MG)
# -- extract function is back (with the lambda expression)
#    record_agrs is now a separate function (recording feat-val
#    pairs from analyzed words in Language.agrs dict)
# 2010.10.24 (MG)
# -- Language directory names lowercase.
#    load() and get() are now static Language methods.
#    Languages, instead of lexicons, pickled (same filename).
# 2010.10.31
# -- Languages have a surface dimension where word forms appear or
#    or are generated for target languages in translation
# -- Generation FST gets loaded as inverted analysis FST when no
#    no generation FST is stored.
# -- Morphologically complex languages have a dict2fs function that
#    converts an agr dictionary to an FSSet for generation.
# -- Language.gen_word() takes a pos, root, and agr dictionary and
#    attempts to generate a word form, using the dict2fs function
#    for the language.
# 2010.11.29
# -- Language python files may contain multiple "grammars", instances
#    of Language with different dimensions, labels, and lexicon.
#    Each grammar gets its own pickle file.
# 2010.12.27
# -- Added language (SEMANTICS) for semantic dimensions.
# 2010.12.29
# -- Loading of morphology happens *after* pickling so the pickle
#    doesn't include the FSTs.
# 2011.01.29
# -- Semantics moved to its own directory like other languages.
#    water.yaml created for Semantics.
# 2011.01.31
# -- Crosslexes (see lex.py) are finalized (in XDG) after all languages and
#    lexicons have been finalized so that source entries point directly
#    to target entries (Language.finalize_crosslexes()).
# 2011.02.10
# -- Empty node names expanded to entries in set_lexicon
# 2011.02.13
# -- When language attribs are finalized, in the agrs dictionary of
#    possible values for agr features, specializations are eliminated.
# 2011.02.26
# -- Empty lexical entries (like @SB) no longer create crosslexes in the
#    other direction (from Semantics back to the language).
# 2011.03.02
# -- Finalization updated with the Crosslex class
# 2011.05.15
# -- Empty crosslexes handled.
# 2011.05.20
# -- Finalization of empty crosslexes causes creation of a simple crosslex
#    in the opposite direction, e.g., Sem->Qu for peripheral semantic roles
#    realized as case markers.
# 2011.08.25
# -- Language data text files (.lg), read in when language is created.
# 2011.09.04
# -- Language data files (.lg) replaced with grammar files (.gr), each
#    with a specific lexicon, set of dimensions and arc labels, morphology
#    POSs.
# 2011.09.05
# -- Grammar data files include morphological feature-value to syntactic
#    feature-value lists, replacing the extract function (that appears in
#    es.py, am.py, etc. for older languages).
# -- anal_from_dict() uses these lists to convert morphological to syntactic
#    analysis.
# 2011.09.06
# -- gen_from_dict() uses syn-to-morpho FV lists for generation (not tested
#    yet though)
# 2011.12.06
# -- RevEmptyCrosslexes
# 2012.03.24
# -- Flattened as well as hierarchical lexicons.
# 2012.05.14
# -- End-of-sentence characters handled explicitly in lexicons.
# 2012.08.13
# -- More options in parse(), allowing particular morphological features to
#    to prevent syntactic features from having values.
# 2012.08.26
# -- Fixed anal_from_dict so more than one value for a feature can match;
#    solves the problem of subjects that are -1 or +1 and otherwise undetermined
#    in the morphology.
# 2012.09.04
# -- Introduced language tokenization files and dictionaries.
# 2013.03.12
# -- Added default values to conversion from morphological to syntactic features
#    in anal_from_dict().
# 2013.04.05
# -- Languages have an agr_maps dict for mapping grammatical features between
#    languages; needed for IFAgreement principle.
# 2013.05.14
# -- Fixed anal_from_dict so it does the right thing: accumulates syntactic features
#    associated with *each* of the values of morphological features in the dict that
#    match the input (for example, for Guarani sj=[-1], second or third person).
# 2013.05.20
# -- For pairs of languages, agr_maps dict created in opposite direction from the one
#    specified in the grammar file
# 2013.07.31
# -- Languages have explicit feats list provided at instantiation. This is used to
#    create the agrs dict.
# 2013.09.04
# -- Segmentation during analysis works better: anal(), anal_from_dict(). Prefix and
#    suffix may be split off of the same word, and a new word from may be generated
#    that differs from the root.
#      ikuñanguérape -> i kuñanguéra pe
#      hetã -> i tetã
# 2013.09.15
# -- Affix-root combination works during post-processing: gen_word(), gen_from_dict().
#      a sus mujeres -> pe i kuña[+pl...] -> i kuñanguéra pe -> ikuñanguérape
#      su país -> i tetã -> hetã
# 2013.09.18
# -- Crosslex is not deleted if the target lex is not found. It's kept around as a
#    shell to be completed at translation time if the target lex has been created in
#    the meantime.

import os, re, importlib, sys

LANGUAGE_DIR = os.path.join(os.path.dirname(__file__), 'languages')

## Regexes for parsing language data
# Language name
LG_NAME_RE = re.compile(r'\s*n.*?:\s*(.*)')
# A set of arc labels
LABEL_RE = re.compile(r'\s*lab.*?:')
# A list of agreement feature names
FEATS_RE = re.compile(r'\s*feat.*?:\s*(.*)')
# A list of feature names to be hidden during display
HIDE_FEATS_RE = re.compile(r'\s*hide:\s*(.*)')
# agrmap: lang_abbrev
AGR_MAP_RE = re.compile(r'\s*agr.*:\s*(\w+)')
# feat>feat: featmap
AGR_MAP1_RE = re.compile(r'\s*(\w+)>(\w+)\s*:\s*(.+)')
# A dimension within a grammar
DIM_RE = re.compile(r'\s*d.*?:\s*(.*)')
# Backup language abbreviation
# l...: 
BACKUP_RE = re.compile(r'\s*lang.*?:\s*(.*)')
# Segments (characters)
# seg...: 
SEG_RE = re.compile(r'\s*seg.*?:\s*(.*)')
# Punctuation
# pun...: 
PUNC_RE = re.compile(r'\s*pun.*?:\s*(.*)')
# Term translations
# tr...:
TRANS_RE = re.compile(r'\s*tr.*?:\s*(.*)')
# Lexicon name
LEX_RE = re.compile(r'\s*lex.*?:\s*(.*)')
# Preprocessing function: module and function name
PREPROC_RE = re.compile(r"\s*prepr.*?:\s*(.*)\s+(.*)")
# Morphology data
MORPH_RE = re.compile(r'\s*mor.*?:\s*(.*)')
# POS within morphology
POS_RE = re.compile(r'\s*pos:\s*(.*)')
# Morphological analysis
ANAL_RE = re.compile(r'\s*an.*?:\s*')
# Morphological generation
GEN_RE = re.compile(r'\s*gen.*?:')
# Feature1 (values on succeeding lines) (morph for anal, syn for gen)
FEAT_RE = re.compile(r'\s*([^=;]+)\s*=')
# Arc specs for morphological generation
# <- arc_label node_name ; feat=value
# -> arc_label node_name ; feat=value
ARC_RE = re.compile(r"\s*((?:<-)|(?:->))\s*(\w+)\s*(\S+)\s*;\s*(.+)")
# Morph value -> syn FV (anal) or syn value -> morph FV (gen)
FV_RE = re.compile(r'\s*([^<>;]+)\s*;\s*([^;]+)')

## Regex for checking for non-ascii characters
ASCII_RE = re.compile(r'[a-zA-Z]')

from .lexicon import *
from .tdict import *
# FST stuff
from .morphology import *
# Morphology and POSMorphology classes
from .morphology import morphology
# Needed in gen_from_dict for unification of syntactic FSs
#from .lex import unify_fs
# Dimension abbreviations
from .utils import DIMENSIONS, ALL_DIMENSIONS
import pickle

class Language:

    LANGUAGES = {}

    T = TDict()

    def __init__(self, name, abbrev, backup='',
                 lexicon=None, labels=None, lexicon_name='',
                 # list of agreement features
                 feats=None,
                 hide_feats=None,
                 agrs=None,
                 agree_triples=None,
                 #                 dagree_tuples=None,
                 govern_triples=None, crossgovern_triples=None,
                 ifagree_pairs=None, 
                 morph_processing=True,
                 eos_chars=['.', '?', '!'],
                 dimensions=None,
                 extract=None, dict2fs=None, preproc=None, postproc=None,
                 seg_units=None):
                 #        print('Creating language {} with agrs {}'.format(name, agrs))
        ## Names
        self.name = name
        self.abbrev = abbrev
        ## End-of-sentence characters
        self.eos_chars = eos_chars
        self.dflt_eos = self.eos_chars[0]
        ## Arc labels for each dimension
        self.labels = labels or {}
        self.lexicon_name = lexicon_name

        ## Dimensions: normally get them from the labels dict
        self.set_dims(dimensions)

        ## The single lexicon
        self.lexicon = lexicon
#        self.flat_lexicon = None
        # List of languages whose lexicons have been cross-finalized with this
        # language's lexicon.
        self.linked_languages = []
 
        ## Caching for words generated by morphology.
        self.generated_words = {}

        ## Agreement features (should these be specific to dimensions?)
        # Extract once all values have been recorded, if not specified initially
        self.feats = feats or []
        self.hide_feats = hide_feats or []
        # dict of agr features and sets of possible values
        if agrs:
            self.agrs = agrs
        elif feats:
            self.agrs = dict([(f, set()) for f in feats])
        else:
            self.agrs = {}
#        self.agrs = agrs or {}
        # sets of possible triples of strings
        self.agree_triples = agree_triples or []
        #        self.dagree_tuples = dagree_tuples or []
        self.ifagree_pairs = ifagree_pairs or []
        self.govern_triples = govern_triples or []
        self.crossgovern_triples = crossgovern_triples or []
        # list of possible label/daughter feature pairs appearing in agree features
        self.labeldfeats = []
        # list of possible label/daughter feature pairs appearing in govern features
        self.govlabeldfeats = []
        # list of possible label/daughter feature pairs appearing in cross govern features
        self.crossgovlabeldfeats = []
        self.agree = []
        #        self.dagree = []
        self.govern = []
        self.crossgovern = []
        # Values for other attributes to be recorded as lexical entries are added
        self.lex_attribs = {}
        # Dictionary mapping features of this language to other languages:
        # {lang: {(feat, feat): {val: [vals], ...}, ...}, ...}
        self.agr_maps = {}

        ## Morphological pre-/post-processing
        self.morphology = None
        self.morph_processing = morph_processing
        self.morphology_loaded = False
        self.seg_units = seg_units or []
        # Caches for storing morphologically analyzed words, generated forms,
        # and segmentations
        if morph_processing:
            self.morph_anal_cache = {}
            self.morph_gen_cache = {}
            self.morph_seg_cache = {}
        else:
            self.morph_anal_cache = None
            self.morph_gen_cache = None
            self.morph_seg_cache = None

        ## Tokenization dictionary
        self.tokenization = None

        ## Functions for converting between morphological and syntactic features.
        ## Replaced for newer languages with POS-specific dicts for analysis and generation.
        # Analysis: morpho -> syn
        self.extract = extract
        # Generation: syn -> morpho
        self.dict2fs = dict2fs

        ## Orthographic or phonetic pre-/post-processing (for example,
        ## for Amharic and Tigrinya). Correction of orthography for Guarani.
        self.preproc = preproc
        self.postproc = postproc

        ## Translation languages
        self.backup = backup
        self.tlanguages = [abbrev]
        if self.backup:
            self.tlanguages.append(self.backup)

        ## Whether the language data and morphology have been loaded
        self.load_attempted = False

        ## Whether the language has been pickled.
        self.pickled = False

    def __repr__(self):
        return '{}'.format(self.name)

    def get_dir(self):
        """Where data for this language is kept."""
        return os.path.join(LANGUAGE_DIR, self.abbrev)

    def get_gram_file(self, grammar=''):
        """Data file for language."""
        name = grammar or self.abbrev
        return os.path.join(self.get_dir(), name + '.gr')

    def get_tok_file(self, grammar=''):
        """Data file for tokenization."""
        name = grammar or self.abbrev
        return os.path.join(self.get_dir(), name + '.tok')

    @staticmethod
    def make(name, abbrev, load_morph=False,
             grammar='',
             analysis=True, generation=True,
             learn=True,
             verbose=False):
        """Create a language using data in the language data file.
        If learn, load guesser analyzers."""
        lang = Language(name, abbrev=abbrev)
        # Load data from language file
        lang.load_data(load_morph=load_morph,
                       analysis=analysis, generation=generation, learn=learn,
                       grammar=grammar,
                       verbose=verbose)
        return lang

    def load_data(self, load_morph=False,
                  grammar='',
                  analysis=True, generation=True, learn=False,
                  verbose=False):
        """Read in data on language from text file."""
        if self.load_attempted:
            return
        self.load_attempted = True
        # First try to morphological and syntactic data
        filename = self.get_gram_file(grammar=grammar)
        if not os.path.exists(filename):
            print(Language.T.tformat('No language data file for {}', [self], self.tlanguages))
        else:
            if verbose:
                print(Language.T.tformat('Loading language data from {}', [filename], self.tlanguages))
            with open(filename, encoding='utf-8') as stream:
                data = stream.read()
                self.parse(data, verbose=verbose)
            if load_morph:
                # If learn, load guesser FSTs so we can check whether unknown words satisfy
                # certain conditions
                self.load_morpho(guess=learn, analysis=analysis, generation=generation,
                                 verbose=verbose)
        # Then try to load tokenization data
        tok_filename = self.get_tok_file(grammar=grammar)
        if not os.path.exists(tok_filename):
            if verbose:
                print(Language.T.tformat('No tokenization file for {}', [self], self.tlanguages))
            return
        if verbose:
            print(Language.T.tformat('Loading tokenization data from {}', [tok_filename], self.tlanguages))
        with open(tok_filename, encoding='utf-8') as stream:
            data = stream.read()
            if verbose:
                print(Language.T.tformat("Parsing tokenization data for {}", [self], self.tlanguages))
            self.parse_tok(data, verbose=verbose)
        
        # Create a default FS for each POS
#        for posmorph in self.morphology.values():
#            if not posmorph.defaultFS:
#                posmorph.defaultFS = posmorph.make_default_fs()

    def parse_tok(self, data, verbose=False):
        """Parse data from a tokenization file (*.tok).
        word
        token
        token
        [blank line]
        """

        lines = data.split('\n')[::-1]

        self.tokenization = {}

        # Current word
        word = ''
        # Current tokens
        tokens = []
        # Current lex indices
        indices = []
        # Current arcs
        arcs = []

        while lines:

            line = lines.pop().split('#')[0].strip() # strip comments

            # Empty lines separate tokenization entries
            if not line:
                if word:
                    # Complete the last entry
                    self.tokenization[word] = tokens, indices, arcs
#                if verbose:
#                    print('Added {}: {}/{}/{} to language'.format(word, tokens, indices, arcs))
                # Reset word, tokens, and indices
                word = ''
                tokens = []
                indices = []
                arcs = []

            elif not word:
                # This line represents the word
                word = line

            else:
                # This line is a token and associated properties:
                #  lex index, dim and arc labels (or -> if this is the head)
                #  token
                #  token lex int
                #  token lex int dim arc-label
                #  token lex int dim arc-label dim arc-label
                #  token dim arc-label
                arc = {}
                index = None
                line = line.partition(' ')
                if line[2]:
                    # There are properties
                    props = line[2].split()
                    for prop, value in zip(props[::2], props[1::2]):
                        if prop == 'lex':
                            # This is a lex index, convert the value to an int and store
                            # it
                            index = int(value)
                        else:
                            # Prop must be the name of a dimension
                            # append the language abbreviation to the front of it
                            dim = self.abbrev + "-" + prop
                            arc[dim] = value
                tokens.append(line[0])
                indices.append(index)
                arcs.append(arc)

        # Complete the final entry
        if word:
            self.tokenization[word] = tokens, indices, arcs
#            if verbose:
#                print('Added {}: {}/{}/{} to language'.format(word, tokens, indices, arcs))
            
    def set_dims(self, dimensions=None):
        """Assign dimensions in different categories."""
        self.dimensions = dimensions or list(self.labels.keys()) or []
        # The dimension that's closest to the surface, normally ID
        self.surface_dim = self.get_surface_dim()
        # The dimension responsible for word order, normally LP
        self.order_dim = self.get_order_dim()

    def parse(self, data, verbose=False):

        """Parse data from a language data file (*.gr)."""
#        if verbose:
#            print('Parsing language data for', self)

        lines = data.split('\n')[::-1]

        seg = []
        punc = []

        labels = {}

        chars = ''

        # POS for morphology
        pos = []
        # Processing direction for morphology features
        proc = ''

        # Agr maps
        agrmap_lang = ''

        current = None
        current_dim = ''
        current_feat = ''
        current_pos = ''

        morph_dict = {}

        while lines:

            line = lines.pop().split('#')[0].strip() # strip comments

            # Ignore empty lines
            if not line: continue
            
            # Name of the lexicon
            m = LEX_RE.match(line)
            if m:
                self.lexicon_name = m.group(1)
                continue

            # Preprocessing function
            m = PREPROC_RE.match(line)
            if m:
                # Find the preprocessing function in the given module
                # (This assumes the file exists)
                module_name = m.group(1)
                function_name = m.group(2)
#                print("Preprocessing function {} in module {}".format(function_name, module_name))
                package = "l3xdg.languages." + self.abbrev + '.' + module_name
#                print("Package: {}".format(package))
                module = importlib.import_module(package)
                function = getattr(module, function_name)
#                print("Function {}".format(function))
                self.preproc = function
                continue

            # Arc labels
            m = LABEL_RE.match(line)
            if m:
                current = 'labels'
                labels = {}
                continue

            m = AGR_MAP_RE.match(line)
            if m:
                agrmap_lang = m.group(1)
                current = 'agrmap'
                self.agr_maps[agrmap_lang] = {}
                continue

            m = AGR_MAP1_RE.match(line)
            if m:
                src_feat, targ_feat = m.group(1), m.group(2)
                feat_tup = (src_feat, targ_feat)
                map = m.group(3)
                maps = map.split(';')
                map_dict = {}
                for map in maps:
                    s, ts = map.split('>')
                    s = tuple(eval(s))
                    s_list = []
                    for t in ts.split('|'):
                        t = tuple(eval(t))
#                        print(' Agr map {}: {}>{}'.format(feat_tup, s, t))
                        s_list.append(t)
                    map_dict[s] = tuple(s_list)
                self.agr_maps[agrmap_lang][feat_tup] = map_dict
                continue

            # A new dimension
            m = DIM_RE.match(line)
            if m:
                current = 'dim'
                current_dim = m.group(1)
                continue

            # Morphology follows
            m = MORPH_RE.match(line)
            if m:
                current = 'morph'
                continue

            # A new morphology part-of-speech
            m = POS_RE.match(line)
            if m:
                # current must be 'morph'
                p = m.group(1)
                pos.append(p)
                current_pos = p
                proc = ''
                morph_dict[p] = {}
                continue

            # Conversions for morphological analysis
            m = ANAL_RE.match(line)
            if m:
                proc = 'anal'
                morph_dict[current_pos][proc] = {}
                continue

            # Conversions for morphological generation
            m = GEN_RE.match(line)
            if m:
                proc = 'gen'
                morph_dict[current_pos][proc] = {}
                continue

            m = ARC_RE.match(line)
            if m:
                dir, arc, mother, fv = m.group(1), m.group(2), m.group(3), m.group(4)
                feat, value = fv.split('=')
                feat = feat.strip()
                value = value.strip()
                if value.isdigit():
                    value = int(value)
#                print("{}arc: arc {}, mother {}, feat {}, value {}".format(dir, arc, mother, feat, value))
                dct = morph_dict[current_pos]['gen']
                if dir not in dct:
                    dct[dir] = {}
                if arc not in dct[dir]:
                    dct[dir][arc] = {}
                dct[dir][arc][mother] = (feat, value)
                continue

            # Morphological feature, e.g., sj=
            m = FEAT_RE.match(line)
            if m and current == 'morph':
                current_feat = m.group(1).strip()
                if current_feat not in morph_dict[current_pos][proc]:
                    morph_dict[current_pos][proc][current_feat] = []
                continue

            # Morphological feature-value conversion:
            # E.g., for anal
            #         presperf;   tmp=[0]
            # for gen
            #         [0];      tmp=presperf
            m = FV_RE.match(line)
            if m:
                val1, f2 = m.groups()
                # Convert val1 to proper form
                val1 = val1.strip()
                # val1 could be '!', which means assign no value to current
                # feat if feat2 has value val2
                if '[' in val1:
                    if proc == 'anal':
                        val1 = fs.FeatStruct(val1)
                    else:
                        val1 = {tuple(eval(val1))}
                elif proc == 'anal':
                    if val1 in {'False', 'True', 'None'}:
                        val1 = eval(val1)
                elif proc == 'gen':
                    val1 = {eval(val1)}
                # f2 could '!'
                if '!' in f2:
                    # If current feat has value val1, return no analysis
                    feat2 = '!'
                    val2 = None
                elif '_' in f2:
#                    print('f2 {}'.format(f2))
                    # One or more words (really detached affixes) to be inserted
                    # (could use regex for this)
                    feat2 = '^'
                    # Split f2 into portions responsible for each word
                    val2 = f2.split(',')
                    toks = []
                    indices = []
                    arcs = []
                    for val in val2:
#                        print('val {}'.format(val))
                        index = None
                        arc = {}
                        # Split each portion at spaces
                        val = val.strip().split()
                        # The token is the first thing
                        toks.append(val[0])
                        vals = val[1:]
#                        print(' vals {}'.format(vals))
                        for prop, v in zip(vals[::2], vals[1::2]):
                            if prop == 'lex':
                                index = int(v)
                            else:
                                # Must be a dimension name
                                dim = self.abbrev + "-" + prop
                                arc[dim] = v
                        arcs.append(arc)
                        indices.append(index)
                    val2 = [toks, indices, arcs]
#                    segs = [x[0] for x in val2]
#                    # Determine whether the affixes should precede or follow the stem
#                    # Split at position of stem
#                    val2 = f2.split('_')
#                    # Lists of prefixes and suffixes
#                    pre = val2[0].strip().split()
#                    post = val2[1].strip().split()
#                    val2 = [pre, post]
                else:
#                    print('f2 {}'.format(f2))
                    feat2, val2 = f2.split('=')
                    feat2 = feat2.strip()
                    val2 = val2.strip()
                    if '[' in val2:
                        if proc == 'gen' or val1 == '!':
                            val2 = fs.FeatStruct(val2)
                        else:
                            # It may be a single value, like [1,0,0], or a list of values, like [[0,0,0],[0,0,1]]
                            v = eval(val2)
                            if isinstance(v, list) and isinstance(v[0], list):
                                # If a list of values
                                val2 = {tuple(x) for x in v}
                            else:
                                val2 = {tuple(v)}
#                        val2 = {tuple(eval(val2))}
                    elif proc == 'anal':
                        val2 = eval(val2)
                        if val1 != '!':
                            val2 = {val2}
                    elif val2 in {'False', 'True', 'None'}:
                        val2 = eval(val2)
#                print('current pos {}, current feat {}, val1 {}, feat2 {}, val2 {}'.format(current_pos,
#                                                                                           current_feat,
#                                                                                            val1, feat2, val2))
                morph_dict[current_pos][proc][current_feat].append((val1, feat2, val2))
                continue

            # Beginning of segmentation units
            m = SEG_RE.match(line)
            if m:
                current = 'seg'
                seg = m.group(1).split()
                continue

            # Feature names
            m = FEATS_RE.match(line)
            if m:
                self.feats.extend(m.group(1).split())
                self.agrs.update(dict([(f, set()) for f in self.feats]))
                continue

            # Feature names to be hidden (also included in feature list)
            m = HIDE_FEATS_RE.match(line)
            if m:
                self.hide_feats.extend(m.group(1).split())
                continue

            m = LG_NAME_RE.match(line)
            if m:
                name = m.group(1).strip()
                self.name = name
                continue

            # Backup language
            m = BACKUP_RE.match(line)
            if m:
                lang = m.group(1).strip()
                self.backup = lang
                self.tlanguages.append(lang)
                continue

            m = PUNC_RE.match(line)
            if m:
                current = 'punc'
                punc = m.group(1).split()
                continue

            m = TRANS_RE.match(line)
            if m:
                current = 'trans'
                w_g = m.group(1).split()
                if '=' in w_g:
                    w, g = w_g.split('=')
                    # Add to the global TDict
                    Language.T.add(w.strip(), g.strip(), self.abbrev)

                continue

            ## Parse a line that doesn't match one of the regexs

            if current == 'seg':
                seg.extend(line.strip().split())

            elif current == 'punc':
                punc.extend(line.strip().split())

            elif current == 'trans':
                wd, gls = line.strip().split('=')
                # Add to the global TDict
                Language.T.add(wd.strip(), gls.strip(), self.abbrev)
            
            elif current == 'dim':
                dim_labels = line.strip().split()
                self.labels[current_dim] = dim_labels

            else:
                raise ValueError("bad line: {}".format(line))

        if punc:
            # Make punc list into a string
            punc = ''.join(punc)

        if seg:
            # Make a bracketed string of character ranges and other characters
            # to use for re
            chars = ''.join(set(''.join(seg)))
            chars = self.make_char_string(chars)
            # Make the seg_units list, [chars, char_dict], expected for transduction,
            # composition, etc.
            self.seg_units = self.make_seg_units(seg)

        if self.labels and not self.dimensions:
            # There is a dict of dimensions and arc labels; set the
            # dimensions for the grammar
            self.set_dims()

        if pos:
            # There is a list of POSs for a Morphology object
            m = morphology.Morphology(pos_morphs=pos)
            self.set_morphology(m)
            # Assign the anal and gen FV dicts for each POS
            for p, posmorph in m.items():
                pos_dicts = morph_dict.get(p, {})
                posmorph.anal_dict = pos_dicts.get('anal', {})
                posmorph.gen_dict = pos_dicts.get('gen', {})

    def make_char_string(self, chars):
        non_ascii = []
        for char in chars:
            if not ASCII_RE.match(char):
                non_ascii.append(char)
        non_ascii.sort()
        non_ascii_s = ''.join(non_ascii)
        return r'[a-zA-Z' + non_ascii_s + r']'

    def make_seg_units(self, segs):
        """Convert a list of segments to a seg_units list + dict."""
        singletons = []
        dct = {}
        for seg in segs:
            c0 = seg[0]
            if c0 in dct:
                dct[c0].append(seg)
            else:
                dct[c0] = [seg]
        for c0, segs in dct.items():
            if len(segs) == 1 and len(segs[0]) == 1:
                singletons.append(c0)
        for seg in singletons:
            del dct[seg]
        singletons.sort()
        return [singletons, dct]

    def is_eos(self, char):
        return char in self.eos_chars

    def get_dir(self):
        return os.path.join(LANGUAGE_DIR, self.abbrev)

    def get_POSs(self):
        morph = self.morphology
        if morph:
            return list(morph.keys())
        return []

    def make_dim_long(self, dim):
        '''Make a language-specific abbreviation for the dimension, unless it's semantics.
        If it's not a dimension, returning None.'''
        if dim in DIMENSIONS['semantics']:
            return dim
        elif dim in DIMENSIONS['arc'] or dim in DIMENSIONS['if']:
            return self.abbrev + '-' + dim
#        dims_short = {self.get_dim_short(dim): dim for dim in self.dimensions}
#        return dims_short.get(dim)

    def get_dim_short(self, dim):
        '''Get the dimension part of the dimension abbrev.'''
        return dim.split('-')[-1]

    def get_surface_dim(self):
        '''Find the dimension where output language words are generated.'''
        for dim in self.dimensions:
            if self.get_dim_short(dim) in DIMENSIONS['surface']:
                return dim
        return ''

    def get_order_dim(self):
        '''Find the dimension where output language words are generated.'''
        for dim in self.dimensions:
            if self.get_dim_short(dim) in DIMENSIONS['order']:
                return dim
        return ''
        
    def get_semif_dim(self):
        '''Find the interface dimension associating syntax with semantics.'''
        for dim in self.dimensions:
            if self.get_dim_short(dim) in DIMENSIONS['semif']:
                return dim
        return ''

    def get_language_dims(self, arc=True):
        '''Return the dimensions associated with only this language, only arc dimensions if arc is True.'''
        dims = ALL_DIMENSIONS - DIMENSIONS['semantics']
        if arc:
            dims = dims & DIMENSIONS['arc']
        return [dim for dim in self.dimensions if self.get_dim_short(dim) in dims]

    def get_cross_dim(self, target_abbrev):
        """Get the name of an interface dimension to the target language."""
        linked = self.linked_languages
        if target_abbrev in linked:
            dims = self.dimensions
            crossdims = DIMENSIONS['semif'] if target_abbrev == 'sem' else DIMENSIONS['crossif']
            for dim in dims:
                # delete the language prefix
                dim_name = dim.split('-')[-1]
                if dim_name in crossdims:
                    return dim
        return ''

    def set_lexicon(self, lexicon, finalize=False):
        """Assign this language's lexicon, saving dimensions.

        @param lexicon:  the language's lexicon
        @type  lexicon:  Lexicon
#        @param flat:     whether this is the flattened lexicon
#        @type  flat:     boolean
        """
        if lexicon:
#            if flat:
#                self.flat_lexicon = lexicon
#            else:
            self.lexicon = lexicon
            lexicon.language = self
            dims = set(self.dimensions)
            # Add entries for ROOT and end-of-sentence characters if they're not there
##            if not 'ROOT' in lexicon:
##                lexicon['ROOT'] = [Lex(word='ROOT',
##                                       dims={'syn': LexDim(outs={'root': '!', 'del': '*'},
##                                                           proj=['root']),
##                                             'sem': LexDim(outs={'root': '!', 'del': '*'})})]
##            for char in self.eos_chars:
##                if self.preproc:
##                    char = self.preproc(char)
##                if char not in lexicon:
##                    lexicon[char] = [Lex(word=char, classes=['ROOT'], lexicon=lexicon)]
            # Make this the language of each lexdim
            for key, lexs in lexicon.items():
                if not isinstance(lexs, list):
                    lexicon[key] = [lexs]
                    lexs = [lexs]
                for lex in lexs:
                    if not lex.lexicon:
                        lex.lexicon = lexicon
                    # Record stuff in crosslexes too
                    for xlexes in lex.crosslexes.values():
                        # Ignore the language abbreviation keys?
                        for xlex in xlexes:
                            if isinstance(xlex, EmptyCrosslex):
                                continue
                            target, lexdim = xlex.targ_lex, xlex.lexdim
                            if lexdim:
                                dims.add(lexdim.dim)
                                lexdim.record_agreement()
                                lexdim.record_attribs()
                    # Expand empty node classes if this hasn't happened already
#                    for i, cls in enumerate(lex.empty_daughs):
##                        print('Expanding empty classes for', lex, ':', i, cls)
#                        if isinstance(cls, str):
#                            lex.empty_daughs[i] = lexicon[cls][0]

                    # Record various stuff for each lex dim
                    for abbrev, dim in lex.dims.items():
                        dims.add(abbrev)
                        dim.language = self
                        dim.record_agreement()
                        dim.record_attribs()
            # Finalize groups
            for group in lexicon.groups:
                group.lexicon = self.lexicon
                group.language = self
            # Finalize lexclasses
            for cls in lexicon.classes.values():
                cls.lexicon = self.lexicon
                cls.language = self

            self.dimensions = list(dims)
            if finalize:
                self.finalize()
                # Do this here; otherwise it's done in finalize_crosslexes
                if not self.crossgovern:
                    self.crossgovern = [x for x in [self.crossgov_strings_to_ints(trip) for trip in self.crossgovern_triples] if x]

    def make_daughter_sets(self):
        """For each LexDim, find possible daughter labels."""
        for key, lexs in self.lexicon.items():
            for lex in lexs:
                lex.make_daughter_sets()
                #                for abbrev, lexdim in lex.dims.items():
                #                    labels = set()
                #                    # Check the possible daughter arcs for the lexdim
                #                    outs = lexdim.attribs.get('outs')
                #                    if outs:
                #                        for label, char in outs.items():
                #                            if char:
                #                                label_int = self.get_label_int(label, abbrev)
                #                                # Ignore labels with 0 as char
                #                                labels.add(label_int)
                #                        lexdim.attribs['daughs'] = labels

    def finalize(self):
        """Do these steps after lexical entries are added."""
#        print("Finalizing {}".format(self))
        # Gather possible daughter labels
        self.make_daughter_sets()
        # create an ordered list of features.
        if not self.feats:
            self.feats = list(self.agrs.keys())
        # create ordered lists of int (tuple) pairs for agree and govern
        if not self.agree:
            self.agree = [self.agree_strings_to_ints(trip) for trip in self.agree_triples]
            #        if not self.dagree:
            #            self.dagree = [self.dagree_strings_to_ints(tup) for tup in self.dagree_tuples]
        if not self.govern:
            # Make sure there aren't duplicates
            self.govern = [self.gov_strings_to_ints(trip) for trip in self.govern_triples]

    def finalize_agrmaps(self, languages):
        """Convert feature names (keys in agr map dicts) to integers, and store reversed agr maps
        for other linked languages."""
        # First convert agr features to integers
        for tlang, agr_maps in self.agr_maps.items():
            if tlang == self.abbrev:
                continue
            targ_lang = self.LANGUAGES[tlang]
            if targ_lang in languages:
                #                print('{} finalizing agrmaps for {}'.format(self, targ_lang))
                reverse_map = False
                if self.abbrev not in targ_lang.agr_maps:
                    reverse_map = True
                for (f1, f2), value_dict in list(agr_maps.items()):
                    if isinstance(f1, str):
                        agrints = self.get_feat_int(f1), targ_lang.get_feat_int(f2)
                        #                        print('tlang {}, feat names ({},{}), agrints {}, value dict {}'.format(tlang, f1, f2, agrints, value_dict))
                        agr_maps[agrints] = value_dict.copy()
                    #                    print('Agr map {} updated'.format(agr_maps))
                        if reverse_map:
                            #                            print('Reversing {} for target language {}'.format(value_dict, targ_lang))
                            targ_lang.reverse_agr_map(self, (f1, f2), value_dict)

    def instantiate_crosslexes(self):
        """Instantiate crosslexes from classinst lexical entries."""
    
    def finalize_crosslexes(self, flatten=False):
        """After all languages have been finalized, finalize crosslexes by finding entries in the
        target language and copying each crosslex in the opposite direction."""
#        print("Finalizing crosslexes from {} to other languages".format(self))
#        finalized_lex_ids = []
        for key, lexs in self.lexicon.items():
            for lex_index, lex in enumerate(lexs):
                if key != lex.name:
                    continue
#                if lex.id in finalized_lex_ids:
#                    # This can happen because the different keys can point to the same lex
#                    print('{} already finalized'.format(lex))
#                    continue
#                finalized_lex_ids.append(lex.id)
                for lang_abbrev, crosslexes in lex.crosslexes.items():
                    if lang_abbrev == self.abbrev:
                        print('Lex {} has crosslex to its own language'.format(lex))
                    # Look for the target language with the right lexicon, but don't load it if it's not loaded
                    target_lang = Language.get(lang_abbrev, load=False, grammar=self.lexicon_name)
                    if target_lang:
                        target_lexicon = target_lang.lexicon
                        agr_maps = self.agr_maps.get(lang_abbrev)
                        # Look for the lexical entries
                        for crosslex in crosslexes[:]:
                            crosslex.targ_lang = target_lang
                            xsource_lang_abbrev = crosslex.source_lang.abbrev
                            xtarg_lang_abbrev = crosslex.targ_lang_abbrev
#                            print('crosslex {}, targ lang {}, source lang {}'.format(crosslex, target_lang, xsource_lang_abbrev))
                            if self.abbrev != xsource_lang_abbrev and self.abbrev != xtarg_lang_abbrev:
                                # Don't understand how this can happen
                                crosslexes.remove(crosslex)
                                continue
                            # EmptyCrosslexes have a source lex as well as a target lex to be
                            # found.
                            # They also create a finalized (regular) crosslex in the other direction
                            xtarg_lang = crosslex.targ_lang
                            if not xtarg_lang:
                                # Assign the target language
                                xtarg_lang = Language.find(xtarg_lang_abbrev)
#                                print('Assigning target language {} to {}'.format(xtarg_lang, crosslex))
                                crosslex.targ_lang = xtarg_lang
                            if isinstance(crosslex, EmptyCrosslex) and not crosslex.empty_lex:
                                src_label = crosslex.empty_lex_key
                                src_index = crosslex.empty_lex_index
                                #                                print('Assigning cross lex source {} to lexicon {}'.format(src_label, self.lexicon))
                                src_entry = self.lexicon[src_label][src_index]
#                                print("Setting empty lex to {}".format(src_entry))
                                crosslex.empty_lex = src_entry
                            if isinstance(crosslex, RevEmptyCrosslex):
                                if not crosslex.insert_lex:
                                    insert_label = crosslex.insert_lex_key
                                    if insert_label not in self.lexicon:
#                                        target_lexicon:
                                        print('insert label {} is not in lexicon {}'.format(insert_label, self.lexicon))
                                        # We can't create an empty node for a lexical entry that does
                                        # not exist, so delete this entry.
                                        #                                        print('Deleting revemptyxlex {} from {} crosslexes {}'.format(crosslex, lex, crosslexes))
                                        for rx in crosslexes:
                                            if rx.equiv(crosslex):
                                                crosslexes.remove(rx)
                                                break
#                                        crosslexes.remove(crosslex)
                                    else:
                                        insert_index = crosslex.insert_lex_index
                                        # insert_lex can be a list of lexes
                                        if insert_index is None:
#                                            print('{} inserting crosslex entry: {}, {}, {}'.format(lex, self, crosslex, insert_index))
                                            crosslex.insert_lex = self.lexicon[insert_label]
                                        else:
                                            crosslex.insert_lex = self.lexicon[insert_label][insert_index]
                                            #                                        print('Assigning crosslex insertion lex {} to lexicon {}'.format(insert_label, self.lexicon))
                                        empty_lex = crosslex.targ_lex
                                        if not empty_lex:
                                            empty_language = xtarg_lang
                                            empty_key = crosslex.targ_lex_key
                                            crosslex.targ_lex = empty_language.lexicon[empty_key][0]
                                            print('Assigning empty lex {} to {} in lexicon {}'.format(crosslex.targ_lex,
                                                                                                      crosslex, empty_language.lexicon))
                            if not crosslex.targ_lex:
#                                print('No targ lex for {}'.format(crosslex))
                                targ_label = crosslex.targ_lex_key
                                # The target lexical entry may have a POS or agr feature value specified
                                spec = None
                                if ':' in targ_label:
                                    targ_label, spec = targ_label.split(':')
#                                    print('targ label {}, spec {}'.format(targ_label, spec))
                                index = crosslex.targ_lex_index
                                lexdim = crosslex.lexdim
                                if lexdim:
                                    attribs = lexdim.attribs
                                    if 'crossgov' in attribs:
                                        for lab2, (attr, val) in attribs['crossgov'].items():
                                            self.crossgovern_triples.append((lab2, attr, val))
                                            self.crossgovlabeldfeats.append((lab2, attr))
#                                    if 'agree' in attribs:
#                                        print('Copy lexdim with agree {} to {}'.format(attribs['agree'], target_entry))
                                # Get the target entries, using the spec if there is one
                                target_entries = target_lexicon.get_by_spec(targ_label, spec)
                                if target_entries:
                                    if len(target_entries) == 1:
                                        target_entry = target_entries[0]
                                        crosslex.targ_lex = target_entry
                                        if crosslex.bidir:
                                            target_entry.add_finalized_crosslex(self.abbrev, lex, lexdim,
                                                                                targ_lex_index=lex_index, count=crosslex.count)
                                    elif index >= 0 and len(target_entries) > index:
                                        target_entry = target_entries[index]
                                        # Set target entry
                                        crosslex.targ_lex = target_entry
                                        if crosslex.bidir:
                                            target_entry.add_finalized_crosslex(self.abbrev, lex, lexdim,
                                                                                targ_lex_index=lex_index, count=crosslex.count)
                                    else:
                                        crosslex.targ_lex = target_entries
                                        # Add crosslex in other direction if bidir is True
                                        if crosslex.bidir:
                                            for targ_entry in target_entries:
                                                target_entry.add_finalized_crosslex(self.abbrev, lex, lexdim,
                                                                                    targ_lex_index=lex_index, count=crosslex.count)
#                                elif flatten:
#                                    # This is an abstract, higher-level crosslex (like N->THING) which is irrelevant for
#                                    # flattened nodes, so just remove it.
#                                    crosslexes.remove(crosslex)
                                else:
                                    print('Warning: {} finalizing crosslexes for {}; target entry for {} not found'.format(self, lex, crosslex))
                            if crosslex.targdim:
#                                print('Crosslex {} has targdim {}; targ lex {}'.format(crosslex, crosslex.targdim, crosslex.targ_lex))
                                targdim = crosslex.targ_lex.dims.get(crosslex.targdim.dim)
                                if targdim:
#                                    print('Merging {} with {}'.format(targdim, crosslex.targdim))
                                    targdim.merge_attribs(crosslex.targdim, lexical=True)
                            if isinstance(crosslex, EmptyCrosslex):
                                # Automatically create the crosslex in the other direction; from the language
                                # with the explicit node to the language with the empty node
#                                print('Finalizing empty crosslex, targ {}, emp {}'.format(crosslex.targ_lex, crosslex.empty_lex))
                                src_entry = crosslex.targ_lex
                                targ_entry = crosslex.empty_lex
                                lexdim = None
                                # Get the dimension from the list of dimensions (rather than from the Crosslex).
                                dim = self.get_cross_dim(xtarg_lang_abbrev)
#                                dim = crosslex.rel[1]
                                arg2 = crosslex.rel[1]
                                arg1 = crosslex.rel[2]
#                                print('arg1 {}'.format(arg1))
                                if isinstance(arg1, list):
                                    arg1 = tuple(arg1)
                                else:
                                    arg1 = (arg1,)
#                                print('arg1 {}'.format(arg1))
                                attribs = {'arg': {arg2: arg1}}
#                                print('crosslex {} attribs {} dim {}'.format(crosslex, attribs, dim))
                                agrs = crosslex.agrs
                                govfeat = None
                                if agrs:
                                    # Govfeat looks like this
                                    # {feat: {(value)}, feat: ...}
                                    # so has to be changed for the crossgov attribute
                                    govfeat = list(agrs[1].items())[0]
                                    govfeat = (govfeat[0], list(govfeat[1])[0])
                                    attribs['crossgov'] = {arg2: govfeat}
                                lexdim = LexDim(language=self, lex=targ_entry, dim=dim, attribs=attribs)
#                                print('New empty lexdim {}'.format(lexdim))
                                # Record the (possibly) new features and values in the target language
                                lexdim.record_attrib('arg', arg1)
                                if agrs:
                                    lexdim.record_attrib('crossgovern', govfeat)
                                    lg_govern = self.crossgovern_triples
                                    lg_gov_lab_dfeats = self.crossgovlabeldfeats
                                    lg_agrs = self.agrs
                                    if (arg2, govfeat[0], govfeat[1]) not in lg_govern:
                                        lg_govern.append((arg2, govfeat[0], govfeat[1]))
                                    if (arg2, govfeat[0]) not in lg_gov_lab_dfeats:
                                        lg_gov_lab_dfeats.append((arg2, govfeat[0]))
                                    lg_agrs[govfeat[0]] = lg_agrs.get(govfeat[0], set()).union({govfeat[1]})
                                if not flatten:
                                    if isinstance(src_entry, list):
                                        for s in src_entry:
                                            s.add_finalized_crosslex(self.abbrev, targ_entry, lexdim=lexdim,
                                                                     count=crosslex.count)
                                    else:
                                        src_entry.add_finalized_crosslex(self.abbrev, targ_entry, lexdim=lexdim,
                                                                 count=crosslex.count)

        if not self.crossgovern:
            self.crossgovern = [x for x in [self.crossgov_strings_to_ints(trip) for trip in self.crossgovern_triples] if x]
            
        for name, lexcls in self.lexicon.classes.items():
            # Check to see whether attribs in cross languages have been recorded
            for finalized, lg_entry in zip(lexcls.finalized, lexcls.entries):
                if not finalized:
                    lg, entry = lg_entry
                    cross = entry.get('cross')
                    if cross:
                        for cross_lg, attribs in cross:
                            cross_language = self.LANGUAGES.get(cross_lg)
                            target_dims = attribs.get('target_dim')
                            if target_dims:
                                for dim, dim_attribs in target_dims:
                                    lexcls.record_attribs(dim_attribs, cross_language)

    def reverse_agr_map(self, lang2, feats, fmap):
        '''Reverse the agr map for lang2 and feat1 feat2, and assign it to this language.'''
        feat2, feat1 = feats
        abbrev2 = lang2.abbrev
        if abbrev2 in self.agr_maps and (feat1, feat2) in self.agr_maps[abbrev2]:
            # The map is already there
            return
        #        print('Reversing agr map for {}: ({},{})'.format(self, feat1, feat2))
        revfmap = {}
        # Assign values to each other
        for val2, vals1 in fmap.items():
            for val1 in vals1:
                if val1 in revfmap:
                    revfmap[val1].add(val2)
                else:
                    revfmap[val1] = {val2}
        # Assign the fmap to self.agr_maps
        if lang2.abbrev not in self.agr_maps:
            self.agr_maps[abbrev2] = {}
        self.agr_maps[abbrev2][(feat1, feat2)] = {}
        for val1, vals2 in revfmap.items():
            if {val1} == vals2:
                # Don't bother to record trivial mappings
                continue
            self.agr_maps[abbrev2][(feat1, feat2)][val1] = tuple(vals2)

    def get_agr_map(self, lang2, feat1, feat2):
        '''Return the agr map for other language lang2, feat1 of this language and feat2 of
        lang2. lang1, feat1, and feat2 are all strings.'''
        lmap = self.agr_maps.get(lang2)
        if lmap:
            fmap = lmap.get((feat1, feat2))
            if fmap:
                return fmap
        return None
              
    def get_label_int(self, label, dim_abbrev):
        labels = self.labels.get(dim_abbrev, [])
        if label == '^':
            return len(labels)
        else:
            return labels.index(label)

    def get_int_label(self, index, dim_abbrev):
        labels = self.labels.get(dim_abbrev, [])
        if index >= len(labels):
            return '^'
        else:
            return labels[index]

    def get_feat_int(self, feature):
        if feature not in self.feats:
            #            print('{} adding {} to feats'.format(self, feature))
            self.feats.append(feature)
        return self.feats.index(feature)

    def get_int_feat(self, index):
        return self.feats[index]

    def get_labeldfeat_int(self, label, dfeat):
        """Convert a label, daughter feature pair to an int."""
#        if (label, dfeat) not in self.labeldfeats:
#            self.labeldfeats.append((label, dfeat))
#        print(self, 'get_labeldfeat_int', label, dfeat)
        return self.labeldfeats.index((label, dfeat))

    def get_int_labeldfeat(self, index):
        """Convert an int to a label, daughter feature pair."""
        return self.labeldfeats[index]

    def get_int_govlabeldfeat(self, index):
        """Convert an int to a label, daughter feature pair."""
        return self.govlabeldfeats[index]

    def get_govlabeldfeat_int(self, label, dfeat):
        """Convert a label, daughter feature pair to an int."""
#        if (label, dfeat) not in self.govlabeldfeats:
#            self.govlabeldfeats.append((label, dfeat))
        return self.govlabeldfeats.index((label, dfeat))

    def get_crossgovlabeldfeat_int(self, label, dfeat):
        """Convert a label, daughter feature pair to an int."""
        if (label, dfeat) in self.crossgovlabeldfeats:
            return self.crossgovlabeldfeats.index((label, dfeat))

    def agree_strings_to_ints(self, agree):
        """Convert an agree triple of strings to a pair of ints."""
#        print('agree', agree)
        # Mother feature int
        mfeat = self.get_feat_int(agree[1])
        # Label/daughter feature int
        labeldfeat = self.get_labeldfeat_int(agree[0], agree[2])
        return mfeat, labeldfeat
        
    #    def dagree_strings_to_ints(self, dagree):
    #        """Convert a daughter agree tuple of strings to a pair of ints.
    #        """
    ##        print('dagree', dagree)
    #        dim = dagree[0]
    #        dagr = dagree[1:]
    #        feat = self.get_feat_int(dagr[1])
    #        labels = [self.get_label_int(l, dim) for l in dagr[1:]]
    #        return (feat,) + tuple(labels)
        
    def gov_strings_to_ints(self, gov):
        """Convert a govern triple of strings (and int tuple) to a pair of ints."""
        labelfeat = self.get_govlabeldfeat_int(gov[0], gov[1])
        return labelfeat, gov[2]

    def crossgov_strings_to_ints(self, gov):
        """Convert a govern triple of strings (and int tuple) to a pair of ints."""
        labelfeat = self.get_crossgovlabeldfeat_int(gov[0], gov[1])
        if labelfeat:
            return labelfeat, gov[2]

    def ints_to_agree_strings(self, agree):
        """Convert an agree int pair to a triple of strings."""
        # Mother feature
        mfeat = self.get_int_feat(agree[0])
        # Label, daughter features
        label, dfeat = self.get_int_labeldfeat(agree[1])
        return label, mfeat, dfeat

    ## Morphology

    def set_morphology(self, morphology):
        '''Assign the Morphology object for this Language.
        @param morphology: everything we need to handle morphology for this
                           language
        @type  morphology: instance of Morphology
        '''
        self.morphology = morphology
        morphology.language = self
        morphology.directory = os.path.join(self.get_dir(), 'FST')
        morphology.seg_units = self.seg_units

    def load_morpho(self, analysis=True, generation=True, segment=False,
                    simplified=False, ortho=True, guess=False,
                    load_analyzed=True, verbose=False):
        """Load words and FSTs for morphological analysis and/or generation.
        @param  analysis:   whether to load analysis FSTs
        @type   analysis:   boolean
        @param  generation: whether to load generation FSTSs
        @type   generation: boolean
        @param  segment:    whether analysis is to be segmentation
        @type   segment:    boolean
        @param  simplified: whether to use simplified FSTs (only relevant
                            for Amharic)
        @type   simplified: boolean
        @param  ortho:      whether to convert phonological to orthographic
                            representation (only supported, minimally, for
                            Amharic)
        @type   ortho:      boolean
        @param  guess:      whether to load guesser FSTs (along with lexical
                            ones)
        @type   guess:      boolean
        @param  load_analyzed: whether to load analyzed words
        @type   load_analyzed: boolean
        @param  verbose:    how verbose to be
        @type   verbose:    boolean
        """
        if self.morphology:
            fsts = self.morphology.pos
            print(Language.T.tformat('Loading morphology for {}...', [self], self.tlanguages))
            # Load unanalyzed and pre-analyzed words if we're doing analysis
            if analysis and load_analyzed:
                self.morphology.set_words(simplify=simplified, ortho=ortho)
                self.morphology.set_analyzed(ortho=ortho)
            for pos in fsts:
                # For analysis, load pre-analyzed words if any
                if analysis and load_analyzed:
                    self.morphology[pos].set_analyzed(ortho=ortho)
                # Load lexical anal and/or gen FSTs
                if analysis:
                    self.morphology[pos].load_fst(gen=False, guess=False,
                                                  simplified=simplified, verbose=verbose)
                if generation:
                    self.morphology[pos].load_fst(generate=True, invert=True, gen=True,
                                                  simplified=simplified, guess=False,
                                                  verbose=verbose)
                # Load guesser anal and gen FSTs
                if guess:
                    if analysis:
                        self.morphology[pos].load_fst(gen=False, guess=True, verbose=verbose)
                    if generation:
                        self.morphology[pos].load_fst(generate=True, invert=True, gen=True,
                                                      simplified=simplified, guess=True,
                                                      verbose=verbose)
#                        self.morphology[pos].load_gen_fst(simplified=simplified, guess=True,
#                                                          verbose=verbose)
            self.morphology_loaded = True

    def anal(self, word, form, guess=False, record=True, cache=True, verbose=True):
        """Return the word along with extracted analyses.
        @param word:  a wordform to be analyzed
        @type  word:  string
        @param form:  possibly preprocessed word
        @type  form:  string
        @param guess: whether to apply guesser FSTs in analysis
        @type  guess: boolean
        @param record: whether to record agr values
        @type  record: boolean
        @param cache: whether to cache the analyses found
        @type  cache: boolean
        @return:       the word and a list of analyses
        @rtype:        tuple consisting of word and a list of analyses
        """
        # Check to see if the word has already been analyzed and is stored in the cache
        if self.morph_anal_cache:
            cached = self.morph_anal_cache.get(form)
            if cached:
                if verbose:
                    print("Analysis of {} is cached".format(form))
                # The analyis is stored in the cache
                if form in self.morph_seg_cache:
                    seg_cache = self.morph_seg_cache[form]
                    return word, seg_cache[0], seg_cache[1], seg_cache[2]
                else:
                    # Avoid analysis altogether
                    return []
        # Do the real morphological analysis WORK, return a list of analyses
        analyses = self.anal_word(form, guess=guess, postproc=False)
        segmentations = None
        if analyses:
            if self.extract:
                # Language has an explicit morpho->syn extraction function
                extracted = [self.extract(analysis) for analysis in analyses]
            else:
                # Language (hopefully) has POS-specific morpho->syn dicts,
                # read in from the grammar data file (.gr), for example, for Gn
                # (eventually all languages)
                extracted = [self.anal_from_dict(analysis) for analysis in analyses]
            # Check for insertions/segmentations; all analyses have to specify the same ones
            seg = None
            new_word = None
            for e in extracted:
                if len(e) == 5:
#                    print('extracted {}'.format(e))
                    # There's a segmentation spec
                    if e[3]:
                        if seg and e[3] != seg:
                            # If this spec is different, there's apparently ambiguity,
                            # so don't do segmentations at all
                            break
                        else:
                            seg = e[3]
                            new_word = e[4]
                    else:
                        break
            segmentations = seg
            # Record the new feat-values
            self.record_agrs([extr[2] for extr in extracted if extr])
            # Return the word, all root, analysis pairs, and a possible insertion
            # preceding or following the root
            anals = [extr[:2] for extr in extracted if extr]
#            print('word {}, anals {}, segmentations {}, new_word {}'.format(word, anals, segmentations, new_word))
            if cache:
                if verbose:
                    print('Caching analysis of {}'.format(form))
                if segmentations:
                    self.morph_seg_cache[form] = [anals, segmentations, new_word]
                self.morph_anal_cache[form] = anals
            return word, anals, segmentations, new_word

    def anal_from_dict(self, analysis):
        """Convert a morphological analysis, consisting of POS, citation, and FS,
        to a dictionary of features appropriate for XDG syntax."""
        # analysis is (POS, root, citation, FS)
        syn = {}
        pos = analysis[0]
        root = analysis[1]
        anal_fs = analysis[3]
        anal_fs = anal_fs.unfreeze()
#        print('anal fs {}'.format(anal_fs.__repr__()))
        # Word(s) to insert if this word is being split
        insert = []
        # Whether anal_fs gets modified
        fs_changed = False
        pos_morph = self.morphology[pos]
        anal_dict = pos_morph.anal_dict
        for morph_feat, fv in anal_dict.items():
            syn_values = {}
            # First check to see whether any of fv begin with '!';
            # these are features that should have no values if the condition
            # (second and third elements in fv) is satisfied
            no_value_conds = [(x[1], x[2]) for x in fv if x[0] == '!']
            # If there are any check whether any of the conditions apply
            no_value = False
            for cond_feat, cond_value in no_value_conds:
                cond_anal_value = anal_fs.get(cond_feat)
                if fs.simple_unify(cond_anal_value, cond_value) != 'fail':
                    # Condition succeeds; no value provided for morph_feat
                    no_value = True
                    break
            if no_value:
                # Some no value condition succeeded, so skip morph_feat
                continue

            dflt_feat, dflt_val = None, None
            anal_value = anal_fs.get(morph_feat)
            match = False
            for morph_value, syn_feat, syn_value in fv:
#                print('anal {}, morph {}, syn {}={}'.format(anal_value.__repr__(), morph_value.__repr__(), syn_feat, syn_value))
                if morph_value == '!':
                    continue
                # Default feature value for case when no other match input
                if morph_value == '*':
                    dflt_feat, dflt_val = syn_feat, syn_value
                elif isinstance(morph_value, str) and morph_value[0] == '*':
                    morph_value = morph_value[1:]
                    if anal_value.get(morph_value) is None:
#                        print('Using default value for {}: {}'.format(syn_feat, syn_value))
                        syn_values[syn_feat] = syn_value
                # If the value in analysis for morph_feat agrees with morph_value,
                # add syn_value to the set of values for syn_feat
                elif fs.simple_unify(anal_value, morph_value) != 'fail':
                    match = True
                    if syn_feat == '!':
                        # Ignore analyses with this feature-value pair
                        return None
                    elif syn_feat == '^':
                        insert.append(syn_value)
#                        print('   root {}, morph_feat {}, morph_value {}'.format(root, morph_feat, morph_value))
                        anal_fs[morph_feat] = None
#                        print("   adjusted FS: {}".format(anal_fs.__repr__()))
                        fs_changed = True
                        continue
                    if syn_feat in syn_values:
                        syn_values[syn_feat].update(syn_value)
                    else:
                        syn_values[syn_feat] = syn_value
#                    print("  Updated values for {}: {}".format(syn_feat, syn_values[syn_feat]))
            if syn_values:
                for sf, sv in syn_values.items():
                    if sf:
                        syn[sf] = sv
#                    print('Assigning syn value for {}: {}'.format(sf, sv))
            # Use default if there were no matches
            if not match and dflt_feat:
                syn[dflt_feat] = dflt_val
        new_word = root
        if fs_changed:
            new_word = pos_morph.gen(root, features=anal_fs)[0][0]
#            print('  new word {}, insert {}'.format(new_word, insert))
        return root, syn, set(), insert, new_word

    def gen_from_dict(self, pos, feat_dict, daughters=None, mothers=None,
                      forms=None, del_nodes=None):
        """Convert feature dictionary to a feature structure and generate using
        morphology FST, dependencies, and forms of other words in sentence."""
        gen_dict = self.morphology[pos].gen_dict
        # feature structure to output
        fs = self.morphology[pos].defaultFS
        if fs:
            fs = fs.copy()
        else:
            fs = morphology.FeatStruct()
#        print('GEN FROM DICT FS {}'.format(fs.__repr__()))
        for syn_feat, fv in gen_dict.items():
            # Record features changed through affix merging so that they don't get changed again
            priority_feats = []
            if syn_feat == '<-':
                # Condition concerning mother of node
                if not mothers or not forms:
                    continue
                for arc, m in fv.items():
                    if arc in mothers:
                        # set of mothers of this node
                        arc_mothers = mothers[arc]
                        for mnode in arc_mothers:
                            mnode_form = forms.get(mnode, '')
                            if mnode_form in m:
                                add_feat, add_value = m[mnode_form]
#                                print('Gen based on mother; arc {}, m node {}, m form {}, add feat {}, add value {}'.format(arc, 
#                                                                                                                            mnode, mnode_form, add_feat, add_value))
                                # Incorporate the feature of the affix
#                                print('Assigning {} to {}'.format(add_value, add_feat))
                                fs[add_feat] = add_value
                                priority_feats.append(add_feat)
                                # Delete the affix
                                del_nodes.append(mnode)
                continue
            if syn_feat == '->':
                # Condition concerning daughter of node
                if not daughters or not forms:
                    continue
#                print('Daughters {}, forms {}'.format(daughters, forms))
                for arc, d in fv.items():
                    if arc in daughters:
                        arc_daughters = daughters[arc]
                        for dnode in arc_daughters:
                            dnode_form = forms.get(dnode, '')
                            if dnode_form in d:
#                                print('Dnode form {} in d {}'.format(dnode_form, d))
                                add_feat, add_value = d[dnode_form]
#                                print('Gen based on daughter; arc {}, d node {}, d form {}, add feat {}, add value {}'.format(arc, dnode, 
#                                                                                                                              dnode_form, add_feat, add_value))
#                                print('Assigning {} to {}'.format(add_value, add_feat))
                                fs[add_feat] = add_value
                                priority_feats.append(add_feat)
                                del_nodes.append(dnode)
                continue
            gen_value = feat_dict.get(syn_feat)
            for syn_value, morph_feat, morph_value in fv:
                # A singleton set, so we need the first element
                if morph_feat in priority_feats:
#                    print('{} already set in affix merging'.format(morph_feat))
                    continue
                syn_value = list(syn_value)[0]
                if syn_value == gen_value:
                    if morph_feat in fs:
                        fs_val = fs[morph_feat]
#                        print('FS already has a value for {}: {}; new value: {}'.format(morph_feat, fs_val.__repr__(),
#                                                                                        morph_value.__repr__()))
                        u = morphology.simple_unify(morph_value, fs_val)
                        if u != 'fail':
#                            print('Assigning {} to {}'.format(u, morph_feat))
                            fs[morph_feat] = u
                            continue
                        elif isinstance(fs_val, morphology.FeatStruct) and isinstance(morph_value, morphology.FeatStruct):
                            # Update dict feat value with new value for some feature within the dict
                            fs_val.update(morph_value)
#                            print('Assigning {} to {}'.format(fs_val, morph_feat))
                            fs[morph_feat] = fs_val
#                            print('new value: {}'.format(fs_val.__repr__()))
                            continue
                        # If the old value doesn't unify with the new one, just replace it
#                    print('Assigning {} to {}'.format(morph_value, morph_feat))
                    fs[morph_feat] = morph_value
#                    print(' syn value {}: assigning morph feat {} to value {}'.format(syn_value, morph_feat, morph_value.__repr__()))
#        print('FS', fs.__repr__())
        # convert the FeatStruct to a FSSet
        return morphology.FSSet(fs)

    def record_agrs(self, featvals):
        """Record feat, val pairs from set featvals in agrs attribute."""
        lg_agrs = self.agrs
        featvals = set().union(*featvals)
        for feat, val in featvals:
            # This is where we can include () as an option for every feature, or not.
            lg_agrs[feat] = lg_agrs.get(feat, set()).union({val})

    def anal_word(self, form, guess=True, simplified=False, segment=False,
                  postproc=False):
        '''Analyze a single word form, trying all existing POSs, both lexical and guesser FSTs.

        @param  guess:      whether to use guesser FSTs (along with lexical ones)
        @type   guess:      boolean
        @param  simplified: whether to use simplified FSTs (only relevant for Amharic)
        @type   simplified: boolean
        @param  segment:    whether to return a segmented analysis
        @type   segment:    boolean
        @param  postproc:   whether to postprocess output (for example, convert roman
                            to non-roman characters)
        @type   postproc:   boolean
        @return:             list of analyses, each consisting of a part of speech,
                            root or stem, citation form, and feature structure
        @rtype:              list of 4-tuples: (string, string or None, string or None,
                            FeatStruct instance)
        '''
        postproc = postproc and self.postproc
        analyses = []
        fsts = self.morphology.pos

        for pos in fsts:
            #... or already analyzed within a particular POS
            preanal = self.morphology[pos].get_analyzed(form, simple=simplified)
            if preanal:
                analyses.extend(self.proc_anal(form, [preanal], pos,
                                               citation=True, simplified=simplified,
                                               guess=False, postproc=postproc))
        if not analyses:
            # We have to really analyze it; first try lexical FSTs for each POS
            for pos in fsts:
                analysis = self.morphology[pos].anal(form, simplified=simplified)
                if analysis:
                    # Keep trying if an analysis is found
                    analyses.extend(self.proc_anal(form, analysis, pos,
                                                   citation=True, simplified=simplified,
                                                   guess=False, postproc=postproc))
            # If nothing has been found, try guesser FSTs for each POS
            if not analyses and guess:
                # Accumulate results from all guessers
                for pos in fsts:
                    analysis = self.morphology[pos].anal(form, guess=True)
                    if analysis:
                        analyses.extend(self.proc_anal(form, analysis, pos,
                                                       citation=True, simplified=simplified,
                                                       guess=True, postproc=postproc))
        return analyses

    def proc_anal(self, form, analyses, pos, citation=True,
                  simplified=False, guess=False, postproc=False):
        '''Process analyses according to various options, returning a list of analysis tuples.
        @param  form:       wordform
        @type   form:       string/unicode
        @param  analyses:   list of analyses: root, feature structure
        @type   analyses:   list of pairs: (string/unicode, FeatStruct instance)
        @param  pos:        part of speech
        @type   pos:        string
        @param  citation:   whether to display the citation form in the output
        @type   citation:   boolean
        @param  simplified: whether the analyses are the result of simplified FSTs (only relevant
                            for Amharic)
        @type   simplified: boolean
        @param  guess:      whether the analyses are the result of applying a guesser FST
        @type   guess:      boolean
        @param  postproc:   whether to postprocess output (for example, convert roman
                            to non-roman characters)
        @type   postproc:   boolean
        '''
        # Add ? to indicate that this is guesser output
        cat = '?' + pos if guess else pos
        # Add results to a set to avoid duplicates
        results = set()
        for analysis in analyses:
            root = analysis[0]
            grammar = analysis[1]
            if postproc and self.morphology[pos].postproc:
                self.morphology[pos].postproc(analysis)
            proc_root = analysis[0]
            for g in grammar:
                grammar = g
                # Create a citation form
                if citation:
                    cite = self.morphology[pos].gen_citation(root, g)
                    if postproc:
                        cite = self.postprocess(cite)
                # Don't bother with citation form
                else:
                    cite = None
                    # Prevent analyses with same citation form and FS
                results.add((cat, proc_root, cite, grammar))
        # Convert the set to a list and return
        return list(results)

    def gen_word(self, pos, root, feat_dict,
                 daughters=None, mothers=None, forms=None, del_nodes=None,
                 verbose=False):
        """Attempt to generate a wordform given POS, root, dict of features and values,
        arc label dicts of daughters and mothers, and target forms of all words in sentence.
        Called in graph.py."""

#        print('Gen word {}, pos {}, feat_dict {}, daughters {}, mothers {}, forms {}'.format(root, pos, feat_dict, daughters, mothers, forms))
        if not feat_dict:
            return "*" + root + "*"
        # Skip this for now; features may change in gen_from_dict()
#        feat_hashable = tuple(sorted(feat_dict.items()))
#        print(pos, root, feat_dict)
#        args = (pos,root,feat_hashable)
#        if args in self.generated_words:
#            return self.generated_words[args]
        if 'pos' not in feat_dict:
            feat_dict['pos'] = pos
        morf = self.morphology
        if pos not in morf:
            if 'all' in morf:
                pos = 'all'
            else:
                print(pos, "can't be generated")
                return
        if self.dict2fs:
            fss = self.dict2fs(feat_dict)
        else:
            fss = self.gen_from_dict(pos, feat_dict, daughters, mothers, forms, del_nodes)
#        print('FSS {}'.format(fss.__repr__()))
        posmorf = morf[pos]
        if verbose:
            print('Generating', pos, root, feat_dict, fss.__repr__())
        output = posmorf.gen(root, fss, postproc=self.postproc)
        if output:
#            self.generated_words[args] = output[0][0]
            return output[0][0]
        print(pos, root, feat_dict, fss, "can't be generated")
        return

    # Functions for doing only morphology analysis or generation
    def analyze(self, form, root=True, pos=True, gram=True,
                preproc=False):
        """Analyze a single word, returning a set with the root, POS,
        and grammatical features as specified. The empty list is returned
        if there is no possible analysis."""
        if preproc:
            form = self.preproc(form)
        analyses = self.anal_word(form)
        if gram:
            return {(a[1], a[1], a[3]) for a in analyses}
        else:
            result = set()
            for a in analyses:
                if root and not pos:
                    result.add(a[1])
                elif pos and not root:
                    result.add(a[0])
                else:
                    result.add((a[1], a[0]))
            return result

    def analyze_file(self, infile, outfile=None,
                     root=True, pos=True, gram=True,
                     start=0, nlines=0, lower=True,
                     preproc=False,
                     saved=None):
        """Analyze the words in infile, writing them to outfile
        if specified.
        If non-0, start specifies a line in the file to start with,
        and nlines specifies a number of lines to analyze.
        If non-None, preproc is a preprocessing function that takes
        a string and returns a string."""
        try:
            filein = open(infile, 'r', encoding='utf-8')
            # If there's no output file, write analyses to standard out
            out = sys.stdout
            if outfile:
                # Where the analyses are to be written
                fileout = open(outfile, 'w', encoding='utf-8')
                out = fileout
            n = 0
            # Save words already analyzed to avoid repetition
            saved = saved or {}
            # If nlines is not 0, keep track of lines read
            lines = filein.readlines()
            if start or nlines:
                lines = lines[start:start+nlines]
            for line in lines:
                output = ''
                # Separate punctuation from words
                line = self.morphology.sep_punc(line)
#                print("Saved {}".format(saved))
                # Segment into words
                for w_index, word in enumerate(line.split()):
                    analyses = []
                    # Lowercase on the first word, assuming a line is a sentence
                    if lower:
                        word = word.lower()
                    if word in saved:
                        # Don't bother to analyze saved words
                        analyses = saved[word]
#                        print('Anal {} for {}'.format(analyses, word))
                    else:
                        # Attempt to analyze the word
                        if preproc:
                            word = preproc(word)
                        analyses = self.analyze(word, root=root, pos=pos, gram=gram,
                                                preproc=preproc)
                        saved[word] = analyses
                    if analyses:
                        output += "{}:{} ".format(word, analyses)
                    else:
                        output += "{} ".format(word)
                print(output, file=out)
            filein.close()
            if outfile:
                fileout.close()
        except IOError:
            print('No such file or path; try another one.')

    def generate(self, pos, root, feat_dict, verbose=False):
        """Attempt to generate a wordform given POS, root, and dict of syntactic
        features and values (which must first be converted a set of morphological
        feature structures. A bit simpler than gen_word."""

        if not feat_dict:
            return "*" + root + "*"
        feat_hashable = tuple(sorted(feat_dict.items()))
        args = (pos,root,feat_hashable)
        if args in self.generated_words:
            return self.generated_words[args]
        if 'pos' not in feat_dict:
            feat_dict['pos'] = pos
        morf = self.morphology
        if pos not in morf:
            if 'all' in morf:
                pos = 'all'
            else:
                print(pos, "can't be generated")
                return
        if self.dict2fs:
            fss = self.dict2fs(feat_dict)
        else:
            fss = self.gen_from_dict(pos, feat_dict)
#        print('FSS {}'.format(fss.__repr__()))
        posmorf = morf[pos]
        if verbose:
            print('Generating', pos, root, feat_dict, fss.__repr__())
        output = posmorf.gen(root, fss, postproc=self.postproc)
        if output:
            self.generated_words[args] = output[0][0]
            return output[0][0]
        print(pos, root, feat_dict, fss, "can't be generated")
        return

    ## Loading, pickling, and depickling languages

    @staticmethod
    def pickle_all(languages, grammar='chunk', verbosity=1):
        """Pickle a list of linked languages, first decoupling morphology."""
        fsts = [l.morphology.unset_fsts() for l in languages]
        for l in languages:
            l.morphology_loaded = False
        for l in languages:
            l.pickle(grammar, decouple_morph=False, verbosity=verbosity)
        for l, f in zip(languages, fsts):
            l.morphology.reset_fsts(f)
            l.morphology_loaded = True

    def pickle(self, grammar, decouple_morph=True, verbosity=1):
        """Save language as a python pickle, for quick loading later.
        Decouple morphology first so the pickle isn't enormous."""
        if verbosity > 1:
            print("Pickling {0}:{1} for later".format(self.name, grammar or self.abbrev))
        fsts = None
        if self.morph_processing and decouple_morph:
            fsts = self.morphology.unset_fsts()
            self.morphology_loaded = False

        path = Language.get_picklepath(self.abbrev, grammar or self.abbrev)

#        print("Pickling {} with morphology {}".format(self, self.morphology))
        
        with open(path, "wb") as stream:
            pickle.dump(self, stream)
        
        if self.morph_processing and decouple_morph:
            self.morphology_reset_fsts(fsts)
            self.morphology_loaded = True

        self.pickled = True

    def load_morphology(self, analysis=True, generation=True, learn=False):
        """Load the language's morphology if this hasn't already happened."""
        if self.morph_processing and not self.morphology_loaded:
            self.load_morpho(guess=learn, analysis=analysis, generation=generation,
                             verbose=False)

    @staticmethod
    def get_langs(lang_ids, load=True, reload=False, flatten_lexicon=False,
                  load_morpho=True, pickle=True,
                  grammar='', verbosity=1):
        """Get the languages with lang_ids, attempting to load them if they're not found
        and load is True or if reload is True."""
        languages = []
        for lang_id in lang_ids:
            if reload or ((not lang_id in Language.LANGUAGES) and load):
                lang = Language.load(lang_id, force=reload, flatten_lexicon=flatten_lexicon,
                                     load_morpho=load_morpho, pickle=pickle,
                                     grammar=grammar, verbosity=verbosity)
            else:
                lang = Language.LANGUAGES.get(lang_id, None)
            languages.append(lang)
        return languages

    def is_linked(self, languages):
        """Is this language linked to all languages (have crosslexes been finalized?)?"""
        return all([l.abbrev in self.linked_languages for l in languages if l != self])

    @staticmethod
    def are_linked(languages):
        return all([l.is_linked(languages) for l in languages])

    @staticmethod
    def load_langs(lang_ids, analysis=True, generation=True, lexicon=True,
                   force=False, pickle=True, flatten=False, learn=False,
                   load_morpho=True, grammar='', semantics=True, verbosity=1):
        languages = []
        print("Loading languages: {}".format(', '.join(lang_ids)))
        for lang_id in lang_ids:
            lang = Language.get(lang_id, load=True, reload=force, flatten_lexicon=False,
                                load_morpho=False, pickle=False, learn=learn,
                                grammar=grammar, verbosity=verbosity)
            languages.append(lang)
        if not flatten:
            for lang in languages:
#            if not lang.pickled:
                lang.finalize()
#            if not Language.are_linked(languages):
#                Language.link(languages, flattened=False, verbosity=verbosity)
        else:
            if verbosity:
                print("Flattening")
            flatlexs = []
            for lang in languages:
                lexicon = lang.lexicon
                if lexicon.hierarchical:
                    # Lexicon is not yet flattened
                    other = languages[:]
                    other.remove(lang)
                    flatlexs.append(lang.lexicon.flatten(between=False, other_languages=other))
            if verbosity:
                print("Finalizing")
            for flex, lang in zip(flatlexs, languages):
                lang.set_lexicon(flex, finalize=True)
        if not Language.are_linked(languages):
            if verbosity:
                print("Linking")
            Language.link(languages, flattened=flatten, verbosity=verbosity)
        if pickle:
            if verbosity:
                print("Pickling")
            for lang in languages:
                if not lang.pickled:
                    lang.pickle(grammar, decouple_morph=False, verbosity=verbosity)
        ## Morphology; not included in language pickle
        if load_morpho:
            for lang in languages:
                if not lang.morphology_loaded:
                    if not lang.pickled:
                        print('Warning: loading morphology for unpickled language {}; pickle will be enormous'.format(lang))
                    lang.load_morpho(guess=learn, analysis=analysis, generation=generation,
                                     verbose=False)
                else:
                    print("{}'s morphology already loaded".format(lang))
        ## Record link finalization for all language pairs
#        for language1 in languages:
#            for language2 in languages:
#                if language1 == language2:
#                    continue
#                language1.linked_languages.append(language2)

        Lex.ID = len(languages[0].lexicon.values())

        return languages

    @staticmethod
    def link(languages, flattened=True, verbosity=0):
        """
        Realize cross-lingual links between languages.
        """
#        if verbosity:
#            print('Linking languages')
        ## Record link finalization for all language pairs
        for language1 in languages:
            for language2 in languages:
                if language1 == language2:
                    continue
                language1.linked_languages.append(language2.abbrev)
        ## Do the actual finalization.
        for lang in languages:
            lang.finalize_agrmaps(languages)
        for lang in languages:
            lang.finalize_crosslexes(flatten=flattened)
        if flattened:
            for lang in languages:
                lang.lexicon.finalize_flat()

    @staticmethod
    def load(lang_id, analysis=True, generation=True, lexicon=True,
             force=False, pickle=True, flatten_lexicon=False,
             load_morpho=True, morpho_only=False, learn=False,
             grammar='', semantics=True, verbosity=1):
        """Load lexicon, morphology objects and FSTs for language with lang_id.
        @param  lang_id:    2-3 char ID for a language; capitalized
        @type   lang_id:    string
        @param  analysis:   whether to load analysis FST for morphologically
                            complex languages
        @type   analysis:   boolean
        @param  generation: whether to load generation FST for morphologically
                            complex languages
        @type   generation: boolean
        @param  lexicon:    whether to load a lexicon for the language
        @type   lexicon:    boolean
        @param  force:      whether to force (re)loading of lexicon
        @type   force:      boolean
        @param  pickle:     whether to pickle the language
        @type   pickle:     boolean
        @param  flatten_lexicon: whether to flatten the lexicon (before pickling)
        @type   flatten_lexicon: boolean
        @param  grammar:    name of a specific grammar to load
        @type   grammar:    string
        @param  semantics:  whether to add lexicon to SEMANTICS too
        @type   semantics:  boolean
        @param  load_morpho: whether to load morphology
        @type   load_morpho: boolean
        @param  morpho_only: whether to load *only* morphology
        @type   morpho_only: boolean
        @param  learn:       whether learning will take place during processing
        @type   learn        boolean
        """
        language = None
        # Use the pickled grammar/lexicon if force is False and there is a pickle
        pkl = not force and Language.load_pickle(lang_id, grammar, verbosity=verbosity)
        if pkl:
            language = pkl
        # Look for the grammar in a Python source file
        # for languages that don't have data files 
    #    try:
        elif lang_id == 'sem':
            from .languages.sem import sem
            language = sem.SEMANTICS[grammar]
        elif lang_id == 'en':
            from .languages.en import en
            language = en.ENGLISH[grammar]
        elif lang_id == 'am':
            from .languages.am import am
            language = am.AMHARIC[grammar]
#        elif lang_id == 'es':
#            from .languages.es import es
#            language = es.SPANISH[grammar]
        elif lang_id == 'qu':
            from .languages.qu import qu
            language = qu.QUECHUA[grammar]
        if language:
#            print('{} already loaded'.format(language))
            pass
            # Attempt to load data from a grammar file if there is one
#            language.load_data(load_morph=False,
#                               analysis=analysis, generation=generation,
#                               grammar=grammar,
#                               verbose=verbosity)
        else:
            # If there's still no language, create it from scratch using the grammar
            # file.
            language = Language.make('', lang_id, load_morph=False,
                                     grammar=grammar,
                                     analysis=analysis, generation=generation, learn=learn,
                                     verbose=verbosity)
        Language.LANGUAGES[lang_id] = language
        ## Lexicon
        # If the language's lexicon wasn't included in its language module and we're supposed
        # to load one, look for it in a YAML file
        if not language.lexicon and lexicon and not morpho_only:
            lex = Lexicon.load(language, verbosity=verbosity)
            # Flatten the lexicon if flatten_lexicon is True
            # (There's a lot duplication here; it can probably be fixed by changing Lexicon.inherit())
            if flatten_lexicon:
                lex = lex.flatten()
            language.set_lexicon(lex)
        if not pkl and pickle and not morpho_only:
            # Pickle the grammar/lexicon for the next time around
            language.pickle(grammar, verbosity=verbosity)
        ## Morphology; do this *after* pickling so it's not included in the pickled grammar,
        ## which will otherwise be *humongous*
        if load_morpho or morpho_only:
            language.load_morpho(guess=learn, analysis=analysis, generation=generation,
                                 verbose=False)
        return language
    #    except ImportError:
    #        print("Language file not found")

    @staticmethod
    def get(lang_id, load=True, reload=False, flatten_lexicon=False,
            load_morpho=True, pickle=True, learn=False,
            grammar='', verbosity=1):
        """Get the language with lang_id, attempting to load it if it's not found
        and load is True or if reload is True."""
        if reload or ((not lang_id in Language.LANGUAGES) and load):
            Language.load(lang_id, force=reload, flatten_lexicon=flatten_lexicon,
                          load_morpho=load_morpho, pickle=pickle, learn=learn,
                          grammar=grammar, verbosity=verbosity)
#        else:
#            print("{} already loaded".format(lang_id))
        return Language.LANGUAGES.get(lang_id, None)

    ### Pickling and depickling languages
    
    @staticmethod
    def load_pickle(lang_abbrev, grammar, verbosity=1):
        """Load the language from the pickle if there's a recent available
        one and force is False.
        """
        import glob
        langdir = Language.get_langdir(lang_abbrev)
        yamls = glob.glob(os.path.join(langdir, '*.yaml'))
        sources = glob.glob(os.path.join(langdir, '*.py'))

        mtimes = [os.path.getmtime(fn) for fn in yamls + sources]

        picklepath = Language.get_picklepath(lang_abbrev, grammar or lang_abbrev)
        if os.path.exists(picklepath):
            pickletime = os.path.getmtime(picklepath)
            if max(mtimes) < pickletime:
                if verbosity:
                    print("Using pickle for {}: {}; depickling".format(lang_abbrev, grammar))
                return Language.depickle(lang_abbrev, grammar or lang_abbrev)

    @staticmethod
    def depickle(lang_abbrev, filename):
#        print('Depickling {}'.format(lang_abbrev))
        path = Language.get_picklepath(lang_abbrev, filename)

        with open(path, "rb") as stream:
            language = pickle.load(stream)

        language.pickled = True

        return language

    @staticmethod
    def get_langdir(lang_abbrev):
        path = os.path.join(LANGUAGE_DIR, lang_abbrev)
        return path

    @staticmethod
    def get_picklepath(lang_abbrev, filename):
        return os.path.join(Language.get_langdir(lang_abbrev), filename + '.pkl')

    @staticmethod
    def find(lang_abbrev):
        """Just return the language with abbreviation lang_abbrev."""
        return Language.LANGUAGES.get(lang_abbrev)
