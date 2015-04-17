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
# -- Language in separate module.
# 2010.08.29 (MG)
# -- Added Group class and Lex method incorporating attributes
#    from groups in participating lexical entries. Groups
#    do not normally create new lexical entries for words
#    they contain.
# 2010.09.05 (MG)
# -- Groups now *do* create new lexical entries for each of their
#    as in Debusmann's groups. (It seemed impossible to implement
#    groups otherwise.)
# 2010.09.11 (MG)
# -- inherit_properties brought over from older XDG (differences
#    include sets instead of lists, list of ints instead of
#    feature structures.
# 2010.09.13 (MG)
# -- Finished inheritance, more or less.
# 2010.10.10 (MG)
# -- I broke pickling of lexicons. It's trying to pickle some function
#    (method?), resulting in
#    _pickle.PicklingError: Can't pickle <class 'function'>: attribute lookup builtins.function failed
# -- Fixed it. But it requires replacing all of the lambda functions that are values
#    of attributes in Language, Morphology, and POS_Morphology including preprocess and postprocess,
#    which are still needed for Amharic
# 2010.10.17 (MG)
# -- Added method (incorp_analyses) for incorporating morphological analyses into clone of lex
# 2010.10.23 (MG)
# -- Fixed inheritance so it works with sets of tuples.
# -- Lexicon.lexicalize() looks up only words (not lexemes) by default.
# -- Lexdim abbreviations changed to lg-dim in lexicon, except for semantic dimensions
# 2010.10.24 (MG)
# -- Unification methods are functions.
# 2010.10.31
# -- Added root and pos to Lex attribs. During inheritance they are copied to the names dict
#    attribute under language (in Lex.inherit_properties()).
# 2010.11.13
# -- Fixed bug in unify_fs (affecting unification of tuples of different lengths)
# 2010.11.16
# -- Fixed valency inheritance so 0, ! have precedence over +, ?, *
# 2010.12.12
# -- In LexDim, record_agrs also records features/values in 'govern' attribute.
# 2011.01.31
# -- Lexes have a crosslexes attrib: a dict association target language abbreviations
#    with [target_entry, LexDim] pairs (LexDim optional).
#    "target_entry" is (target_entry_label, target_entry_index) when lexicon is initialized,
#    converted to entry object in Language.finalize_crosslexes()
# 2011.02.01
# -- New crosslexes work in inheritance by creating a clone of the target entry
#    with the cross-lingual LexDim added to it (when there is a LexDim; when there
#    isn't, no clone is necessary).
# 2011.02.06
# -- Fixed inherit so it doesn't get stuck in loops. Target languages can't inherit
#    back to semantics.
# 2011.02.10
# -- Empty nodes incorporated in inheritance and Lex.from_dict().
# 2011.02.13
# -- New pattern functions check whether one feature tuple is a generalization of
#    another and remove specializations from sets of feature tuples. This is used
#    in language.py to simplify the list of possible agr features (and prevent
#    spurious analyses with features that have values of (0,0) vs. (0,0,0), say).
# 2011.02.22
# -- Fix crosslexes so that an entry can have more than one. In an entry, the YAML
#    now looks like this:
#    cross:
#      sem:
#        - lex: ...
#          dim: ...
#        - lex: ...
#      om:
#        lex: ...
# 2011.02.26
# -- Empty lexical entries (like @SB) now record this (based on the '@' in the name).
# 2011.03.09
# -- Cloned lexes were inheriting multiple times from the same class; fixed this (checking
#    ids and languages of inherited classes).
# -- Lex names attribute (including word, lexeme, gram labels) is now copied (a deepcopy)
#    when Lex is cloned. This fixes the output form of some words in the target language.
# 2011.03.11
# -- New way to represent subclass partitions of classes in YAML files, read in with
#    Lex.partition_from_dict().
# 2011.03.15
# -- Fix to incorp_analyses(), which failed to get the language for the LexDims right.
# 2011.03.18
# -- Possible to nest exhaustive class partitions, using 'subpartition' keyword under
#    'partition' in YAML lexicon (see examples in es/tiny.yaml).
# 2011.04.08
# -- Lexical class entries belonging to disjoint partitions of classes now record the other
#    elements of the partition in their disjoint attribute, and disjoint classes are
#    also accumulated during inheritance. The disjoint list is used in class_compatible.
# 2011.04.13
# -- Changes in how disjoint classes are read in from YAML files and recorded in entries.
# 2011.04.15
# -- Fixed a strange bug in inherit1 (how did this last so long?) that left the list of
#    entries empty if a possible ancestor on some branch was incompatible with the
#    original lex.
# 2011.04.17
# -- Fixed a bug in how disjoint classes get their parent classes.
# 2011.05.15
# -- In getting crosslexes, check for compatibility in the empty crosslex case.
# 2011.10.07
# -- Within partitions, crosslexes need to be associated with all parts (children)
#    rather than with the shared superclass. This now happens (see Lex.from_dict()).
# -- Lexicon.add_lex() changed to make words work as partition parts.
# 2011.12.06
# -- Lots of changes incorporating RevEmptyCrosslexes (mostly to inheritance)
# 2011.12.08
# -- Possible now to have more than one government constraint for a given word
#    and dimension (needed for Spanish transitive verbs).
# 2011.12.16
# -- Higher-level inheritance functions rewritten. Within-language and cross-language
#    inheritance is not kept separate, and inheritance for reverse empty nodes
#    is handled specially.
# 2011.12.18
# -- A few more fixes to inheritance, especially for empty nodes. Pretty stable now,
#    I think.
# 2011.12.22
# -- Patterns and unification eliminated (functions still around though).
# 2012.02.17
# -- Multiple indices possible in crosslex attribute.
# 2012.02.22
# -- Groups modified in several ways. Lexemes accessed in YAML can be copied
#    from others (see "break the ice" in en/tiny.yaml). (Note that this requires
#    that groups appear *after* other lexical entries.)  Groups now have a head
#    Lex (or set of Lexes in the case of disjoint lexeme children) which must
#    appear first in the YAML.
# 2012.02.25
# -- Various changes to reading functions for empty nodes, allowing more flexibility
#    for complex empty nodes (like copula in English as target).
# 2012.03.*
# -- Counts and probabilities in lexical entries and crosslexes.
#    Fixed bug in filter_classes.
# 2012.03.25
# -- Lexicon.flatten() produces a lexicon of only word and lexeme entries with
#    all attributes in grammatical entries inherited.
# -- In partition, keywords can now include 'wordpart', 'lexemepart', and 'grampart'.
# 2012.08.14
# -- Lexicon can have the same entry participating in multiple partitions (e.g.,
#    Gn @none in both @SJ and @OJ)
# 2012.09.16
# -- Fixes to make crosslexes work right in generation.
# 2012.11.19
# -- For each Lex, dictionaries for group IDs and group head IDs, with languages
#    as keys.
# 2012.12.01
# -- New attrib type specifying maximum (and potentially also minimum) number of arcs
#    into and out of nodes.
# 2013.05.22
# -- Added entries for unknown words.
# -- Fixed inheritance so it only checks the lexicon for grammatical classes when
#    it is flattening or working with (now completely obsolete!) hierarchical lexicons.
# 2013.07.11
# -- Split lexicon.py and lex.py
# 2013.07.15
# -- Fixed inherit_properties so it doesn't add classes from other languages.
# -- LexClass class for templates for new lexical entries (avoiding all inheritance).
# 2013.07.20-31
# -- LexClass read() method for reading in lex classes from files
# 2013.08.05
# -- Crosslex creation permits "cond", condition for creating empty node.
# 2013.09.12
# -- Made False the default value for the "bidir" attribute of crosslexes.
# 2014.02.02
# -- Method for creating and saving entry with word already morphologically analyzed,
#    inst_lexeme().
# 2014.02.04
# -- Method for creating entry with crosslingual features already "inherited" (spelled out),
#    lexify_cross_inh()

# Needed to check on dimension names in crosslex attributes (at least)
from .utils import DIMENSIONS, PARSE, GENERATE, TRANSLATE
from .crosslex import *
import copy, re

# String key for entries for unknown words.
UNKNOWN = '*'

# There can be many del arcs out of a node; that's why this is high.
MAX_CARD = 8

#### We need a Pattern class for this.
##
##def is_generalization(fs1, fs2):
##    """Is the first tuple a generalization (proper or improper) of the second?
##    >>> is_generalization((1,1,1), (1,1,1)) => True
##    >>> is_generalization((1,1), (1,1,1)) => True
##    >>> is_generalization((1,1,-1), (1,1,1)) => True
##    >>> is_generalization((1,1,0), (1,1,1)) => False
##    >>> is_generalization((1,1,1), (1,1)) => False
##    """
##    if len(fs1) > len(fs2):
##        return False
##    for i, (v1, v2) in enumerate(zip(fs1, fs2)):
##        if v2 == -1:
##            if v1 != -1:
##                return False
##        elif v1 != -1 and v1 != v2:
##            return False
##    # fs2 could still be longer than fs1, but it
##    # doesn't matter what's there
##    return True
##

### Feature structures

def elim_specializations(fss):
    """Eliminate any FSs in FSS that are specializations of other FSs."""
    fss_list = list(fss)
    for i1, fs1 in enumerate(fss_list[:-1]):
        i2 = i1 + 1
        if fs1 not in fss:
            continue
        removed = False
        while i2 < len(fss_list) and not removed:
            fs2 = fss_list[i2]
            if fs2 in fss:
                if is_generalization(fs2, fs1):
                    fss.remove(fs1)
                    removed = True
                elif is_generalization(fs1, fs2):
                    fss.remove(fs2)
            i2 += 1

def unify_fssets(fss1, fss2, elim_specs=False):
    """Unify sets of feature tuples, returning a set of results."""
    result1 = [unify_fs(f1, f2) for f1 in list(fss1) for f2 in list(fss2)]
#    print('fss1', fss1, 'fss2', fss2, 'result1', result1)
    result2 = {u for u in result1 if u is not False}
    if elim_specs:
        elim_specializations(result2)
    return result2

def unify_fs(fs1, fs2):
    """Unify two features (ints) or 'feature structures' (tuples of ints). -1 is a wild card.
    """
    if isinstance(fs1, int):
        return fs1 == fs2
    result = []
    for i, (v1, v2) in enumerate(zip(fs1, fs2)):
        u = unify_values(v1, v2)
        # u could be 0
        if u is False:
            return False
        result.append(u)
    if len(fs1) < len(fs2):
        result.extend(fs2[len(fs1):])
    elif len(fs2) < len(fs1):
        result.extend(fs1[len(fs2):])
    return tuple(result)

def unify_values(v1, v2):
    """Unify 2 feature ints. -1 is the wild card."""
    if v1 == -1:
        return v2
    if v2 == -1:
        return v1
    if v2 != v1:
        return False
    return v1
                
class Lex:
    '''Lexical entries'''

    ID = 0
    cloneID = 1

    # Precedence of valency values
    valency = [             
               0, '!', 
               # new options, to accommodate "soft" valency; "hard", then "soft";
               '0?', '!?',               
               '+', '?', '*'
               ]

    def __init__(self, name='', word='', label='', altname='', cloned=0,
                 lexeme=None, gram=None, empty=None, classes=None,
                 crosslexes=None, empty_daughs=None, crosslex=False,
                 complex_empty_nodes=None,
                 inh_classes=None, disjoint=None,
                 root=None, pos=None, names=None,
                 # Whether this is a partition "part"
                 part=False,
                 morph=None,
                 gid=0, id=0, entry_index=0, ghead=0,
                 # Added 2012.11.18: dictionaries of language, group ids; group head ids
                 gids=None, gheads=None,
                 # Added 2013.07.09
                 group_thead=None,
                 lexicon=None, language=None,
                 dims=None, cat=None,
                 # Partitions to which this lex belongs
                 partitions = None,
                 # Whether this entried is already flat (or flattened)
                 flat=False,
                 count=1, xcount=0,
                 # Only relevant for node entries during processing
                 prob=1.0):
        # Various kinds of names, probably not all needed
        self.name = name or word or lexeme or gram
        # Reserved for names of total disjoint subclasses of a superclass
        self.label = label
        self.altname = altname
        # Whether this is a cloned lexical entry
        self.cloned = cloned or 0
        # Basic lexical categories
        self.word = word
        self.lexeme = lexeme
        self.gram = gram
        self.root = root
        self.pos = pos
        # Whether this is an "empty lex"
        self.empty = empty
        # Dictionary of dim abbreviation: LexDim
        self.dims = dims or {}
        # Lexical classes
        self.classes = classes or []
        # Inherited classes
        self.inh_classes = inh_classes or []
        # Group id defaults to 0 (member of no group)
        self.gid = gid
        self.gids = gids or {}
        self.gheads = gheads or {}
        # Whether this is a group head
        self.ghead = ghead
        self.group_thead = group_thead or {}
        # Create a unique ID for this Lex (needed to recognize copies of same Lex)
        self.id = id or Lex.get_id()
        self.source_id = 0
        self.lexicon = lexicon
        self.language = language
        # Note: after this, there may still be no lexicon assigned
        if not self.language and lexicon:
            self.language = lexicon.language
        if not self.lexicon and self.language:
            self.lexicon = language.lexicon
        self.cat = cat
        self.entry_index = entry_index
        # Dict for storing language properties when merging with crosslingual entries
        self.names = names or {}
        # Part of a partition
        self.part = part
        # Dict for storing morphological information (only for lexemes)
        self.morph = morph or {}
        # Dict for storing crosslexes
        # {lang-id: [Crosslex, Crosslex, ...], ...}
        self.crosslexes = crosslexes or {}
        # List of classes for empty daughters
        self.empty_daughs = empty_daughs or []
        # List of xlexes for generating complex empty nodes
        self.complex_empty_nodes = complex_empty_nodes or []
        # Is this a cloned crosslex entry?
        self.crosslex = crosslex
        # Classes that this lex cannot have as ancestors
        self.disjoint = disjoint or []
        # Names of lexemes or grams whose partitions this lex belongs to
        self.partitions = partitions or []
        # Is it flat?
        self.flat = flat
        # Number of times this entry has been "used"
        self.count = count
        # Count of inherited xlexes (only in a Lex copy used during processing)
        self.xcount = xcount
        # Probability associated with this node entry; set for different copies of the entry
        # depending on counts for competing entries for a given node
        self.prob = prob
        if self.lexeme and not self.root:
            self.root = self.lexeme

    def __repr__(self):
        return '%{}:{}_{}{}'.format(self.language.abbrev, self.id, self.label or self.get_name(),
                                    ('=' + str(self.cloned)) if self.cloned else '')

    @staticmethod
    def get_id():
        '''Return a new Lex id, incrementing the counter.'''
        Lex.ID += 1
        return Lex.ID

    def clone(self, disjoint=True, temp=True, suf='', gid=0, lexicon=None,
              xcount=0, copy_xtarg=True, new_id=False, source_id=True):
        """Return a copy of this Lex. Only applies to word-level entries.
        If disjoint is False, don't copy disjoint classes. If temp is
        False, this is a permanent copy, not a temporary clone of self.
        If new_id is True, make this a separate lexical entry with all
        of the properties of self."""
#        print("Cloning {}".format(self))
        if not new_id:
            cloneID = Lex.cloneID
            Lex.cloneID += 1
        lexeme = self.lexeme
        word = self.word
        if suf:
            if lexeme:
                lexeme += suf
            else:
                word += suf
        copied = Lex(word=word, gram=self.gram, lexeme=lexeme,
                     name=self.name, root=self.root, pos=self.pos,
                     label=self.label, altname=self.altname,
                     cloned=0 if new_id else cloneID,
                     language=self.language,
                     # When flattening a lexicon, the cloned lex's lexicon is
                     # the new flattened one.
                     lexicon=lexicon or self.lexicon,
                     empty=self.empty,
                     crosslexes=self.copy_crosslexes(copy_targ=copy_xtarg),
                     crosslex=self.crosslex,
                     classes=self.classes[:],
                     inh_classes=self.inh_classes[:],
                     disjoint = self.disjoint[:] if disjoint else [],
                     partitions = self.partitions,
                     part = self.part,
                     # how about this?
                     empty_daughs=self.empty_daughs,
                     # or these; should they be copied too?
                     complex_empty_nodes=self.complex_empty_nodes,
                     entry_index=self.entry_index,
                     # names is a dict of dicts, so the copy must be deep
                     names=copy.deepcopy(self.names),
                     # morph may also be a dict of dicts (if it gets used at all)
                     morph=copy.deepcopy(self.morph),
                     id=self.id if (temp and not new_id) else self.get_id(),
                     gid=gid or self.gid,
                     gids=self.gids.copy(),
                     ghead=self.ghead,
                     gheads=self.gheads.copy(),
                     group_thead=self.group_thead,
                     flat=self.flat,
                     count=self.count,
                     xcount=xcount or self.xcount,
                     prob=self.prob)
        # Clone LexDims
        copied.dims = {}
        for abbrev, dim in self.dims.items():
            copied.set_lexdim(abbrev, dim.clone(lex=copied))
            #        if self.gid > 0:
            #            print('{} is member of group'.format(self))
#        if not temp and self.lexicon:
#            self.lexicon.add_lex(copied)
        if source_id:
            copied.source_id = self.id
        return copied

    def inst_lexeme(self, word):
        """Create an entry for an 'instantiated lexeme', a specific form that has already been
        analyzed and had its agreement features incorporated. lex is cloned lexeme entry."""
        # First clone the clone because we're going to add it to the lexicon
        inst = self.clone(disjoint=False, temp=False, new_id=True)
        inst.word = word
        self.lexicon.add_lex1(word, inst, existing=word in self.lexicon)
        return inst

    def lexify_cross_inh(self, word):
        """Create a new lexical entry for a Lex clone whose target lex features have
        been 'inherited'. The appropriate crosslex is deleted since it's no longer needed."""
        lex = self.clone(disjoint=False, temp=False, new_id=True, source_id=True)
        lex.crosslexes = None
        return lex

    def copy_crosslexes(self, copy_targ=True):
        if self.crosslexes:
            xlex_copy = {}
            for abbrev, xlexes in self.crosslexes.items():
                xlex_copy[abbrev] = [x.clone(copy_targ=copy_targ) for x in xlexes]
            return xlex_copy

    def equals(self, lex):
        """Are the two lexes 'the same lex'; is one a clone of the other?"""
        return (self.language == lex.language) and (self.id == lex.id)

    def is_disjoint(self, cls):
        """Are this lex incompatible with cls because of their disjoint classes?"""
        disj = self.disjoint
        if any([cls.equals(d) for d in disj]):
            # Class (or a clone of it) is on the list of disjoint classes of self
            return True
        inh = self.inh_classes
        for i in inh:
            if any([cls.equals(d) for d in i.disjoint]):
                # Class (or a clone of it) is on the list of disjoint classes of
                # some ancestor of self
                return True
        return False

    def is_lexical(self):
        """Is this a 'lexical' entry, that is, an entry for a word or a lexeme?"""
        return self.word or self.lexeme

    def is_unknown(self, language=None):
        """Is this entry 'unknown'; if language is non-None, for that language within the entry?"""
        if language:
            return self.names.get(language, {}).get('word') == '*'
        else:
            return self.word == '*'

    def is_inherited(self, languages):
        """Has the entry 'inherited' features from the corresponding entry in another language?"""
        l = languages if isinstance(languages[0], str) else [lg.abbrev for lg in languages]
        # does language have an entry in the names dictionary?
        return all([self.names.get(lg, False) for lg in l])

    def set_lexdim(self, dim, lexdim, traced=''):
        if traced and traced in {self.word, self.gram, self.name, self.label, self.lexeme}:
            print('{} setting lexdim {}: {}'.format(self, dim, lexdim))
        self.dims[dim] = lexdim

    def get_lexdim(self, dim):
        """The lexdim for a given dimension.
        dim: an instance of a subclass of Dimension
        """
        return self.dims.get(dim)

    def get_dimattrib(self, dim, attrib):
        lexdim = self.get_lexdim(dim)
        if lexdim:
            return lexdim.attribs.get(attrib, {})
        return {}

    def get_name(self):
        """Return the string identifier for the Lex, used as key in Lexicon."""
        return self.word or self.label or self.lexeme or self.gram or self.name

    def get_altname(self):
        """Return the other language string identifier for the Lex if language is Multiling."""
        return self.altname

    def get_pos(self):
        """Get the word's POS."""
        if self.pos:
            return self.pos
        else:
            for dct in self.names.values():
                p = dct.get('pos')
                if p:
                    return p

    def isa(self, cls):
        """Is cls an ancestor of this lex?"""
        # Need 'equals' rather than == because one could be a clone of the other
        if self.equals(cls):
            return True
        classes = self.classes
        for c in classes:
            for c1 in self.lexicon.get(c, []):
                if c1.isa(cls):
                    return True
        return False

    ## Daughter sets
    def make_daughter_sets(self):
        """This happens during finalization."""
        for abbrev, lexdim in self.dims.items():
            labels = set()
            # Check the possible daughter arcs for the lexdim
            outs = lexdim.attribs.get('outs')
            if outs:
                for label, char in outs.items():
                    if char:
                        label_int = self.language.get_label_int(label, abbrev)
                        # Ignore labels with 0 as char
                        labels.add(label_int)
                lexdim.attribs['daughs'] = labels

    ## Crosslexes

    def get_crosslexes(self, lang_abbrev, setit=True):
        """Get the list of Crosslex instances for entries corresponding to this one in
        language with lang_abbrev."""
#        if lang_abbrev == self.language.abbrev:
#            print('{} attempting to get crosslexes to own language!'.format(self))
        crosslexes = self.crosslexes.get(lang_abbrev)
        if crosslexes:
            return crosslexes
        if setit:
            self.init_crosslexes(lang_abbrev)
            return self.crosslexes[lang_abbrev]
        return None

    def init_crosslexes(self, lang_abbrev):
        self.crosslexes[lang_abbrev] = []

    def add_crosslex(self, lang_abbrev, lex_key, index, lexdim, targdim,
                     bidir=False, count=1):
        """Add a crosslex for language with lang_abbrev and entry lex."""
#        print('Add xlex', lang_abbrev, lex_key, index, lexdim, targdim)
        index = index if isinstance(index, list) else [index]
        for i in index:
            Crosslex(self,
                     targ_lang_abbrev=lang_abbrev,
                     targ_lex_key=lex_key,
                     targ_lex_index=i,
                     lexdim=lexdim,
                     targdim=targdim,
                     bidir=bidir,
                     count=count)
#        return xlex

    def add_emptycrosslex(self, lang_abbrev, slex_key, sindex, tlex_key, tindex,
                          agrs=None, rel=None, ifdim=None,
                          empty_cond=None,
                          count=1):
        xlex = EmptyCrosslex(self,
                             empty_lex_key=slex_key, empty_lex_index=sindex,
                             targ_lang_abbrev=lang_abbrev,
                             targ_lex_key=tlex_key,
                             targ_lex_index=tindex,
                             empty_cond=empty_cond,
                             agrs=agrs, rel=rel, if_dim=ifdim, count=count)
        return xlex

    def add_revemptycrosslex(self, empty_lang_abbrev,
                             empty_lex_key, empty_lex_index,
                             insert_lex_key, insert_lex_index,
                             if_dim, arc_label, rel=None, count=1):
        xlex = RevEmptyCrosslex(self,
                                empty_lang_abbrev=empty_lang_abbrev,
                                empty_lex_key=empty_lex_key, empty_lex_index=empty_lex_index,
                                empty_lex=None,
                                insert_lex_key=insert_lex_key, insert_lex_index=insert_lex_index,
                                insert_lex=None,
                                if_dim=if_dim,
                                rel=rel,
                                arc_label=arc_label,
                                count=count)
        return xlex

    def add_finalized_crosslex(self, lang_abbrev, target_entry, lexdim,
                               targ_lex_index=0,
                               count=1, flatten=False):
        """Add a finalized crosslex (already has the entry); if flatten, then
        assign no target lex. Used to create crosslex in opposite direction from
        the one given explicitly in the lexicon."""
#        print('Adding finalized xlex', lang_abbrev, self, target_entry, lexdim)
        xlex = Crosslex(self,
                        targ_lang_abbrev=lang_abbrev,
                        targ_lex=target_entry if not flatten else None,
                        targ_lex_key=target_entry.name,
                        targ_lex_index=targ_lex_index,
                        lexdim=lexdim,
                        bidir=False,
                        count=count)
        xlex.targ_lang = target_entry.language
        return xlex

    def update_crosslex_entry(self, lexdim):
#        """Create a clone of a target language lex along with its associated lexdim."""
        """Make the lexdim in the crosslex the lexdim of the entry."""
        if lexdim:
            dim = lexdim.dim
            if not self.dims.get(dim):
                # This may already have happened
                self.set_lexdim(dim, lexdim)
#                print(' Updating crosslex entry', self, 'with', lexdim)
#            else:
#                print(' {} already has a lexdim {}'.format(self, self.dims.get(dim)))
        self.crosslex = True

    ## Groups

    def proc_group_lex(self, gid):
        """Modify lex to include group information."""
        self.gid = gid
        self.gids[self.language.abbrev] = gid
        for dim in self.dims.values():
            for attrib, value in dim.attribs.items():
                if attrib in ['groupouts']:
                    # Assume the value is a list; turn it into a dict
                    dim.attribs[attrib] = {v: gid for v in value}

    @staticmethod
    def val_prec(v1, v2):
        '''Does valency value v1 have precedence over v2?'''
        return Lex.valency.index(v1) < Lex.valency.index(v2)

    def describe(self):
        '''Print out attributes in all of the lex's lexdims.'''
        print(self)
        if self.crosslexes:
            for lang, cs in self.crosslexes.items():
                print('  {}: {}'.format(lang, cs))
        for dlabel, dim in self.dims.items():
            print('  {}'.format(dlabel))
            for attrib, value in dim.attribs.items():
                print('    {}: {}'.format(attrib, value))

    def inherit(self, lexicon, languages, inh_lexicon=None, between=True, clone=False):
        """Explicitly inherit attributes from all ancestors of self.
        Used only in flattening."""
        if clone:
            copy = self.clone(lexicon=lexicon)
        else:
            copy = self
        entries = [copy]
        inh_lexicon = inh_lexicon or self.lexicon
        inh_lexicon.inherit(copy, self.language.dimensions,
                            add_entries=entries,
                            languages=languages,
                            target_languages=[], copy_xtarg=False,
                            transfer_xlex=False, set_prob=False,
                            flatten=True, within=True, between=between,
                            verbosity=0)
        return entries

    def inherit_properties(self, cls, dim_abbrevs, language, flatten=False,
                           between=True, process=PARSE, copy_xtarg=True,
                           languages=None, is_source=True, verbosity=0):
        """Inherit properties of cls to this Lex for each dimension.

        @param  cls: a lexical class of this Lex
        @type   cls: instance of Lex representing a lexical class
        @param  dim_abbrevs: list of dimensions
        @type   dim_abbrevs: list of strings
        @param  language: language of this entry
        @type   language: Language
        @param  is_source: whether the language is the source language
        @type   is_source: boolean
        """
        languages = languages or []
        # Check whether self has already inherited from this class, but allow multiple inheritance
        # for crosslex classes (why??)
        if any([cls.equals(c) for c in self.inh_classes]):
            if verbosity > 1:
                print(' ', self, 'already has', cls, 'in its inherited classes', self.inh_classes)
            return False
        if verbosity > 1:
            print('  {} inheriting properties from {}'.format(self, cls))
            print('    Language {}, dimensions {}'.format(language, dim_abbrevs))
            print('    Source? {}'.format(is_source))
        # First inherit cross-dimensional properties if this is between
        if cls.crosslexes:
            for lg_abbrev, xlexes in cls.crosslexes.items():
                # The generation case: process is GENERATE and lg_abbrev is 'sem'
                # Inherit only reverse empty crosslexes back to semantics
                if not flatten and (process == GENERATE and lg_abbrev == 'sem'):
                    target_abbrev = languages[0]
                    for xlex in xlexes:
                        if xlex.empty and xlex.reverse:
                            if target_abbrev not in self.crosslexes:
                                self.crosslexes[target_abbrev] = []
                            current_xlex = self.crosslexes[target_abbrev]
                            current_xlex.append(xlex.clone())
                # All other cases
                elif languages == 'all' or lg_abbrev in languages:
                    if lg_abbrev != self.language.abbrev:
                        if lg_abbrev not in self.crosslexes:
                            self.crosslexes[lg_abbrev] = []
                        current_xlex = self.crosslexes[lg_abbrev]
                        if flatten:
                            if cls.is_lexical():
                                # No current xlex but since class is lexical, clone xlexes and append
                                for xlex in xlexes:
                                    current_xlex.append(xlex.clone(source=self, copy_targ=False))
                            else:
                                for xlex in xlexes:
                                    if xlex.empty:
                                        # Class xlex is empty or reverse empty; create a new xlex in child
                                        current_xlex.append(xlex.clone(copy_targ=False))
                                    elif current_xlex:
                                        for child_xlex in current_xlex:
                                            if not child_xlex.empty:
                                                child_xlex.merge(xlex, self)
                                    else:
                                        # No xlex in child so nothing to merge with class xlex
                                        continue
                            # For flattening inheritance, clone the crosslexes first
                        else:
                            unique = Crosslex.unique(current_xlex + xlexes)
                            self.crosslexes[lg_abbrev] = unique
        # Inherit group id
        if cls.gid:
            if not self.gid:
                self.gid = cls.gid
            self.gids[language.abbrev] = cls.gid
        # Inherit crosslex count if this is between languages
        if between and cls.xcount:
            self.xcount += cls.xcount
        # Add the class to the list of inherited classes for the lex if it's in the same language
        if is_source:
            self.inh_classes.append(cls)
        # Add the list of disjoint classes
        self.disjoint.extend(cls.disjoint)
        # Add to the list of empty daughter entry classes, but only do this for the source
        # language
        if is_source and cls.empty_daughs:
            for d in cls.empty_daughs:
                if d not in self.empty_daughs:
                    if not isinstance(d, str):
                        d = d.name
                    self.empty_daughs.append(d)
        # Inherit word name properties
        lg_abbrev = language.abbrev
        lg_names = self.names.get(lg_abbrev, {})
        cls_names = cls.names.get(lg_abbrev, {})
        changed = False
        for lab in ['word', 'lexeme', 'gram', 'root', 'pos', 'label']:
            # Don't replace a name from a lower entry
            if lab == 'gram' and flatten:
                continue
            if lab not in lg_names:
                attr = getattr(cls, lab) or cls_names.get(lab)
                # The attr could be None
                if attr:
                    if attr == '*':
                        # What to do with unknown entries in target languages
                        if self.name:
                            lg_names['name'] = self.name
                            lg_names[lab] = '*'
                            changed = True
#                            lg_names[lab] = self.name
                    else:
                        changed = True
                        lg_names[lab] = attr
        if changed:
#            print('lg names: {}'.format(lg_names))
            self.names[lg_abbrev] = lg_names

        # Then inherit dimensional properties
        for dim_abbrev in dim_abbrevs:
            inh_dim_abbrev = dim_abbrev
            cls_lexdim = cls.dims.get(dim_abbrev)
            # Only update if class has something for this dimension
            if cls_lexdim:
                lexdim = self.dims.get(inh_dim_abbrev)
                if not lexdim:
                    # The language for this LexDim can disagree with the Lex language
                    lexdim = LexDim(label=inh_dim_abbrev, lex=self, dim=dim_abbrev,
                                    language=language)
                    self.set_lexdim(inh_dim_abbrev, lexdim)
                # Inherit int attributes
                for int_attrib in ['inmin', 'outmin', 'inmax', 'outmax']:
                    # For each of these, ignore the class if there's already a value for the attrib; otherwise inherit
                    # the class attribute.
                    if int_attrib in cls_lexdim.attribs:
                        existing_attrib = lexdim.attribs.get(int_attrib, None)
                        if existing_attrib is None:
                            # (Could be 0)
                            # Inherit class attribute
                            lexdim.attribs[int_attrib] = cls_lexdim.attribs[int_attrib]
                            
                # Inherit dict attributes
                for dict_attrib in ['arg', 'argrev', 'ldend', 'laend', 'lbstart', 'lb12s', 'lab12s', 'labs', 'lbend', 'mod']:
                    # First linking attributes, treated specially for each dim2 label, there can only by one constraint.
                    # When there is a conflict, give priority to word or lexeme entries, deleting constraints already
                    # inherited from gram entries, if any.
                    if dict_attrib in cls_lexdim.attribs:
                        # Getting existing linking constraints; put in a dict with features (dim2 arcs) as keys
                        existing_attribs = [(a, lexdim.attribs[a]) for \
                                                a in ['arg', 'argrev', 'ldend', 'laend', 'lbstart', 'lbend', 'lb12s', 'lab12s', 'labs', 'mod']\
                                                if a in lexdim.attribs]
                        link_attrib_dct = {}
                        for a, att in existing_attribs:
                            for f in att.keys():
                                link_attrib_dct[f] = (a, att)
                        if dict_attrib not in lexdim.attribs:
                            lexdim.attribs[dict_attrib] = {}
                        lexdim_dict = lexdim.attribs[dict_attrib]
                        for feat, val in cls_lexdim.attribs[dict_attrib].items():
                            if feat in link_attrib_dct:
                                # This feat (dim2 label) is already in a linking constraint
                                if cls.word or cls.lexeme:
                                    # The current constraint has priority because it's in a
                                    # word or lexeme entry, so delete the old one from lexdim.attribs
                                    attrib, feat_val = link_attrib_dct[feat]
                                    del feat_val[feat]
                                    if not lexdim.attribs[attrib]:
                                        # The linking constraint attrib is now empty, so delete it too
                                        del lexdim.attribs[attrib]
                            if feat not in lexdim_dict:
                                # Inherit the new value if there's no current value
                                lexdim_dict[feat] = val
                            # Otherwise leave the old value

                # Other dict attributes
                for dict_attrib in ['ins', 'outs', 'groupouts', 'govern', 'crossgov', 'cross', 'merge', 'arcagree']:
                    if dict_attrib in cls_lexdim.attribs:
                        if dict_attrib not in lexdim.attribs:
                            lexdim.attribs[dict_attrib] = {}
                        lexdim_dict = lexdim.attribs[dict_attrib]
                        for feat, val in cls_lexdim.attribs[dict_attrib].items():
                            if feat not in lexdim_dict:
                                # Inherit the new value if there's no current value
                                lexdim_dict[feat] = val
                            elif dict_attrib in ['ins', 'outs'] and Lex.val_prec(val, lexdim_dict[feat]):
                                # Inherit a new valency value if it has precedence over the old value
                                lexdim_dict[feat] = val
                            elif dict_attrib == 'govern':
                                # Add whatever new feat-value pairs are present for the "feat" (arc)
                                # Merge the old and new lists
                                oldvalues = set(lexdim_dict[feat])
                                oldvalues.update(val)
                                lexdim_dict[feat] = list(oldvalues)
                            # Otherwise leave the old value

                # Inherit set attributes
                for set_attrib in ['order', 'agree', 'dagree', 'proj', 'blocks', 'ordereq', 'daughs']:
                    if set_attrib in cls_lexdim.attribs:
                        if set_attrib not in lexdim.attribs:
                            lexdim.attribs[set_attrib] = set()
                        lexdim_list = lexdim.attribs[set_attrib]
                        for attrib in cls_lexdim.attribs[set_attrib]:
                            if set_attrib == 'agree':
                                lab = attrib[0]
                                # See if out arcs for label are not possible
                                if lexdim.attribs.get('outs', {}).get(lab) == 0:
                                    continue
                            # Lower class has priority
                            if attrib not in lexdim_list:
                                lexdim_list.add(attrib)

                # agrs is special because the lex and class FSs need "unify"
                cls_agrs = cls_lexdim.attribs.get('agrs')
                if cls_agrs:
                    # "Feature structures" are tuples of integers
                    if 'agrs' not in lexdim.attribs:
                        lexdim.attribs['agrs'] = {}
                    agrs = lexdim.attribs.get('agrs')
                    # The value of agrs is a dict of label strings with sets of FSs
                    # as values
                    for feat, valueS in cls_agrs.items():
                        # Priority to lexeme/word over class
                        if feat not in agrs:
                            agrs[feat] = valueS.copy()
                        else:
                            new_value = unify_fssets(valueS, agrs[feat])
                            agrs[feat] = new_value
        return True

    def class_compatible(self, cls, dimensions, verbosity=0):
        '''Is lex class cls compatible with this lex?

        That is, does the agrs attribute in this lex unify
        with that in the class, and are the outs attributes compatible?'''
        # First check on whether the class is disjoint with this lex
        if self.is_disjoint(cls):
            return False
        # Check compatible on each dimension
        for dim_abbrev in dimensions:
            lexdim, cls_lexdim = self.dims.get(dim_abbrev), cls.dims.get(dim_abbrev)
            if cls_lexdim and lexdim:
                agrs, cls_agrs = lexdim.attribs.get('agrs', {}), cls_lexdim.attribs.get('agrs', {})
                outs, cls_outs = lexdim.attribs.get('outs', {}), cls_lexdim.attribs.get('outs', {})
#                if agrs or cls_agrs:
#                    print(self, cls, 'Agrs', agrs, 'cls_agrs', cls_agrs)
                if cls_agrs:
                    if agrs:
                        if verbosity > 1:  print('  Unifying',  cls_agrs,  'and', agrs)
                        # go through agrs and cls_agrs dictionaries making sure corresponding features match
                        for cls_feat, cls_val in cls_agrs.items():
                            agrs_val = agrs.get(cls_feat)
                            if agrs_val:
                                unification = unify_fssets(agrs_val, cls_val)
                                if not unification:
                                    if verbosity > 1:
                                        print('Dimension', dim_abbrev, lexdim, cls_lexdim,
                                              lexdim.language, cls_lexdim.language)
                                        s = "{} not compatible with {} because {} and {} don't agree"
                                        print(s.format(self, cls, agrs, cls_agrs))
                                    return False
                if cls_outs:
                    for arc, constraint in cls_outs.items():
                        if arc in outs:
                            lower_constraint = outs[arc]
                            if lower_constraint == 0:
                                # 0 isn't compatible with !
                                # What were %, %!, and %% about?
                                if constraint in ['!']:  # , '%', '%!', '%%']:
                                    if verbosity > 1:
                                        print('Dimension', dim_abbrev, lexdim, cls_lexdim,
                                              lexdim.language, cls_lexdim.language)
                                        s = "{} not compatible with {} because {} and {} don't agree"
                                        print(s.format(self, cls, lower_constraint, constraint))
                                    return False
                            # Other combinations (?, !, *) are compatible
        return True

    ## Use these two methods to set list of disjoint classes for members of partition.

    @staticmethod
    def prune_disjoint(lex, disj, tree):
        lex.disjoint = disj[:]
        for d in disj:
            if Lex.ISA(lex, d, tree) or Lex.ISA(d, lex, tree):
                lex.disjoint.remove(d)

    @staticmethod
    def ISA(lex, cls, tree):
        if lex == cls:
            return True
        classes = tree.get(lex, [])
        for c in classes:
            if Lex.ISA(c, cls, tree):
                return True
        return False

    @staticmethod
    def from_dict(dct, lang_prefix='', language=None, lexicon=None):
        """Create a Lex from the dict in a lexicon YAML representation. Treat partitions and 'ordinary'
        entries differently.
        This is ugly, but it seems to work. It allows nesting of partitions to only two levels, but
        beyond that would probably be confusing (in the YAML file) anyway.
        """
        if 'partition' in dct:
            # This specifies a partition; all created lexes are returned
            # The superclass can be either a gram or a lexeme
            category = 'gram'
            if 'gram' not in dct and 'lexeme' in dct:
                category = 'lexeme'
            lexes = []
            # The lexes in the partition (excluding shared lexes)
            partition = []
            name = dct.get(category)
            if not name:
                print('category', category, 'dct', dct)
            shared_name = name + '!'
            any_shared = 'shared' in dct
            # Tree to represent the inheritance hierarchy within the partition
            tree = {}
            # The lexes directly under the shared_lex
            lexes1 = []
            # Crosslexes need to be copied in all partition parts
            shared_cross = {}
            # Keys include "gram", "lexeme", "shared", and "partition"
            for k, v in dct.items():
                if k == 'partition':
                    # v is a list of Lex specifications
                    for lex in v:
                        if 'subpartition' in lex:
                            # A subpartition of the partition; a dictionary with
                            # 'shared' and 'subclasses' keys (as well as 'subpartition')
                            subshared_name = lex['subpartition']
                            subshared_lex_spec = lex['shared']
                            subshared_lex_spec['gram'] = subshared_name
                            subshared_classes = subshared_lex_spec.get('classes', [])
                            if any_shared:
                                subshared_classes.append(shared_name)
                            subshared_lex_spec['classes']= subshared_classes
                            subshared_lex = Lex.from_dict(subshared_lex_spec, lang_prefix=lang_prefix,
                                                          language=language, lexicon=lexicon)
                            lexes.extend(subshared_lex)
                            partition.extend(subshared_lex)
                            lexes1.extend(subshared_lex)
                            # The lexes under subshared_lex
                            sublexes = []
                            for sublex in lex['subclasses']:
                                if 'subpartition' in sublex:
                                    # One more level of nesting possible...
                                    anysubpartition = True
                                    subsubshared_name = sublex['subpartition']
                                    subsubshared_lex_spec = sublex['shared']
                                    subsubshared_lex_spec['gram'] = subsubshared_name
                                    subsubshared_classes = subsubshared_lex_spec.get('classes', [])
                                    # Add shared and subshared to classes of subsubshared
                                    subsubshared_classes.append(subshared_name)
#                                    if any_shared:
#                                        subsubshared_classes.append(shared_name)
                                    subsubshared_lex_spec['classes'] = subsubshared_classes
                                    subsubshared_lex = Lex.from_dict(subsubshared_lex_spec, lang_prefix=lang_prefix,
                                                                     language=language, lexicon=lexicon)
                                    lexes.extend(subsubshared_lex)
                                    partition.extend(subsubshared_lex)
                                    sublexes.extend(subsubshared_lex)
                                    # The lexes under subsubshared_lex
                                    subsublexes = []
                                    for subsublex in sublex['subclasses']:
                                        subsublex['gram'] = name
                                        subsublex_classes = subsublex.get('classes', [])
                                        subsublex_classes.append(subsubshared_name)
#                                        if any_shared:
#                                            subsublex_classes.append(shared_name)
                                        subsublex['classes'] = subsublex_classes
                                        subsublex = Lex.from_dict(subsublex, lang_prefix=lang_prefix, language=language,
                                                                  lexicon=lexicon)
                                        lexes.extend(subsublex)
                                        partition.extend(subsublex)
                                        subsublexes.extend(subsublex)
                                    tree[subsubshared_lex[0]] = subsublexes
                                else:
                                    sublex['gram'] = name
                                    sublex_classes = sublex.get('classes', [])
                                    sublex_classes.append(subshared_name)
                                    sublex['classes'] = sublex_classes
                                    sublex = Lex.from_dict(sublex, lang_prefix=lang_prefix, language=language,
                                                           lexicon=lexicon)
                                    lexes.extend(sublex)
                                    partition.extend(sublex)
                                    sublexes.extend(sublex)
                            tree[subshared_lex[0]] = sublexes
                        else:
                            if 'lexeme' in lex:
                                lex['lexeme'] = name
                            else:
                                lex['gram'] = name
#                            lex[category] = name
                            if any_shared:
                                lex['classes'] = lex.get('classes', []) + [shared_name]
    #                    print('Creating partition sublex', lex['label'])
                            sublex = Lex.from_dict(lex, lang_prefix=lang_prefix, language=language,
                                                   lexicon=lexicon)
#                            print('Partition element {}, sublex {}'.format(name, sublex))
                            sublex[0].partitions.append(name)
                            lexes.extend(sublex)
                            partition.extend(sublex)
                            lexes1.extend(sublex)
                elif k == 'shared':
                    # v is a Lex specification without a name
                    v[category] = shared_name
    #                print('Creating shared lex for partition', shared_name)
                    if 'cross' in v:
                        # Crosslexes are associated with partition parts, not
                        # with shared parent
                        shared_cross1 = v['cross']
                        shared_cross.update(shared_cross1)
                        # Remove 'cross' from the shared lex dict
                        del v['cross']
                    shared_lex = Lex.from_dict(v, lang_prefix=lang_prefix, language=language,
                                               lexicon=lexicon)
                    lexes.extend(shared_lex)
                elif k == category:
                    pass
                else:
                    print('WARNING: lexicon key {} not interpretable'.format(k))
            tree[shared_lex[0]] = lexes1
            # Record the list of lexes in each lexes disjoint attrib
            for lex in partition:
                Lex.prune_disjoint(lex, partition, tree)
                if shared_cross:
                    # Add the shared crosslexes to each partition part
                    Lex.cross_from_dict(shared_cross, lex, language=language)
#            if shared_cross:
#                print('Shared cross', shared_cross, 'partition', partition)
#            print('Partition {}, all lexes {}'.format(partition, lexes))
            return lexes
        else:
            if dct.get('morph*'):
                # Entry already defined elsewhere to use in partition
                name = dct['morph*']
#                print('Empty morph copy {}'.format(name))
                lex = lexicon.get(name)
#                print('Found original lex {}'.format(lex))
                lex[0].part = True
                return lex
            # The dct specifies a regular entry
            # First check to see if it's a "lexeme*" entry, in which
            # case a copy of an existing lexeme is made
            lexeme_copy = dct.get('lexeme*')
            if lexeme_copy:
                lexes = lexicon.copy_disjoint_lexeme(lexeme_copy)
            else:
                lexes = [Lex(language=language)]
            for lex in lexes:
                # First assign the part of label name
                if 'part' in dct:
                    v = dct.get('part')
                    lex.gram = v
                    lex.label = v
                    lex.part = True
                    del dct['part']
                if 'label' in dct:
                    v = dct.get('label')
                    lex.gram = v
                    lex.label = v
                    lex.part = True
                    del dct['label']
                # Then handle all of the other attributes
                for k, v in dct.items():
                    if k == 'lexeme*' or k == 'morph*':
                        continue
                    if v == None:
                        v = {}
                    if k == 'cross':
                        Lex.cross_from_dict(v, lex, language=language)
                    elif k == 'empty':
                        # Create empty daughters for these entry classes
                        lex.empty_daughs = v
                    else:
                        # Check to see whether k is one of the dimension abbreviations
                        dim_abbrev = language.make_dim_long(k)
                        if dim_abbrev:
#                            print('Lex', lex, 'has dim', dim_abbrev)
                            lexdim = LexDim.from_dict(v, language=language)
                            lexdim.dim = dim_abbrev
                            lexdim.lex = lex
                            lex.set_lexdim(dim_abbrev, lexdim)
                        # k is not a dimension; assign it to entry as an attribute
                        elif k == 'morph':
                            lex.word = v
                            lex.part = True
                        elif k == 'wordpart':
                            lex.word = v
                            lex.part = True
                        elif k == 'lexemepart':
                            lex.lexeme = v
                            lex.part = True
                        elif k == 'grampart':
                            lex.gram = v
                            lex.part = True
                        else:
                            setattr(lex, k, v)
                # Make sure the lex has a name
                if not lex.name:
                    lex.name = lex.word or lex.lexeme or lex.gram
            # Return a list to make it compatible with partition cases
            return lexes

    @staticmethod
    def cross_from_dict(dct, lex, language=None):
        # dct is a dict of form {lang_abbrev: <crosslex or crosslex_list>}
        for lang_abbrev, crosslexes in dct.items():
            if not isinstance(crosslexes, list):
                crosslexes = [crosslexes]
            for crosslex in crosslexes:
                if 'revempty' in crosslex:
                    # Reverse empty crosslexes: used when target contains node
                    # not found in non-target (usually Semantics)
                    empty_lex_key = crosslex.get('elex', 'zero')
                    empty_lex_index = crosslex.get('eindex', 0)
                    insert_lex_key = crosslex['inslex']
                    insert_lex_index = crosslex.get('iindex', None)
                    if_dim = crosslex.get('ifdim')
                    arc_label = crosslex.get('arc')
                    rel = crosslex.get('rel')
                    count = crosslex.get('count', 1)
                    lex.add_revemptycrosslex(lang_abbrev,
                                             empty_lex_key, empty_lex_index,
                                             insert_lex_key, insert_lex_index,
                                             if_dim, arc_label, rel, count=count)
                elif 'empty' in crosslex:
                    # Keys in empty crosslex dict: 'slex', 'tlex', 'sindex', 'tindex'
                    #   'ins', 'agrs', 'rel', 'ifdim'
                    targ_lex = crosslex['tlex']
                    src_lex = crosslex.get('slex', 'zero')
                    targ_index = crosslex.get('tindex', 0)
                    src_index = crosslex.get('sindex', 0)
                    agrs = crosslex.get('agrs')
                    rel = crosslex.get('rel')
                    ifdim = crosslex.get('ifdim')
                    empty_cond = crosslex.get('cond')
                    count = crosslex.get('count', 1)
#                    print('Cross from dict {}, {}, {}, {}, {}'.format(lex, language, lang_abbrev, ifdim,
#                                                                  empty_cond))
                    lex.add_emptycrosslex(lang_abbrev,
                                          src_lex, src_index, targ_lex, targ_index,
                                          agrs=agrs, rel=rel, ifdim=ifdim,
                                          empty_cond=empty_cond,
                                          count=count)
                else:
                    # Keys in crosslex dict: 'lex', 'index', 'bidir', dimension abbrevs
                    # Entry must also be present
                    other_lex = crosslex['lex']
                    # Index of other lex defaults to 0
                    index = crosslex.get('index', 0)
                    # Whether the crosslex should be bidirectional (the default)
                    bidir = crosslex.get('bidir', False)
                    # How many times this crosslex has occurred
                    count = crosslex.get('count', 1)
                    # There may be no LexDims, just a corresponding entry
                    lexdim = None
                    # There may be at most one target dimension, an arc dimension in the target lex
                    targdim = None
                    # Find any lexdim and target dim
                    for key, constraints in crosslex.items():
                        if key in DIMENSIONS['if']:
                            # an interface dimension attribute
                            dim_abbrev = language.make_dim_long(key)
                            if dim_abbrev:
                                lexdim = LexDim.from_dict(constraints, language=language)
                                lexdim.dim = dim_abbrev
                                lexdim.lex = lex
                        elif key in DIMENSIONS['arc']:
#                            print('key {}, constraints {}, lex {}, dims {}'.format(key, constraints, lex, lex.dims))
                            # A dimension in the target language for which something is to be
                            # constrained
                            name = key if lang_abbrev == 'sem' else lang_abbrev + '-' + key
                            # Create a temporary dimension later to merged with the corresponding
                            # dimension in the target lex
                            targdim = LexDim.from_dict(constraints)
                            targdim.dim = name
                                
                    lex.add_crosslex(lang_abbrev, other_lex, index, lexdim, targdim,
                                     bidir=bidir, count=count)

class LexDim:
    """Class for lexical specifications for particular dimensions.
    attributes are kept in a dict (attribs). Possibly keys are
    ins, outs, blocks, agree, order, groupouts, agrs, govern,
    cross, merge, arg, argrev, ldend, ...
    """

    def __init__(self, label='', name='', language=None, lex=None, dim='',
                 empty=False, attribs=None):
        """
        @param label:     string label for the dimension type
        @param name:      string name for the word on this dimension,
                          e.g., when semantics needs to be labeled differently
                          or when the dimensions represent different languages
        @param language:  the Language associated with this lexdim (not normally
                          assigned in the constructor)
        @param lex:       this lexdim's lexical entry (instance of Lex)
        @param dim:       string abbreviation of this lexdim's dimension
        @param empty:     whether this LexDim has no surface form
        @param attribs:   dict of attributes and values, e.g., outs, order
        """
        self.label = label or ''
        self.name = name or ''
        self.language = language
        self.lex = lex
        self.dim = dim
        self.empty = empty
        self.attribs = attribs or {}
        
    def __repr__(self):
        if self.lex:
            return '{}_{}'.format(self.lex.__repr__() if self.lex else '', self.dim)
        else:
            return '**{}'.format(self.dim)

    def clone(self, lex=None):
        """Make a copy of this LexDim."""
        copied = LexDim(label=self.label, name=self.name, language=self.language,
                        lex=lex or self.lex, dim=self.dim, empty=self.empty,
                        attribs=copy.deepcopy(self.attribs))
        return copied

    @staticmethod
    def from_dict(dct, language=None):
        """Create a LexDim from a dict in a yaml lexicon representation."""
        lexdim = LexDim(language=language)
        lexdim.attribs = dct
        lexdim.fix_attribs()
        return lexdim

    def fix_attribs(self):
        """Change types of some attribute values from those that are read in from YAML files."""
        for attrib, value in self.attribs.items():
            val_type = type(value)
            # YAML attrib values can be
            # Lists:
            if val_type == list:
                #  of strings                      (blocks, ordereq)
                if value and isinstance(value[0], str):
                    self.attribs[attrib] = set(value)
                #  of lists of strings             (agree, order, dagree)
                elif value and isinstance(value[0], list):
                    # Change the list to a set of tuples
                    self.attribs[attrib] = set([tuple(x) for x in value])
            # Dicts:
            elif val_type == dict:
                for attrib1, value1 in value.items():
                    if attrib == 'agrs' and isinstance(value1, int):
                        # A single agreement value; make it a set of a 1-element tuple
                        value[attrib1] = {(value1,)}
                    elif value1 and isinstance(value1, list):
                        #  value1: [ ]
                        # govern's value1 for each dict key (arc) could be a single feat/val list
                        # or a list of feat/val lists
                        if attrib == 'govern':
                            value1ls = value1
                            if isinstance(value1[0], str):
                                value1ls = [value1]
                            for i1, fv in enumerate(value1ls):
                                for i2, x in enumerate(fv):
                                    # Replace any lists inside the list with tuples
                                    # Currently only one value possible for a feature,
                                    # for example, cat for the arg1 of a verb in Semantics
                                    if isinstance(x, list):
                                        # Later fix it so that there can be multiple values
                                        # for the governed feature; for now only one is
                                        # possible (x)
#                                        if isinstance(x[0], list):
#                                            x = [tuple(y) for y in x]
                                        fv[i2] = tuple(x)
                                    elif isinstance(x, int):
                                        # x is an int representing a value for the governed
                                        # feature
                                        fv[i2] = (x,)
                                    # Otherwise x is the name of the feature
                                value1ls[i1] = tuple(fv)
                            value[attrib1] = value1ls
                        #  value1: [[int...]...]           (agrs)
                        elif isinstance(value1[0], list):
                            value[attrib1] = set(tuple(x) for x in value1)
                        #  value1: [string...]             (govern, cross, merge, arg, argrev, ldend, ...)
                        elif isinstance(value1[0], str):
                            for i, x in enumerate(value1):
                                # Replace any lists inside the list with tuples
                                if isinstance(x, list):
                                    value1[i] = tuple(x)
                            value[attrib1] = tuple(value1)
                        #  value1: [True, False, ...]
                        elif isinstance(value1[0], bool):
                           # Convert boolean to int
                            value[attrib1] = {int(value1[0])}
                        #  value1: [int, ...]
                        #  Value is already ints, but we need a set of ints (for agrs)
                        elif isinstance(value1[0], int):
                            value[attrib1] = set(value1)
            # If value is already a set, do nothing
            elif val_type == set:
                continue
            # A few attributes (inmax, etc.) have int values
            elif val_type == int:
                continue
            else:
                print('Value', value, 'is neither list nor dict')

    def get_attrib(self, label):
        # But not all attributes have list values
        return self.attribs.get(label, [])

    def get_max_card(self, direction):
        """Maximum number of in or out arcs."""
        return self.attribs.get('inmax', MAX_CARD) if direction == 'in' else self.attribs.get('outmax', MAX_CARD)

    def get_label_card_bounds(self, label, direction):
        """Return min and max cardinality and then soft min and max cardinality."""
        dct = self.attribs.get('ins', {}) if direction == 'in' else self.attribs.get('outs', {})
        card = dct.get(label, 0)
#        print('Getting label cards', self, label, direction, dct, card)
        if card == '!':
            return 1, 1, 1, 1
        elif card == 0:
            return 0, 0, 0, 0
        elif card == '!?':
            return 1, 1, 0, 1
        elif card == '0?':
            return 0, 0, 0, 1
        elif card == '?':
            return 0, 1, 0, 1
        else:
            maxim = self.get_max_card(direction)
            if card == '*':
                return 0, maxim, 0, maxim
            elif card == '+':
                return 1, maxim, 1, maxim
            else:
                ValueError('Unknown cardinality: {}'.format(card))

    def get_label_card(self, label, direction, soft=False):
        """Return cardinality for label as a set of ints.
        Only for dimensions with in and out constraints."""
        dct = self.attribs.get('ins', {}) if direction == 'in' else self.attribs.get('outs', {})
        card = dct.get(label, 0)
        if card == '!' or card == '!?':
            return {1}
        elif card == 0 or card == '0?':
            return {0}
        else:
            maxim = self.get_max_card(direction)
            if card == '?':
                return {0, 1}
            elif card == '*':
                return set(range(maxim))
            elif card == '+':
                return set(range(1, maxim))
            else:
                ValueError('Unknown cardinality: {}'.format(card))

    def record_agreement(self, language=None):
        self.record_agrs(language=language)
        self.record_agree(language=language)

    def record_agrs(self, language=None):
        """Record the agrs attributes of this LexDim in the language."""
        lang = language or self.language
        lg_agrs = lang.agrs
        # This is where we can add () to every feature set or not
        for feat, values in self.attribs.get('agrs', {}).items():
#            print('Recording agrs', feat, values)
            # Update values already associated with feat
            lg_agrs[feat] = lg_agrs.get(feat, set()).union(values)
#            print('  Current value', lg_agrs[feat])
        # Also record values in govern attribute
        for featvalues in self.attribs.get('govern', {}).values():
            for feat, value in featvalues:
#                print('Recording gov agrs', feat, value)
                lg_agrs[feat] = lg_agrs.get(feat, set()).union({value})
#                print('  Current value', lg_agrs[feat])

    def record_agree(self, language=None):
        """Record the agree attributes of this LexDim in the language."""
        lang = language or self.language
        lg_agree = lang.agree_triples
#        lg_dagree = lang.dagree_tuples
        lg_ifagree = lang.ifagree_pairs
        lg_govern = lang.govern_triples
        lg_lab_dfeats = lang.labeldfeats
        lg_gov_lab_dfeats = lang.govlabeldfeats
        for feats in self.attribs.get('agree', []):
            if len(feats) == 3:
                # Standard agreement
                if feats not in lg_agree:
                    lg_agree.append(feats)
                lg_dfeat = feats[0], feats[2]
                if lg_dfeat not in lg_lab_dfeats:
                    lg_lab_dfeats.append(lg_dfeat)
            else:
                # Interface agreement
                if feats not in lg_ifagree:
                    lg_ifagree.append(feats)
                    #        for feats in self.attribs.get('dagree', []):
                    #            if (self.dim,) + feats not in lg_dagree:
                    #                lg_dagree.append((self.dim,) + feats)
        for label, featvals in self.attribs.get('govern', {}).items():
            for feat, value in featvals:
                if (label, feat, value) not in lg_govern:
                    lg_govern.append((label, feat, value))
                if (label, feat) not in lg_gov_lab_dfeats:
                    lg_gov_lab_dfeats.append((label, feat))

    def get_agree(self):
        """Convert set of string triples into set of int pairs.

        Used in AgreementPrinciple.
        """
        agree_strings = self.get_attrib('agree')
        agree_ints = set()
        for strings in agree_strings:
            agree_ints.add(self.language.agree_strings_to_ints(strings))
        return agree_ints

    def get_govern(self):
        """Convert set of string triples into set of int pairs.

        Used in GovernmentPrinciple.
        """
        gov_strings = self.get_attrib('govern') or {}
        gov_ints = set()
        for label, featvalues in gov_strings.items():
            for feat, value in featvalues:
                gov_ints.add(self.language.gov_strings_to_ints((label, feat, value)))
        return gov_ints

    def get_crossgovern(self):
        """Convert set of string triples into set of int pairs.

        Used in CrossGovernmentPrinciple.
        """
        gov_strings = self.get_attrib('crossgov') or {}
        gov_ints = set()
        for label, (feat, value) in gov_strings.items():
            gov_ints.add(self.language.crossgov_strings_to_ints((label, feat, value)))
        return gov_ints

    def record_attrib(self, attrib, value):
        """Add the value for this attribute to the attribs dict in language."""
        lg_attribs = self.language.lex_attribs
#        print('Record attrib, lg attribs {}; attrib {} -- value {}'.format(lg_attribs, attrib, value))
        if isinstance(value, list):
            value = tuple(value)
        lg_attrib = lg_attribs.get(attrib, set())
        if isinstance(value, dict):
            print('lg attrib {}, value {}'.format(lg_attrib, value))
        lg_attrib.add(value)
        lg_attribs[attrib] = lg_attrib

    def record_attribs(self):
        for attrib, value in self.attribs.items():
            if isinstance(value, dict):
                # Value is itself a dict of features and values
                # Ignore the features.
                for v1 in value.values():
                    # The subvalue could be a list of values
                    if isinstance(v1, set): # and isinstance(v1[0], tuple):
                        for v2 in v1:
                            self.record_attrib(attrib, v2)
                    else:
                        self.record_attrib(attrib, v1)
            elif isinstance(value, list) or isinstance(value, set):
                # Value is a list
                for v1 in value:
                    self.record_attrib(attrib, v1)
            else:
                pass

    def merge_attribs(self, lexdim, lexical=False):
        """Merge attributes in lexdim into this LexDim. lexical is whether the lex of lexdim is 'lexical'"""
        ## Inherit dict attributes
        for dict_attrib in ['arg', 'argrev', 'ldend', 'laend', 'lbstart', 'lbend', 'lb12s', 'lab12s', 'labs', 'mod']:
            # First linking attributes, treated specially. For each dim2 label, there can be only one constraint.
            # When there is a conflict, give priority to word or lexeme entries, deleting constraints already
            # inherited from gram entries, if any.
            if dict_attrib in lexdim.attribs:
                # Getting existing linking constraints; put in a dict with features (dim2 arcs) as keys
                existing_attribs = [(a, self.attribs[a]) for \
                                        a in ['arg', 'argrev', 'ldend', 'laend', 'lbstart', 'lbend', 'lb12s', 'lab12s', 'labs', 'mod']\
                                        if a in self.attribs]
                link_attrib_dct = {}
                for a, att in existing_attribs:
                    for f in att.keys():
                        link_attrib_dct[f] = (a, att)
                if dict_attrib not in self.attribs:
                    self.attribs[dict_attrib] = {}
                lexdim_dict = self.attribs[dict_attrib]
                for feat, val in lexdim.attribs[dict_attrib].items():
                    if feat in link_attrib_dct:
                        # This feat (dim2 label) is already in a linking constraint
                        if lexical:
                            # The current constraint has priority because it's in a
                            # word or lexeme entry, so delete the old one from self.attribs
                            attrib, feat_val = link_attrib_dct[feat]
                            del feat_val[feat]
                            if not self.attribs[attrib]:
                                # The linking constraint attrib is now empty, so delete it too
                                del self.attribs[attrib]
                    if feat not in lexdim_dict:
                        # Inherit the new value if there's no current value
                        lexdim_dict[feat] = val
                    # Otherwise leave the old value

        # Other dict attributes
        for dict_attrib in ['ins', 'outs', 'groupouts', 'govern', 'crossgov', 'cross', 'merge', 'arcagree']:
            if dict_attrib in lexdim.attribs:
                if dict_attrib not in self.attribs:
                    self.attribs[dict_attrib] = {}
                lexdim_dict = self.attribs[dict_attrib]
                for feat, val in lexdim.attribs[dict_attrib].items():
                    if feat not in lexdim_dict:
                        # Inherit the new value if there's no current value
                        lexdim_dict[feat] = val
                    elif dict_attrib in ['ins', 'outs'] and Lex.val_prec(val, lexdim_dict[feat]):
                        # Inherit a new valency value if it has precedence over the old value
                        lexdim_dict[feat] = val
                    elif dict_attrib == 'govern':
                        # Add whatever new feat-value pairs are present for the "feat" (arc)
                        # Merge the old and new lists
                        oldvalues = set(lexdim_dict[feat])
                        oldvalues.update(val)
                        lexdim_dict[feat] = list(oldvalues)
                    # Otherwise leave the old value

        # Inherit set attributes
        for set_attrib in ['order', 'agree', 'proj', 'blocks', 'ordereq']:
#            if set_attrib == 'blocks':
#                print('Found blocks in {}'.format(lexdim))
            if set_attrib in lexdim.attribs:
                if set_attrib not in self.attribs:
                    self.attribs[set_attrib] = set()
                lexdim_list = self.attribs[set_attrib]
                for attrib in lexdim.attribs[set_attrib]:
                    # Lower class has priority
                    if attrib not in lexdim_list:
                        lexdim_list.add(attrib)

        # agrs is special because the lex and class FSs need "unify"
        cls_agrs = lexdim.attribs.get('agrs')
        if cls_agrs:
            # "Feature structures" are tuples of integers
            if 'agrs' not in self.attribs:
                self.attribs['agrs'] = {}
            agrs = self.attribs.get('agrs')
            # The value of agrs is a dict of label strings with sets of FSs
            # as values
            for feat, valueS in cls_agrs.items():
                # Priority to lexeme/word over class
                if feat not in agrs:
                    agrs[feat] = valueS.copy()
                else:
                    new_value = unify_fssets(valueS, agrs[feat])
                    agrs[feat] = new_value

class Group:
    """Representation for a multi-word group. Not added directly to the lexicon. Instead
    included lexical entries are modified."""

    # 0 means no group
    ID = 0

    def __init__(self, name='', classes=None,
                 lexes=None,
                 lexicon=None, language=None):
        self.name = name
        self.classes = classes or []
        self.lexes = lexes or {}
        # Create a unique ID for this Lex (needed to recognize copies of same Lex)
        self.id = Group.get_id()
        # The lex or list of disjoint lexes that are the head of the group
        self.head = None
        # Language
        self.thead = {}
        self.lexicon = lexicon
        self.language = lexicon.language if lexicon else None

    def __repr__(self):
        return '%{}{}'.format(self.id, self.name)

    @staticmethod
    def get_id():
        '''Return a new Lex id, incrementing the counter.'''
        Group.ID += 1
        return Group.ID

    @staticmethod
    def from_dict(dct, language=None, lexicon=None):
        """Create Lexes for each of the words in word_list."""
        labbrev = language.abbrev
        group = Group(language=language)
        group.name = dct.get('group')
        word_dicts = dct.get('words')
#        empty = dct.get('empty')
#        if empty:
#            print('{} has empty {}'.format(group, empty))
        for word_dict in word_dicts:
            head = False
            # Lex.from_dict returns a list of lexes; these are the words in
            # the group. The entry for each is a new entry for the given string.
            lexes = Lex.from_dict(word_dict, language=language, lexicon=lexicon)
#            if not group.head:
            if 'head' in word_dict:
                group.head = lexes
                head = True
            for lex in lexes:
                lex.proc_group_lex(group.id)
                if 'thead' in word_dict:
                    lex.group_thead.update(word_dict['thead'])
                if head:
                    lex.ghead = group.id
                    lex.gheads[labbrev] = group.id
                # word_dict may be for an actual word or a lexeme or a copied
                # lexeme ("lexeme*")
                if 'word' in word_dict:
                    group.lexes[word_dict.get('word')] = lex
                elif 'lexeme' in word_dict:
                    group.lexes[word_dict.get('lexeme')] = lex
                elif 'lexeme*' in word_dict:
                    group.lexes[lex.get_name()] = lex
                else:
                    print('No name for group element {}: {}'.format(lex, word_dict))
        return group

    @staticmethod
    def make(name, lexicon, head, other_lexes):
        """Create a group 'on the fly'.
        head and other_lexes is in the form of LexGroup to be instantiated.
        """
        group = Group(name, lexicon=lexicon, language=lexicon.language)
        lexes = []
        for lex in [head] + other_lexes:
            # Each is a dict with keys
            # class, bindings
            lexclass = lex.get('class')
            # There may or may not be a lexclass
            if lexclass:
                # lexclass is a pair
                classname, classindex = lexclass
                lexclass = lexicon.get('lexclass')
                if lexclass:
                    lex = lexclass.instantiate(lex.get('bindings', {}), entries=[classindex])

##    def reverse(self, tlang):
##        """Given a target language (or its abbreviation), generate a group that goes in the opposite direction,
##        from target to source language. (Only applicable to cross-lingual groups.)"""
##        slang = self.language
##        languages = slang.LANGUAGES
##        if isinstance(tlang, str):
##            if tlang not in languages:
##                print('{} is not a loaded language'.format(tlang))
##                return
##            else:
##                tlang_abbrev = tlang
##                tlang = languages[tlang]
##        else:
##            tlang_abbrev = tlang.abbrev
##        heads = self.head
##        xlexes = []
##        for head in heads:
##            xx = head.crosslexes
##            if xx:
##                xlexes = xx.get(tlang_abbrev)
##                if xlexes:
##                    break
##        if not xlexes:
##            # There is no target language, so fail
##            print('{} does not have cross-lingual links to {}'.format(self, tlang_abbrev))
##            return
##        else:
##            tlexicon = tlang.lexicon
##            slang_abbrev = slang.abbrev
##            shead = self.head[0]
##            print('Reversing {}, head {}'.format(self, shead))
##            new_group = Group(language=tlang)
##            gid = new_group.id
##            print('Creating new group with id {}'.format(gid))
##            lexes = []
##            shead_eq_thead = False
##            if not any([tlang_abbrev in slex.group_thead for slex in self.lexes.values()]):
##                # No explict head for target
##                shead_eq_thead = True
##            for skey, slex in self.lexes.items():
##                xls = slex.crosslexes.get(tlang_abbrev)
##                thead = ''
##                shead = False
##                print('Lex {}, key {}'.format(slex, skey))
##                if tlang_abbrev in slex.group_thead:
##                    thead = slex.group_thead[tlang_abbrev]
##                    print('  Target head: {}'.format(thead))
##                if slex.ghead:
##                    shead = True
##                    if shead_eq_thead:
##                        thead = '^'
##                    print('  Source head')
##                if xls:
##                    for xl in xls:
##                        tlex = xl.targ_lex
##                        tlex_key = xl.targ_lex_key
##                        xlexdim = xl.lexdim
##                        xtargdim = xl.targdim
##                        if xlexdim:
##                            print('  Crosslex lexdim {}'.format(xlexdim))
##                        if xtargdim:
##                            print('  Crosslex targdim {}'.format(xtargdim))
##                        if xl.empty:
##                            empty_lex = xl.empty_lex
##                            print("  Source empty crosslex {}, target {}, targ key {}, source empty lex {}".format(xl, tlex, tlex_key,
##                                                                                                                   empty_lex))
##                            glex = tlex.clone(lexicon=tlexicon, new_id=True)
##                            gxlex = Crosslex(glex,
##                                             targ_lex_key=skey, targ_lex_index=0, targ_lex=empty_lex,
##                                             targ_lang_abbrev=slang_abbrev,
##                                             lexdim=None, targdim=None,
##                                             bidir=False, id=0, count=1, add=True,
##                                             empty=False, reverse=False)
##                            print("  New crosslex {}".format(gxlex))
##                            # Add crosslex to lex dict
##                            glex.crosslexes = {slang_abbrev: [gxlex]}
##                            # Add new lex to lexicon
##                            tlexicon.add_lex1(tlex_key, glex, tlex_key in tlexicon)
##                            # Add new lex to new group lexes
##                            lexes.append(glex)
##                            #                            entries = tlexicon.get(tlex_key, [])
##                            #                            entries.append(glex)
##                            #                            tlexicon[tlex_key] = entries
##                        elif tlex_key in ['zero', 'ZERO']:  # possible lexes for empty nodes
##                            print("  Target empty crosslex {}, target {}, targ key {}".format(xl, tlex, tlex_key))
##                            # This is really complicated because we have to find the trigger for the empty node
##                            # Assume the relevant relations are on the "surface" dimension
##                            sdim = slang.surface_dim
##                            tdim = tlang.surface_dim
##                            slexdim = slex.dims.get(sdim)
##                            if slexdim:
##                                attribs = slexdim.attribs
##                                souts = attribs.get('outs')
##                                sins = attribs.get('ins')
##                                sgouts = attribs.get('groupouts')
##                                print("    Source lex: ins {}, outs {}, groupouts {}".format(sins, souts, sgouts))
##                            #                            gxlex = EmptyCrosslex(trigger_lex,
##                            #                                                  empty_lex_key='', empty_lex_index=0,
##                            #                                                  targ_lang_abbrev=None, targ_lex_key='', targ_lex_index=0, targ_lex=None,
##                            #                                                  lexdim=None,
##                            #                                                  targdim=None,
##                            #                                                  if_dim='',
##                            #                                                  agrs=None, rel=None,
##                            #                                                  id=0,
##                            #                                                  count=1, add=True)
##                        else:
##                            print("  Normal crosslex {}, target {}, targ key {}".format(xl, tlex, tlex_key))
##                            glex = tlex.clone(lexicon=tlexicon, new_id=True)
##                            print("  New group lex {}".format(glex))
##                            if thead:
##                                # This is the head of the new group
##                                new_group.head = [glex]
##                                glex.ghead = gid
##                                glex.gheads[tlang_abbrev] = gid
##                                print("  Making {} the head of the new group".format(glex))
##                            gxlex = Crosslex(glex,
##                                             targ_lex_key=skey, targ_lex_index=0, targ_lex=slex,
##                                             targ_lang_abbrev=slang_abbrev,
##                                             lexdim=None,
##                                             targdim=None,
##                                             bidir=False, id=0, count=1, add=True,
##                                             empty=False, reverse=False)
##                            print("  New crosslex {}".format(gxlex))
##                            # Add crosslex to lex dict
##                            glex.crosslexes = {slang_abbrev: [gxlex]}
##                            # Add new lex to new group lexes
##                            lexes.append(glex)
##                            # Add new lex to lexicon
##                            tlexicon.add_lex1(tlex_key, glex, tlex_key in tlexicon)
##                            #                            entries = tlexicon.get(tlex_key, [])
##                            #                            entries.append(glex)
##                            #                            tlexicon[tlex_key] = entries

class LexClass:
    """A single level of abstraction over Lexes. Basically a template that
    is instantiated when a new 'entry' is created, resulting in the creation
    of one or more Lex instances, which are added to the Lexicon.
    """

    VAR = re.compile(r'\?(\S+)\?')

    # A line containing only a class name
    CLASS = re.compile(r'(\^\S+)\s*$')
    # A line containing var... = and a series of variable names separated by spaces
    VARS = re.compile(r'\s*var\S*\s*=\s*(.*)$')
    # A line containing ent... = and an entry name (normally a variable)
    # May begin with whitespace, which becomes the indentation for the entry
    ENTRY = re.compile(r'(\s*)ent\S*\s*=\s*(.*)$')
    # A line containing pos = and a POS name; whitespace at the beginning is saved
    POS = re.compile(r'(\s*)pos\s*=\s*(.*)$')
    # A line containing lexeme (and possibly nothing else); whitespace at the beginning is saved
    LEXEME = re.compile(r'(\s*)lexeme.*$')
    # A line containing root = and a root name; whitespace at the beginning is saved
    ROOT = re.compile(r'(\s*)root\s*=\s*(.*)$')
    # A line containing dim... = and a dimension name
    # with dim_attribs following on succeeding lines
    DIM = re.compile(r'(\s*)dim\S*\s*=\s*(.*)$')
    # A line containing cross... = and a language abbreviation
    # with cross_dim and target_dim attribs following on succeeding lines
    # May begin with indentation, which becomes the indentation for the cross
    CROSS = re.compile(r'(\s*)cross\s*=\s*(.*)$')
    # A line containing lex = and an entry name (normally a variable); the
    # target entry in the cross portion of the LexClass.
    # May begin with whitespace, which becomes the indentation for the entry
    LEX = re.compile(r'(\s*)lex\s*=\s*(.*)$')
    # Empty lex
    #   empty= tlex tindex relation label
    EMPTY = re.compile(r'(\s*)empty\s*=\s*(.*)$')
    # A line containing an attribs name followed by = and the value of the feature
    FEAT = re.compile(r'(\s*)(\S*)\s*=\s*(.*)$')
    # A line containing a description of the class
    DESC = re.compile(r'\s*desc\S*\s*=\s*(.*)$')
    # A condition on the form of an entry's wordform
    COND = re.compile(r'\s*cond\S*\s*=\s*(.*)$')
    
    # Morphological analyzer condition
    ANAL = re.compile(r'!(\S+)')

    def __init__(self, name, lexicon=None, variables=None, entries=None,
                 description='', final=False):
        if name[0] != '^':
            # Names of LexClasses should start with ^
            name = '^' + name
        self.name = name
        print('{} '.format(name), end='')
        self.lexicon = lexicon
        self.language = lexicon.language
        # Whether the lexclass is finalized for each entry (list of booleans).
        self.finalized = []
        # Set the class description
        self.description = description
        # Store the class in the lexicon
        self.lexicon.classes[name] = self
        # A dict of variables that get instantiated to features when the class
        # is instantiated; var names begin with '?'
        self.vars = variables or {}
        self.if_agree = []
        # A list of name, features pairs, where
        # features is a list of dim, dim_features pairs and
        # dim_features is a dict; dim_features can contain variables
        self.entries = []
        for name, entry in entries:
            self.add_entry(name, entry)

    def add_entry(self, name, entry):
        """Add an entry, fixing possible issues with names and recording
        the agrs and agree attributes."""
        # First fix any issues in the entry
        lang_abbrev = self.language.abbrev
        del_props = []
        add_props =[]
        finalized = True
        for prop, value in list(entry.items()):
            if prop in ('dim_attribs', 'dim'):
                fixed_value = []
                for v, attribs in value:
                    # v should be a dimension name
                    if '-' not in v:
                        v = lang_abbrev + '-' + v
                    fixed_value.append((v, attribs))
                    #                    print('Recording attribs {} for language {}'.format(attribs, self.language))
                    self.record_attribs(attribs, self.language)
                entry['dim_attribs'] = fixed_value
                # Get rid of alternate name
                if prop == 'dim':
                    del entry['dim']
            if prop == 'cross':
#                print('Value {}'.format(value))
                for clang, cprops in value:
                    clanguage = self.language.LANGUAGES.get(clang)
                    if not clanguage:
                        finalized = False
                    for ckey, cprop in list(cprops.items()):
                        fixed_value = []
                        if ckey in ('dim_attribs', 'target_dim'):
                            for v, attribs in cprop:
                                if '-' not in v:
                                    v = clang + '-' + v
                                fixed_value.append((v, attribs))
                                if clanguage:
                                    self.record_attribs(attribs, clanguage)
                            cprops['dim_attribs'] = fixed_value
                        elif ckey in ('cross_attribs', 'dim', 'cross_dim'):
                            label, attribs = cprop
                            if '-' not in label:
                                label = lang_abbrev + '-' + label
                            self.record_cross_attribs(attribs, self.language)
                            cprops['cross_attribs'] = (label, attribs)
                        # Get rid of alternate names
                        if ckey in ('dim', 'cross_dim', 'target_dim'):
                            del cprops[ckey]
        # Update the entry with corrected properties
        if del_props:
            for d in del_props:
                del entry[d]
        if add_props:
            for p, v in add_props:
                entry[p] = v
        self.finalized.append(finalized)
        self.entries.append((name, entry))

    def record_attribs(self, dim_attribs, language):
        """Record agreement and government features and feature combinations
        in the language."""
        labbrev = language.abbrev
        for attrib, values in dim_attribs.items():
            if attrib == 'agrs':
                lang_agrs = language.agrs
                #                print('Language agrs {}, values {}'.format(lang_agrs, values))
                for f, v in values.items():
#                    print('Recording {}; lang agrs {}, lang feats {}'.format(f, lang_agrs, language.feats))
                    lang_agrs[f].update(v)
            elif attrib == 'agree':
                lang_agree = language.agree
                lang_dfeats = language.labeldfeats
                for triple in values:
                    dfeat = triple[0], triple[2]
                    if dfeat not in lang_dfeats:
                        lang_dfeats.append(dfeat)
                    # Only do the following if this *follows* finalization
#                    trip_int = language.agree_strings_to_ints(triple)
#                    if trip_int not in lang_agree:
#                        lang_agree.append(trip_int)
            elif attrib == 'govern':
                lang_govern = language.govern
                lang_govdfeats = language.govlabeldfeats
                for triple in values:
                    # Only do this following finalization
#                    trip_int = language.gov_strings_to_ints(triple)
#                    if trip_int not in lang_govern:
#                        lang_govern.append(trip_int)
                    dfeat = triple[0], triple[1]
                    if dfeat not in lang_govdfeats:
                        lang_govdfeats.append(dfeat)

    def record_cross_attribs(self, dim_attribs, language):
        """Record crosslingual agreement and government features and feature combinations
        in the (source) language. What about the other language??"""
        labbrev = language.abbrev
        for attrib, values in dim_attribs.items():
            if attrib == 'agree':
                lang_ifagree = language.ifagree_pairs
                for triple in values:
                    if triple not in lang_ifagree:
                        lang_ifagree.append(triple)
            elif attrib == 'crossgov':
                for lab2, (attr, val) in values.items():
                    language.crossgovern_triples.append((lab2, attr, val))
                    language.crossgovlabeldfeats.append((lab2, attr))

    @staticmethod
    def subs_var(bindings):
        """Returns a function that takes a match object to
        pass to re.sub() in substitute()."""
        return lambda matchobj: bindings.get(matchobj.group(1), '')
    
    @staticmethod
    def substitute(string, bindings):
        """Substitutes variable values in var_dict into string."""
#        print('substitute: string {}, bindings {}'.format(string, bindings))
        return LexClass.VAR.sub(LexClass.subs_var(bindings), string)

    def subs_dimattribs(self, dim_attribs, bindings):
        """Substitute variable bindings where needed in dim_attribs dict."""
        for key, value in dim_attribs.items():
            if key == 'agrs':
                for akey, avalue in value.items():
                    if '?' in avalue:
#                        print(' agr value is variable {}'.format(avalue))
                        var_name = avalue.replace('?', '')
                        avalue = bindings.get(var_name, set())
                        if not isinstance(avalue, set):
                            if not isinstance(avalue, tuple):
                                if not isinstance(avalue, int):
                                    avalue = int(avalue)
                                avalue = (avalue,)
                            avalue = {avalue}
                        #                        avalue = LexClass.substitute(avalue, bindings)
#                        print(' substituted value: {}'.format(avalue))
                        value[akey] = avalue

    def check_cond(self, pattern, word):
        """Check to see whether word matches the phonetic/orthographic condition represented by
        pattern."""
        match = LexClass.ANAL.match(pattern)
        if match:
            # run a morphology FST on the word
            fst_name = match.group(1)
            fst = self.language.morphology.get(fst_name)
            analysis = fst.anal(word, guess=True)
            if analysis:
                return [a[0] for a in analysis]
            else:
                return False
        elif pattern == 'U':
            # capitalized
            return word.istitle()
        elif pattern == 'l':
            # not capitalized
            return word.islower()
        else:
            # Add sentence final character to pattern; treat as regex
            return re.match(pattern + '$', word)

    def instantiate(self, bindings, entries=None,
                    cross=True, final=False,
                    # when learning, sugg_name is wordform encountered;
                    # check_cond is True: phon/orth condition is checked first
                    sugg_name=None, check_cond=False,
                    verbosity=0):
        """Create lexical entries, given variable bindings.
        entries is None or a list of indices of the class entries
        to be instantiated.
        """
        for index, (name, entry) in enumerate(self.entries):
            if entries and index not in entries:
                # Don't instantiate this entry because it's not in entries
                continue
#            if verbosity:
#                print('entry name {}, index {}'.format(name, index))
            if sugg_name:
                name = sugg_name
            else:
                name_var = name.replace('?', '')
                if name_var not in bindings:
#                print('No name provided for entry {}'.format(name))
                    continue
                name = self.substitute(name, bindings)
            root = ''
            if check_cond:
                cond = entry.get('cond')
                if cond:
                    sat = True
                    for c in cond:
                        check = self.check_cond(c, name)
                        if not check:
                            print("word {} doesn't match condition for class {}".format(name, self.description))
                            sat = False
                            break
                        elif isinstance(check, list):
                            print("Morphological analysis found roots {}".format(check))
                            root = check[0]
                            # Use the root as the lexical key
                            name = root
                    if not sat:
                        continue
            if verbosity:
                print('Instantiating lex class {}, creating entry {}'.format(self, name))
            # Make a copy of the entry because we'll be mutating it
            e_copy = copy.deepcopy(entry)
            for key, prop in e_copy.items():
#                print('key {}, prop {}'.format(key, prop))
                # possible keys: dim_attribs, cross, pos, root
                if key == 'root' and not root:
                    root = self.substitute(prop, bindings)
                elif key == 'dim_attribs':
                    for dim, attribs in prop:
                        # dim attribs values can contain variables
                        # so return a copy with variables instantiated
                        self.subs_dimattribs(attribs, bindings)
                        #                        for akey, avalue in attribs.items():
                        #                            print('akey {}, avalue {}'.format(akey, avalue))
                elif key == 'cross':
#                    if not cross:
#                        continue
                    # cross can contain variables in name, root,
                    # and dim_attribs
                    to_del = []
                    to_add = []
#                    print('Cross props {}'.format(prop))
                    for clang, cprops in prop:
                        # check to see if there is a binding for the name variable
                        crossname = cprops.get('name')
                        if crossname:
                            crossname = crossname.replace('?', '')
                        if crossname and crossname not in bindings:
#                            print("Cross lex name {} not in bindings for {}".format(crossname, name))
                            to_del.append((clang, cprops))
                            continue
                        cross_binding = bindings.get(crossname)
                        # The binding of the variable could be a list of lexes in the other language
                        # In this case make a cross list for each name in the list
                        if isinstance(cross_binding, list):
#                            print('Cross lex {} is list'.format(cross_binding))
                            # Replace the original pair with a list of pairs
                            to_del.append((clang, cprops))
                            for tname in cross_binding:
                                cprops_copy = cprops.copy()
                                for ckey, cprop in cprops_copy.items():
                                    if ckey == 'name':
                                        cprops_copy['name'] = tname
                                    elif ckey == 'root':
                                        troot = self.substitute(cprop, bindings)
                                        cprops_copy['root'] = troot
                                    elif key == 'dim_attribs':
                                        for dim, attribs in cprop:
                                            # dim attribs values can contain variables
                                            # so return a copy with variables instantiated
                                            self.subs_dimattribs(attribs, bindings)
                                to_add.append((clang, cprops_copy))
                        else:
                            for ckey, cprop in cprops.items():
                                if ckey == 'name':
                                    tname = self.substitute(cprop, bindings)
                                    cprops['name'] = tname
                                elif ckey == 'root':
                                    troot = self.substitute(cprop, bindings)
                                    cprops['root'] = troot
                                elif key == 'dim_attribs':
                                    for dim, attribs in cprop:
                                        # dim attribs values can contain variables
                                        # so return a copy with variables instantiated
                                        self.subs_dimattribs(attribs, bindings)
                    # remove language entries that have no translations specified
                    for lang_props in to_del:
                        prop.remove(lang_props)
                    for lang_props in to_add:
                        prop.append(lang_props)
#            if e_copy.get('cross'):
#                print('Cross: {}'.format(e_copy.get('cross')))
                                
            self.lexicon.extend(name, pos=e_copy.get('pos'), root=root,
                                lexeme=e_copy.get('lexeme', False),
                                dim_attribs=e_copy.get('dim_attribs'),
                                cross=e_copy.get('cross'), finalized=final,
                                verbosity=verbosity)

    def __repr__(self):
        return "{}:{}".format(self.lexicon, self.name)

    @staticmethod
    def read(stream, lexicon):
        """Read in class definitions from a stream."""
        # class variables
        #        classes=[]
        #        print('Reading in lex classes for {}'.format(lexicon))
        name = ''
        entries = []
        variables = []
        description = ''
        # entry variables
        entry_name = ''
        value = ''
        split_line = False
        # Current entry dict
        entry = {}
        # cross entry variables
        # Current cross
        cross = {}
        # Current list of crosses
        crosses = []
        # Language for current cross
        cross_language = ''
        # dimension variables
        # Current dimension
        dimension = {}
        # Current feature
        feat = ''
        # Current list of dimensions
        dims = []
        dim_indent = 0
        dim_name = ''
        feat_indent = 0
        # Which portion we're working on
        in_cross, in_cross_lex = False, False
        # Indentation
        entry_indent, cross_indent, cross_lex_indent = 0, 0, 0
        for line in stream:
            # An empty line (no comments either) means the end of a class entry
            if not line.strip():
                # There's a class waiting to finish
                if name:
                    # First finalize waiting dimensions
                    if dimension:
                        dims.append((dim_name, dimension))
                        dimension = {}
                    # First finalize waiting cross, dimensions, entry
                    LexClass._finish_dims(entry, cross, dims, in_cross, in_cross_lex)
                    LexClass._finish_crosses(entry, crosses, cross, cross_language)
                    LexClass._finish_class(entry_name, entry, entries, cross, crosses, cross_language)
#                    print('Creating last class {}'.format(name))
                    cls = LexClass(name, lexicon=lexicon, variables=variables,
                                   description=description, entries=entries)
                    name = ''
                    dims = []
                continue

            # Strip comments
            line = line.split('#')[0]

            if not line.strip():
                # Ignore lines with only comments
                continue

            # Try different regexs for the current line
            m = LexClass.CLASS.match(line)
            if m:
                # start a new LexClass
                variables = []
                entries = []
                description = ''
                entry = {}
                entry_name = ''
                name = m.group(1)
                #                print('Starting a new class {}'.format(name))
                continue
            m = LexClass.VARS.match(line)
            # Normally the variables come at the beginning
            if m:
                variables = m.group(1).split()
#                print('Variables {}'.format(variables))
                continue
            m = LexClass.DESC.match(line)
            if m:
                description = m.group(1).strip()
                continue
            m = LexClass.ENTRY.match(line)
            if m:
                # Add last entry
                if entry:
                    if dimension:
                        dims.append((dim_name, dimension))
                    LexClass._finish_dims(entry, cross, dims, in_cross, in_cross_lex)
                    LexClass._finish_crosses(entry, crosses, cross, cross_language)
                    if entry.get('lexeme') and not entry.get('root'):
                        entry['root'] = entry_name
                    entries.append((entry_name, entry))
                entry_indent = len(m.group(1))
                entry_name = m.group(2)
#                print('New entry {}, indentation {}'.format(entry_name, entry_indent))
                # Reinitialize entry variables
                entry = {}
                cross = {}
                crosses = []
                dims = []
                dimension = {}
                dim_name = ''
                entry_indent, cross_indent, cross_lex_indent = 0, 0, 0
                in_cross, in_cross_lex = False, False
                continue
            m = LexClass.ROOT.match(line)
            if m:
                indent = len(m.group(1))
                entry_root = m.group(2)
#                print('Entry root {}, indentation {}'.format(entry_root, indent))
                if cross_lex_indent and indent > cross_lex_indent:  # OR if in_cross
#                    print('Part of cross lex entry')
                    cross['root'] = entry_root
                else:
#                    print('Part of top-level entry')
                    entry['root'] = entry_root
                # Check to see if a dimension is waiting
                if dimension and dim_indent and indent <= dim_indent:
                    dims.append((dim_name, dimension))
                    dimension = {}
                    dim_indent = 0
                continue
            m = LexClass.POS.match(line)
            if m:
                indent = len(m.group(1))
                entry_pos = m.group(2)
#                print('Entry POS {}, indentation'.format(entry_pos, indent))
                if cross_lex_indent and indent > cross_lex_indent:
#                    print('Part of cross lex entry')
                    cross['pos'] = entry_pos
                else:
#                    print('Part of top-level entry')
                    entry['pos'] = entry_pos
                # Check to see if a dimension is waiting
                if dimension and dim_indent and indent <= dim_indent:
                    dims.append((dim_name, dimension))
                    dimension = {}
                    dim_indent = 0
                continue
            m = LexClass.LEXEME.match(line)
            if m:
                indent = len(m.group(1))
#                print('Entry is lexeme, indentation {}'.format(indent))
                entry_lexeme = True
                if cross_lex_indent and indent > cross_indent:
#                    print('Part of cross lex entry')
                    cross['lexeme'] = True
                else:
#                    print('Part of top-level entry')
                    entry['lexeme'] = True
                # Check to see if a dimension is waiting
                if dimension and dim_indent and indent <= dim_indent:
                    dims.append((dim_name, dimension))
                    dimension = {}
                    dim_indent = 0
                continue
            m = LexClass.COND.match(line)
            if m:
                condition = m.group(1)
                condition = [c.strip() for c in condition.split(';')]
#                print("Entry condition {}".format(condition))
                entry['cond'] = condition
                continue
            m = LexClass.DIM.match(line)
            if m:
                indent = len(m.group(1))
                dim_name = m.group(2).strip()
#                print('Entry dim {}, indentation {}'.format(dim_name, indent))
#                if cross_lex_indent and indent > cross_lex_indent:
#                    print('Part of cross lex entry')
#                elif cross_indent and indent > cross_indent:
#                    print('Part of cross')
#                else:
#                    print('Part of top-level entry')
                # Check to see if a dimension is waiting
                if dimension and dim_indent and indent <= dim_indent:
                    dims.append((dim_name, dimension))
                    dimension = {}
                dim_indent = indent
                continue
            m = LexClass.CROSS.match(line)
            if m:
                # Finish the last cross entry if one is waiting
                if cross:
                    crosses.append((cross_language, cross))
                cross_indent = len(m.group(1))
                cross_language = m.group(2)
#                print('Entry cross to {}, indentation {}'.format(cross_language, cross_indent))
                # Check to see if a dimension is waiting
                if dimension and dim_indent and cross_indent <= dim_indent:
                    dims.append((dim_name, dimension))
                    dimension = {}
                    dim_indent = 0
                # dims needs to be assigned somewhere
                if dims:
                    if in_cross_lex:
                        cross['target_dim'] = dims
                    elif in_cross:
                        cross['cross_dim'] = dims
                    else:
                        entry['dim'] = dims
                    dims = []
                # Initialize the new cross entry
                in_cross = True
                in_cross_lex = False
                cross = {}
                dimension = {}
                continue
            m = LexClass.LEX.match(line)
            if m:
                cross_lex_indent = len(m.group(1))
                cross_lex_name = m.group(2)
                cross['name'] = cross_lex_name
                in_cross_lex = True
#                print('Entry cross lex {}, indentation {}'.format(cross_lex_name, cross_lex_indent))
                # Check to see if a dimension is waiting
                if dimension and dim_indent and cross_lex_indent <= dim_indent:
                    dims.append((dim_name, dimension))
                    dimension = {}
                    dim_indent = 0
                if dims:
                    # If there are dims, they must be cross dims, but there's only one
                    cross['cross_dim'] = dims[0]
                    dims = []
                continue
            m = LexClass.EMPTY.match(line)
            if m:
                empty_indent = len(m.group(1))
                empty_props = m.group(2).split(',')
                empty_attribs = empty_props[0].split()
                empty_cond = empty_props[1].split() if len(empty_props) == 2 else None
                if len(empty_attribs) == 4:
                    empty_attribs[3] = int(empty_attribs[3])
#                print('Empty {}, cond {}'.format(empty_attribs, empty_cond))
                if 'empty' not in cross:
                    cross['empty'] = [(empty_attribs, empty_cond)]
                else:
                    cross['empty'].append((empty_attribs, empty_cond))
                continue
            # Features/attributes
            m = LexClass.FEAT.match(line)
            if m:
                feat_indent = len(m.group(1))
                feat = m.group(2)
                # Deal with feature aliases
                feat = LexClass._convert_feat(feat)
                curr_value = m.group(3)
                last_char = curr_value[-1]
                value += curr_value
#                print('  Feature {} curr value {} value {} last char {}'.format(feat, curr_value, value, last_char))
                if last_char in (",", ";", "\\"):
                    split_line = True
                else:
                    split_line = False
                    value = LexClass._feat_value(feat, value)
#                    value = eval(value)
                    dimension[feat] = value
                if not split_line:
                    value = ''
                continue
            # Otherwise this has to be a feature continuation
            if not split_line:
                print("Something wrong with this line {}".format(line))
            else:
                curr_value = line.strip()
                last_char = curr_value[-1]
                value += ' ' + curr_value
#                print('  Feature {} curr value {} value {} last char {}'.format(feat, curr_value, value, last_char))
                if last_char in (",", ";", "\\"):
                    split_line = True
                else:
                    split_line = False
                    value = LexClass._feat_value(feat, value)
#                    value = eval(value)
                    dimension[feat] = value
                    #                print("  New value {}, value {}".format(curr_value, value))
                if not split_line:
                    value = ''
                    #        print('Finished, dimension waiting {}, dims waiting {}, in cross lex? {}'.format(dimension, dims, in_cross_lex))
        # Create the last class
        if name:
            if dimension:
                dims.append((dim_name, dimension))
            # Finalize waiting cross, dimensions, entry
            LexClass._finish_dims(entry, cross, dims, in_cross, in_cross_lex)
            if cross:
                crosses.append((cross_language, cross))
            if entry.get('lexeme') and not entry.get('root'):
                entry['root'] = entry_name
            LexClass._finish_crosses(entry, crosses, cross, cross_language)
            LexClass._finish_class(entry_name, entry, entries, cross, crosses, cross_language)
#                    print('Creating last class {}'.format(name))
            LexClass(name, lexicon=lexicon, variables=variables,
                     description=description, entries=entries)

    @staticmethod
    def _convert_feat(string):
        """Aliases for various feature/attribute names."""
        if string in ['in', 'mothers']:
            return 'ins'
        elif string in ['out', 'daughters']:
            return 'outs'
        else:
            return string

    @staticmethod
    def _agr_str2value(string):
        """string is something like '0 1' or a variable."""
        ints = string.split()
        # Make characters into ints
        for i, c in enumerate(ints):
            ints[i] = int(c)
        return tuple(ints)

    @staticmethod
    def _feat_value(feat, value):
        if feat in ('order', 'agree'):
            # List of different orderings
            value = value.split(',')
            res = set()
            for v in value:
                # Make an ordering tuple from a space-separated list
                res.add(tuple(v.split()))
            return res
        elif feat in ('ins', 'outs',):
            value = value.split(',')
            res = {}
            for v in value:
                arc, char = v.split()
                if char.isdigit():
                    char = int(char)
                res[arc] = char
            return res
        elif feat == 'arcagree':
            value = value.split(';')
            res = {}
            for v in value:
                arc, f, v1, v2 = v.split(',')
                res[arc.strip()] = (f.strip(), LexClass._agr_str2value(v1), LexClass._agr_str2value(v2))
            return res
        elif feat == 'agrs':
            value = value.split(';')
            res = {}
            for v in value:
                v = v.strip()
                f, x, vv = v.partition(' ')
                # vv is a string with comma-separated sequences of integers
                if '?' in vv:
                    tups = vv
                else:
                    tups = set()
                    for i in vv.strip().split(','):
                        tups.add(LexClass._agr_str2value(i))
                res[f.strip()] = tups
            return res
        # all the linking principles
        elif feat in ('ldend',):
            value = value.split(';')
            res = {}
            for v in value:
                v = v.strip()
                v = v.split()
                res[v[0]] = tuple(v[1:])
            return res
        else:
            return eval(value)

    @staticmethod
    def _finish_dims(entry, cross, dimensions, in_cross=False, in_cross_lex=False):
        if dimensions:
            if in_cross_lex:
                cross['target_dim'] = dimensions
            elif in_cross:
                # Dimension is a single pair, not a list of pairs
                cross['cross_dim'] = dimensions[0]
            else:
                entry['dim'] = dimensions

#    @staticmethod
#    def _finish_entry(entry, crosses):
#        entry['cross'] = crosses

    @staticmethod
    def _finish_crosses(entry, crosses, cross, cross_language):
        if cross:
            crosses.append((cross_language, cross))
        if crosses:
            entry['cross'] = crosses

    @staticmethod
    def _finish_class(name, entry, entries, cross, crosses, language):
#        if cross:
#            crosses.append((language, cross))
#            if entry:
#                entry['cross'] = crosses
        if entry:
            entries.append((name, entry))
