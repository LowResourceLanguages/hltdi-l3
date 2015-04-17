#   
#   Hiiktuu entries: words, grammatical morphemes, lexemes, lexical classes
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

# 2014.02.10
# -- Created
#    Possible subclasses: Lex (word, lexeme, class), Gram
# 2014.02.12
# -- Inheritance (class to word/lexeme): completed except for government.
#    (But possible conflicts in order are not handled yet.)
# 2014.02.15
# -- Methods for making dicts from entries and entries from dict, used
#    in serialization.
# 2014.02.16-18
# -- Class for groups (multi-word expressions).
# 2014.02.18
# -- Cloning of Lex instances (for groups and L3 nodes).
# 2014.03.18
# -- Lots of changes and additions to groups.
# 2014.03.24
# -- words attribute in Group is a list of [word, feat_dict] pairs.
# 2014.04.16
# -- Created simpler Group (with no dependency types), renamed old Group to MWE.
# 2014.04.20
# -- Matching of group and sentence nodes.
# 2014.04.30
# -- Eliminated everything but Groups.
# 2014.05.01
# -- Group/node matching fixed.
# 2014.05.06
# -- Group entry indices need to distinguish ambiguous words/lexemes.
#    Indices can be things like "end_n", with POS or other identifiers after "_".
#    "end_n" and "end_v" would be different roots of "end" in the forms dict.

import copy, itertools
import yaml

from .features import *

LEXEME_CHAR = '_'
CAT_CHAR = '$'

class Entry:
    """Superclass for Group and possibly other lexical classes."""

    ID = 1
    dflt_dep = 'dflt'
    
    def __init__(self, name, language, id=0, trans=None):
        """Initialize name and basic features: language, trans, count, id."""
        self.name = name
        self.language = language
        self.trans = trans
        self.count = 1
        if id:
            self.id = id
        else:
            self.id = Entry.ID
            Entry.ID += 1

    def __repr__(self):
        """Print name."""
        return '<{}:{}>'.format(self.name, self.id)

    @staticmethod
    def is_cat(name):
        """Is this the name of a category?"""
        return CAT_CHAR in name

    @staticmethod
    def is_lexeme(name):
        """Is this the name of a lexeme?"""
        return LEXEME_CHAR in name

    ## Serialization

    def to_dict(self):
        """Convert the entry to a dictionary to be serialized in a yaml file."""
        d = {}
        d['name'] = self.name
#        d['language'] = self.language
        d['count'] = self.count
        if self.trans:
            d['trans'] = self.trans
        d['id'] = self.id
        return d

    @staticmethod
    def from_dict(d, language):
        """Convert a dict (loaded from a yaml file) to an Entry object."""
        e = Entry(d.get('name'), language)
        e.count = d.get('count', 1)
        e.id = d.get('id', 1)
        e.trans = d.get('trans')
        return e

    def update_count(self, count=1):
        """Update count on the basis of data from somewhere."""
        self.count += count

    ### Translations (word, gram, lexeme, group entries)
    ###
    ### Translations are stored in a language-id-keyed dict.
    ### Values are dicts with target entry names as ids.
    ### Values are dicts with correspondence ('cor'), count ('cnt'), etc.
    ### as keys.

    def get_translations(self, language, create=True):
        """Get the translation dict for language in word/lexeme/gram entry.
        Create it if it doesn't exist and create is True."""
        if self.trans is None:
            self.trans = {}
        if language not in self.trans and create:
            self.trans[language] = {}
        return self.trans.get(language)

    def add_trans(self, language, trans, count=1):
        """Add translation to the translation dictionary for language,
        initializing its count."""
        transdict = self.get_translations(language, create=True)
        transdict[trans] = {'c': count}

    def update_trans(self, language, trans, count=1):
        """Update the count of translation."""
        transdict = self.get_translations(language)
        if trans not in transdict:
            s = "Attempting to update non-existent translation {} for {}"
            raise(EntryError(s.format(trans, self.name)))
        transdict[trans]['c'] += count

##class Lex(Entry):
##
##    cloneID = 1
##
##    def __init__(self, name, language, cls=None, id=0, group=False):
##        """In addition to Entry features, initialize
##        depsin, depsout, order, agr, gov, grams, and (for word and lexeme) class."""
##        Entry.__init__(self, name, language, id=id)
##        self.depsin = None
##        self.depsout = None
##        self.order = None
##        self.agr = None
##        self.gov = None
##        self.grams = None
##        self.cls = cls
##        self.cloneID = 0
##        # Whether entry is part of a group
##        self.group = group
##
##    def __repr__(self):
##        """Print name and a unique identifier."""
##        return '<{}:{}{}>'.format(self.name, self.id, ';' + str(self.cloneID) if self.cloneID else '')
##
##    ## Cloning
##    ## Needed for groups, which consist of copies of lexes and
##    ## for L3 node entries
##
##    def clone(self, group=True):
##        copied = Lex(self.name, self.language, cls=self.cls, id=self.id, group=group)
##        copied.depsin = self.depsin
##        copied.depsout = self.depsout
##        copied.order = self.order
##        copied.agr = self.agr
##        copied.gov = self.gov
##        copied.grams = self.grams
##        copied.cloneID = Lex.cloneID
##        Lex.cloneID += 1
##        return copied
##
##    ## Serialization
##
##    def to_dict(self):
##        """Convert the lex to a dictionary to be serialized in a yaml file."""
##        d = Entry.to_dict(self)
##        if self.depsin:
##            d['depsin'] = copy.deepcopy(self.depsin)
##        if self.depsout:
##            d['depsout'] = copy.deepcopy(self.depsout)
##        if self.order:
##            d['order'] = copy.deepcopy(self.order)
##        if self.agr:
##            d['agr'] = copy.deepcopy(self.agr)
##        if self.gov:
##            d['gov'] = copy.deepcopy(self.gov)
##        if self.grams:
##            d['grams'] = self.grams.copy()
##        if self.cls:
##            d['cls'] = self.cls
##        return d
##
##    @staticmethod
##    def from_dict(d, language):
##        """Convert a dict (loaded from a yaml file) to a Lex object."""
##        l = Lex(d.get('name'), language, cls=d.get('cls'))
##        if d.get('depsin'):
##            l.depsin = d.get('depsin')
##        if d.get('depsout'):
##            l.depsout = d.get('depsout')
##        if d.get('order'):
##            l.order = d.get('order')
##        if d.get('agr'):
##            l.agr = d.get('agr')
##        if d.get('gov'):
##            l.gov = d.get('gov')
##        if d.get('grams'):
##            l.grams = d.get('grams')
##        return l
##
##    ## Dependencies (word, lexeme, class entries)
##
##    def get_depin(self, label, create=False):
##        """Get the dict of features of incoming dependencies with label, creating
##        the dict if it's not there and create is True."""
##        if self.depsin is None:
##            self.depsin = {}
##        if create and label not in self.depsin:
##            self.depsin[label] = {}
##            self.language.record_label(label)
##        return self.depsin.get(label)
##
##    def add_depin(self, label, feats):
##        """Assign feats (a dictionary) to features for incoming dependencies with label,
##        or update the current features."""
##        d = self.get_depin(label, create=True)
##        d.update(feats)
##
##    def get_depout(self, label, create=False):
##        """Get the dict of features of outgoing dependencies with label, creating
##        the dict if it's not there and create is True."""
##        if self.depsout is None:
##            self.depsout = {}
##        if create and label not in self.depsout:
##            self.depsout[label] = {}
##            self.language.record_label(label)
##        return self.depsout.get(label)
##
##    def add_depout(self, label, feats):
##        """Assign feats (a dictionary) to features for outgoing dependencies with label,
##        or update the current features."""
##        d = self.get_depout(label, create=True)
##        d.update(feats)
##
##    ## Dependency features
##    ## A dict with keys
##    ## 'min', 'max', 'dflt', 'maxdist'
##
##    def set_deps_feat(self, featdict, key, value):
##        featdict[key] = value
##
##    def get_deps_feat(self, featdict, key):
##        return featdict.get(key)
##
##    ## Order constraints
##    ## A constraint is a tuple of dependency labels and '^' representing the head
##
##    def get_order(self, create=False):
##        """Get the set of order constraint tuples, creating the set if it's not there
##        and create is True."""
##        if self.order is None and create:
##            self.order = []
##        return self.order
##
##    def add_order(self, constraint):
##        """Add an order constraint tuple to the set of order constraints."""
##        order_constraints = self.get_order(create=True)
##        order_constraints.append(constraint)
##        self.language.record_order(constraint)
##
##    ## Grammatical features associated with words, classes, and lexemes
##
##    def get_gram(self, feature, create=False):
##        """Get the possible values and their counts for grammatical feature.
##        If this is a word, the value is a string; if a class or lexeme, a dict
##        of values and counts."""
##        if self.grams is None:
##            self.grams = {}
###        if feature not in self.grams and create:
###            self.grams[feature] = {}
##        return self.grams.get(feature)
##
##    def set_gram(self, feat, values):
##        """Set possible values and their counts for grammatical feature.
##        values is a dict of values and their counts."""
##        if self.grams is None:
##            self.grams = {}
##        if feat in self.grams:
##            s = "Entry for {} already has a constraint for feature {}"
##            raise(EntryError(s.format(self.name, feat)))
##        self.grams[feat] = values
##
##    def update_gram_value(self, feat, value, count=1):
##        """Add count to the current count for feature value."""
##        gram = self.get_gram(feat, create=True)
##        if value in gram:
##            gram[value] += count
##        else:
##            gram[value] = count
##
##    ## Agreement and government
##
##    ## An agreement constraint requires a dependency label, a head feature, and
##    ## and a dependent feature.
##
##    def add_agr(self, deplabel, head_feat, dep_feat):
##        """Add an agreement constraint to the list of constraints in the entry."""
##        if self.agr is None:
##            self.agr = []
##        self.agr.append([deplabel, head_feat, dep_feat])
##
##    ## A government constraint requires a dependency label, a dependent feature,
##    ## and a dependent value.
##
##    def add_gov(self, deplabel, dep_feat, dep_value):
##        if self.gov is None:
##            self.gov = []
##        self.gov.append([deplabel, dep_feat, dep_value])
##
##    ## Inheritance: copying features from classes to lexemes and words
##    ## at initialization
##
##    def inherit(self):
##        if not self.cls:
##            return
##        cls = self.language.get_class(self.cls)
##        if not cls:
##            s = "Class {} for {} does not exist"
##            raise(EntryError(s.format(self.cls, self)))
##        self.inherit_deps(cls)
##        self.inherit_order(cls)
##        self.inherit_grams(cls)
##        self.inherit_agr(cls)
##        self.inherit_gov(cls)
##        # Also inherit translation?
##
##    def inherit_deps(self, cls):
##        """Inherit dependency constraints (in and out) from class."""
##        # In
##        cls_depsin = cls.depsin
##        if cls_depsin:
##            if self.depsin is None:
##                self.depsin = {}
##            for label, cls_constraints in cls_depsin.items():
##                if label in self.depsin:
##                    constraints = self.depsin[label]
##                    for k, v in cls_constraints.items():
##                        if k in constraints:
##                            continue
##                        constraints[k] = v
##                else:
##                    # Should this be a copy of cls_constraints?
##                    self.depsin[label] = cls_constraints
##        # Out
##        cls_depsout = cls.depsout
##        if cls_depsout:
##            if self.depsout is None:
##                self.depsout = {}
##            for label, cls_constraints in cls_depsout.items():
##                if label in self.depsout:
##                    constraints = self.depsout[label]
##                    for k, v in cls_constraints.items():
##                        if k in constraints:
##                            continue
##                        constraints[k] = v
##                else:
##                    # Should this be a copy of cls_constraints?
##                    self.depsout[label] = cls_constraints
##
##    def inherit_order(self, cls):
##        """Inherit order constraints from class."""
##        cls_order = cls.order
##        if cls_order:
##            my_order = self.get_order(create=True)
##            # Just add all constraints (tuples) from the class to ones
##            # already there in the word or lexeme; what if there are
##            # conflicts?? (sort these out later)
##            for co in cls_order:
##                if co not in my_order:
##                    my_order.append(co)
##
##    def inherit_grams(self, cls):
##        """Inherit grammatical features from class."""
##        cls_grams = cls.grams
##        if cls_grams:
##            if self.grams is None:
##                self.grams = {}
##            for feature, value in cls_grams.items():
##                if feature in self.grams:
##                    # word/lexeme gram has priority over class, so
##                    # ignore this
##                    continue
##                # copy any other feature/value constraint
##                # (should the value be a copy??)
##                self.grams[features] = value
##
##    def inherit_agr(self, cls):
##        """Inherit agreement constraints from class."""
##        cls_agr = cls.agr
##        if cls_agr:
##            if self.agr is None:
##                self.agr = []
##            for constraint in cls_agr:
##                if constraint not in self.agr:
##                    self.agr.append(constraint)
##
##    def inherit_gov(self, cls):
##        """Inherit government constraints from class."""
##
##class MWE(Entry):
##    """Multi-word expressions. Each group consists of a head and a set of nodes,
##    possibly connected to other nodes through explicit dependencies and an explicit
##    order of the nodes.
##    Variable slots have dedicated names that allow them to be
##    referenced in translations.
##    MWEs must be created *after* other lexical items.
##    {index: [word_obj, {dep/position_feats}...}
##    """
##    
##    def __init__(self, name, language, head, head_feats=None, head_order=None, head_lexeme=False):
##        """name of a MWE is something like acabar_de_V.
##        head is the word that is the syntactic head of the group."""
##        Entry.__init__(self, name, language)
##        # A list of [word feats] pairs; index in the list is the word's (node's) ID
##        self.words = []
##        self.word_id = 0
##        if head_lexeme:
##            self.head_lexeme = True
##            head_type = language.get_lexeme(head)
##        else:
##            self.head_lexeme = False
##            head_type = language.get_words(head)
##        if not head_type:
###            print("No existing lexical entry in {} for head of group {}".format(language, name))
##            # SHOULD THIS BE RECORDED IN THE WORD LEXICON?
##            self.head = language.add_word(head, group=True)
##        else:
##            # Use the first one if there's more than one
##            self.head = head_type[0].clone()
##        self.words.append([self.head, {}])
###        self.words[self.word_id] = [self.head, {}]
##        if head_order is not None:
##            self.words[word_id][1]['o'] = head_order
###            self.words[self.word_id][1]['o'] = head_order
##        self.word_id += 1
##
##    def __repr__(self):
##        """Print name."""
##        return '<{}:{}>'.format(self.name, self.id)
##
##    # Serialization
##
##    def to_dict(self):
##        """Convert the group to a dictionary to be serialized in a yaml file."""
##        d = Entry.to_dict(self)
##        d['head_lexeme'] = self.head_lexeme
###        d['words'] = {}
##        d['words'] = []
##        w = d['words']
###        for index, lex in self.words.items():
##        for lex in enumerate(self.words):
##            l = lex[0]
##            name = l.name
##            w.append([name])
###            w[index] = [name]
##            if len(lex) == 2:
##                w[-1].append(copy.deepcopy(lex[1]))
###                w[index].append(copy.deepcopy(lex[1]))
##        return d
##
##    @staticmethod
##    def from_dict(d, language):
##        """Convert a dict (loaded from a yaml file) to a MWE object."""
##        lexeme = d['head_lexeme']
##        m = MWE(d.get('name'), language, d.get('words')[0][0], head_lexeme=lexeme)
###        for id, word in d.get('words').items():
##        for id, word in enumerate(d.get('words')):
##            if id == 0:
##                # Just handle the dependencies for this case
##                deps = word[1]
##                m.words[0][1] = copy.deepcopy(deps)
##            else:
##                name = word[0]
##                lex = language.get_words(name)[0]
##                if len(word) == 2:
##                    deps = word[1]
##                    lex_info = [lex.clone(), copy.deepcopy(deps)]
##                else:
##                    lex_info = [lex.clone()]
##                m.words.append(lex_info)
##        return m
##
##    ## Getters
##
##    def get_word(self, index):
##        """The lex and features for a word in the group with ID index."""
##        if index > len(self.words) - 1:
##            s = "No word in {} with internal ID {}"
##            raise(EntryError(s.format(self, index)))
##        return self.words[index]
##
##    def get_word_feats(self, index):
##        word = self.get_word(index)
##        return word[1]
##
##    def get_lex(self, id):
##        """Return the Lex with the given index."""
##        word = self.get_word(id)
##        return word[0]
##
##    def get_daughters(self, word_id, dep=None):
##        """Return the indices of the daughters of word with id word_id
##        of type dep or all daughters if dep is None."""
##        feats = self.get_word_feats(word_id)
##        if 'd' not in feats:
##            return
##        daughters = feats['d']
##        if dep is not None:
##            return daughters.get(dep)
##        else:
##            # Maybe leave as an iterable object?
##            return list(itertools.chain.from_iterable(daughters.values()))
##
##    def get_mother(self, word_id):
##        """Return the type and index of the internal mother of word with id word_id.
##        If this is the head, return None."""
##        feats = self.get_word_feats(word_id)
##        if 'm' not in feats:
##            return
##        return feats['m']
##
##    def add_word(self, word, head_id=None, dependency=Entry.dflt_dep, order=None):
##        """Add a word to the group, as dependent on dependency from head."""
##        # For now, use first word entry
##        typ = self.language.get_words(word)
##        if not typ:
###            print("No existing lexical entry in {} for head of group {}".format(self.language, word))
##            # SHOULD THIS BE RECORDED IN THE WORD LEXICON?
##            word = self.language.add_word(word, group=True)
##        else:
##            # Pick the first lexical entry for now
##            word = typ[0].clone()
##        self.words.append([word, {}])
###        self.words[self.word_id] = [word, {}]
##        if head_id is not None:
##            self.add_dep(head_id, self.word_id, dep=dependency)
##        if order is not None:
##            self.words[self.word_id][1]['o'] = order
##        id = self.word_id
##        self.word_id += 1
##        return id
##
##    def add_dep(self, src, dest, dep=Entry.dflt_dep):
##        """Make a dependency of type dep from word with id src to word with id dest."""
##        if src >= len(self.words):
##            s = "No word in {} with internal ID {}"
##            raise(EntryError(s.format(self, src)))
##        if dest >= len(self.words):
##            s = "No word in {} with internal ID {}"
##            raise(EntryError(s.format(self, dest)))
##        daughter_dict = self.get_word_feats(dest)
##        if 'm' in daughter_dict:
##            s = "Word {} in {} already has a mother"
##            raise(EntryError(s.format(dest, self)))
##        daughter_dict['m'] = (dep, src)
##        mother_dict = self.get_word_feats(src)
##        if 'd' not in mother_dict:
##            mother_dict['d'] = {}
##        mother_daughters = mother_dict['d']
##        if dep not in mother_daughters:
##            mother_daughters[dep] = []
##        mother_daughters[dep].append(dest)
##    
##    ## Translations
##    ## A translation of a group is a group in another language, with a mapping or alignment
##    ## between the nodes (words) in the two groups.
##    ## The mapping takes the form of a list of target word indices or None if the corresponding
##    ## word is unspecified or -1 if there is not corresponding word (deletion). If there are
##    ## more words/nodes in the target than in the source group, the length of the list of
##    ## is the number of target nodes.
##
##    def add_trans(self, language, trans, count=1):
##        """Add translation to the translation dictionary for language,
##        initializing its count."""
##        Entry.add_trans(self, language, trans, count=count)
##        transdict = self.get_trans(language, trans)
##        transdict['m'] = [None for x in range(len(self.words))]
##
##    def get_trans(self, language, trans, create=True):
##        alltrans = self.get_translations(language, create=create)
##        if not alltrans or trans not in alltrans:
##            s = "Attempting to update non-existent translation {} for {}"
##            raise(EntryError(s.format(trans, self.name)))
##        return alltrans[trans]
##
##    def get_trans_map(self, language, trans):
##        """Get the mapping to nodes in translation."""
##        tdict = self.get_trans(language, trans)
##        return tdict.get('m')
##
##    def get_trans_map1(self, language, trans, src_index):
##        """Get the mapped index of src_index in translation trans."""
##        map = self.get_trans_map(language, trans)
##        if not map:
##            s = "Attempting to access non-existing mapping for translation {} of {}"
##            raise(EntryError(s.format(trans, self)))
##        return map[src_index]
##
##    def add_trans_map(self, language, trans, src_id, trg_id):
##        """Add a correspondence between source and target nodes in a translation mapping."""
##        tdict = self.get_trans(language, trans)
###        if 'm' not in tdict:
###            tdict['m'] = []
###        tdict['m'].append((src_id, trg_id))
##        tdict['m'][src_id] = trg_id
##
##    def add_trans_del(self, language, trans, src_id):
##        """Record a node in the source group with nothing corresponding to it in the target group."""
##        tdict = self.get_trans(language, trans)
###        if 'm' not in tdict:
###            tdict['m'] = []
###        tdict['m'].append((src_id, -1))
##        tdict['m'][src_id] = -1
##
##    def add_trans_ins(self, language, trans, trg_id):
##        """Record a node in the target group with nothing corresponding to it in the source group."""
##        tdict = self.get_trans(language, trans)
###        if 'm' not in tdict:
###            tdict['m'] = []
##        tdict['m'].append(trg_id)
###        tdict['m'].append((-1, trg_id))

class Group(Entry):
    """Primitive multi-word expressions. Default is a head with unlabeled dependencies
    to all other tokens and translations, including alignments, to one or more
    other languages."""

    def __init__(self, tokens, head_index=-1, head='', language=None, name='',
                 features=None, agr=None, trans=None):
        """Either head_index or head (a string) must be specified."""
        # tokens is a list of strings
        # name may be specified explicitly or not
        name = name or Group.make_name(tokens)
        Entry.__init__(self, name, language, trans=trans)
        self.tokens = tokens
        if head:
            self.head = head
            if head in tokens:
                self.head_index = tokens.index(head)
            else:
                self.head_index = tokens.index(head.partition('_')[0])
#            self.head_index = tokens.index(head_tokens[0]) or tokens.index(head_tokens[1])
        else:
            self.head = tokens[head_index]
            self.head_index = head_index
        # Either None or a list of feat-val dicts for tokens that require them
        # Convert dicts to Features objects
        if isinstance(features, list):
            features = [Features(d) if d else None for d in features]
        self.features = features
        # Agr constraints: each a list of form
        # (node_index1, node_index2 . feature_pairs)
        self.agr = agr or None

    def __repr__(self):
        """Print name."""
        return '{}:{}'.format(self.name, self.id)

    @staticmethod
    def make_name(tokens):
        # Each token is either a string or a (string, feat_dict) pair
#        strings = []
#        for token in tokens:
#            if isinstance(token, str):
#                strings.append(token)
#            else:
#                form, feat_dict = token
#                fv = ['{}={}'.format(f, v) for f, v in feat_dict.items()]
#                fv = ','.join(fv)
#                strings.append("{}:{}".format(form, fv))
        return '.'.join(tokens)

    # Serialization

    def to_dict(self):
        """Convert the group to a dictionary to be serialized in a yaml file."""
        d = Entry.to_dict(self)
        d['words'] = self.tokens
        d['features'] = self.features
        d['agr'] = self.agr
        return d

    @staticmethod
    def from_dict(d, language, head):
        """Convert a dict (loaded from a yaml file) to a Group object."""
        tokens = d['words']
        features = d.get('features')
        agr = d.get('agr')
        name = d.get('name', '')
        trans = d.get('trans')
        p = Group(tokens, head=head, language=language, features=features,
                  agr=agr, name=name, trans=trans)
        return p

    def match_nodes(self, snodes, head_sindex, verbosity=0):
        """Attempt to match the group tokens (and features) with snodes from a sentence,
        returning the snode indices and root and unified features if any."""
#        print("Does {} match {}".format(self, snodes))
        match_snodes = []
        for index, token in enumerate(self.tokens):
            match_snodes1 = []
            feats = self.features[index] if self.features else None
            if verbosity:
                print(" Attempting to match {}".format(token))
            matched = False
            for node in snodes:
                if verbosity:
                    print("  Trying {}, token index {}, snode index {} head index {}".format(node, index, node.index, head_sindex))
                if index == self.head_index:
                    # This token is the head of the group
                    if node.index == head_sindex:
                        # This was already matched in lexicalization
#                if index == node.index == head_sindex:
                        # This is the token corresponding to the group head
                        node_match = node.match(token, feats)
                        if node_match == False:
                            # This has to match, so fail now
                            return False
                        else:
                            match_snodes1.append((node.index, node_match))
                            if verbosity:
                                print("  Head matched already".format(node))
                            matched = True
                            # Don't look further for an snode to match this token
                            break
                else:
                    node_match = node.match(token, feats)
                    if verbosity:
                        print('  Node {} match {}:{}, {}:: {}'.format(node, token, index, feats, node_match))
                    if node_match != False:
                        match_snodes1.append((node.index, node_match))
                        if verbosity:
                            print("  Matched node {}".format(node))
                        matched = True
            if not matched:
                if verbosity:
                    print("  {} not matched; failed".format(token))
                return False
            else:
                match_snodes.append(match_snodes1)
#        print("Group {}, s_indices {}".format(self, match_snodes))
        return match_snodes

    ### Translations

    ## Alignments: position correspondences, agreement constraints
    ## አድርጎ አያውቅም -> godhe hin beeku
    ## a: {positions: (1, 2),
    ##     agreements: {gen: gen},
    ##     featmaps: {((pers, 2), (num, 2)): ((pers, 3), (num, 2))}
    ##     }

    def add_alignment(self, trans):
        pass

class EntryError(Exception):
    '''Class for errors encountered when attempting to update an entry.'''

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)
    
