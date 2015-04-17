#   
#   Hiiktuu languages: dictionaries of lexical/grammatical entries
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

# 2014.02.09
# -- Created
# 2014.02.10
# -- Made entries a separate class.
# 2014.02.15
# -- Methods for serializing and deserializing languages (using YAML).
# 2014.03.24
# -- Words, lexemes, and classes are all in the same dictionary (self.words).
#    Lexemes start with %, classes with $.
# 2014.04.17
# -- Analysis and generation dicts for particular wordforms.
# 2014.04.30
# -- Eliminated entry types in lexicon other than Groups and forms.

from .entry import *

import os, yaml

LANGUAGE_DIR = os.path.join(os.path.dirname(__file__), 'languages')

class Language:
    """Dictionaries of words, lexemes, grammatical features, and
    lexical classes."""

    languages = {}
    
    def __init__(self,
                 name, abbrev,
                 words=None, lexemes=None, grams=None, classes=None,
                 mwes=None, groups=None, forms=None,
                 genforms=None):
        """Initialize dictionaries and names."""
        self.name = name
        self.abbrev = abbrev
        # Words, lexemes, classes
        self.words = words or {}
        # Combine with words in a single lexicon?
#        self.lexemes = lexemes or {}
#        self.grams = grams or {}
#        self.classes = classes or {}
#        self.mwes = mwes or {}
        self.forms = forms or {}
        self.groups = groups or {}
        # Dict of groups with names as keys
        self.groupnames = {}
#        # Record possibilities for dependency labels, feature values, order constraints
#        self.possible = {}
        # Record whether language has changed since last loaded
        self.changed = False
        # Dictionary of morphologically generated words:
        # {lexeme: {(feat, val): {(feat, val): wordform,...}, ...}, ...}
        self.genforms = genforms or {}
        Language.languages[abbrev] = self

    def __repr__(self):
        """Print name."""
        return '<<{}>>'.format(self.name)

    def to_dict(self):
        """Convert the language to a dictionary to be serialized as a yaml file."""
        d = {}
        d['name'] = self.name
        d['abbrev'] = self.abbrev
#        d['possible'] = self.possible
        # Entries: each is a dict, whose values must be converted to dicts
#        if self.grams:
#            grams = {}
#            for k, v in self.grams.items():
#                grams[k] = v.to_dict()
#            d['grams'] = grams
#        if self.classes:
#            classes = {}
#            for k, v in self.classes.items():
#                classes[k] = v.to_dict()
#            d['classes'] = classes
        # Lexemes and words should probably be separate dictionaries (and files).
#        if self.lexemes:
#            lexemes = {}
#            for k, v in self.lexemes.items():
#                lexemes[k] = v.to_dict()
#            d['lexemes'] = lexemes
#        if self.words:
#            words = {}
#            for k, v in self.words.items():
#                # Words are lists
#                words[k] = [lex.to_dict() for lex in v]
#            d['words'] = words
#        if self.mwes:
#            mwes = {}
#            for k, v in self.mwes.items():
#                mwes[k] = [m.to_dict() for m in v]
#            d['mwes'] = mwes
        if self.groups:
            groups = {}
            for head, v in self.groups.items():
                groups[head] = [g.to_dict() for g in v]
            d['groups'] = groups
        if self.forms:
            forms = {}
            for k, v in self.forms.items():
                # v is an fv dict or a list of fv dicts
                forms[k] = v
        return d

    def write(self, directory, filename=''):
        """Serialize the language."""
        filename = filename or self.abbrev + '.lg'
        path = os.path.join(directory, filename)
        with open(path, 'w', encoding='utf8') as file:
            yaml.dump(self.to_dict(), file)

    @staticmethod
    def from_dict(d, reverse=True):
        """Convert a dict (loaded from a yaml file) to a Language object."""
        l = Language(d.get('name'), d.get('abbrev'))
        l.possible = d.get('possible')
#        grams = d.get('grams')
#        if grams:
#            l.grams = {}
#            for k, v in grams.items():
#                l.grams[k] = Entry.from_dict(v, l)
#        classes = d.get('classes')
#        if classes:
#            l.classes = {}
#            for k, v in classes.items():
#                l.classes[k] = Lex.from_dict(v, l)
#        lexemes = d.get('lexemes')
#        if lexemes:
#            l.lexemes = {}
#            for k, v in lexemes.items():
#                l.lexemes[k] = Lex.from_dict(v, l)
#        words = d.get('words')
#        if words:
#            l.words = {}
#            for k, v in words.items():
#                l.words[k] = [Lex.from_dict(lex, l) for lex in v]
#        mwes = d.get('mwes')
#        if mwes:
#            l.mwes = {}
#            for k, v in mwes.items():
#                l.mwes[k] = [MWE.from_dict(m, l) for m in v]
        groups = d.get('groups')
        if groups:
            l.groups = {}
            for head, v in groups.items():
                group_objs = [Group.from_dict(g, l, head) for g in v]
                l.groups[head] = group_objs
                # Add groups to groupnames dict
                for go in group_objs:
                    l.groupnames[go.name] = go
        forms = d.get('forms')
        if forms:
            l.forms = {}
            for k, v in forms.items():
                # v should be a dict or a list of dicts
                # Convert features value to a Features object
                if isinstance(v, dict):
                    if 'features' in v:
                        v['features'] = Features(v['features'])
                else:
                    for d in v:
                        if 'features' in d:
                            d['features'] = Features(d['features'])
                l.forms[k] = v
                if reverse:
                    # Add item to genform dict
                    if isinstance(v, dict):
                        if 'seg' not in v:
                            l.add_genform(k, v['root'], v.get('features'))
                    else:
                        for d in v:
                            l.add_genform(k, d['root'], d.get('features'))
        return l

    @staticmethod
    def read(path):
        """Create a Language from the contents of a yaml file, a dict
        that must be then converted to a Language."""
        with open(path, encoding='utf8') as file:
            dct = yaml.load(file)
            return Language.from_dict(dct)

    @staticmethod
    def load(*abbrevs):
        languages = []
        for abbrev in abbrevs:
            if abbrev in Language.languages:
                language = Language.languages[abbrev]
                languages.append(language)
            else:
                path = os.path.join(LANGUAGE_DIR, abbrev + '.lg')
                try:
                    language = Language.read(path)
                    languages.append(language)
                    print("Loading language {}".format(language))
                except IOError:
                    print("That language doesn't seem to exist.")
                    return
        return languages

    ### Basic setters. Create entries (dicts) for item. For debugging purposes, include name
    ### in entry.

##    def add_word(self, word, cls=None, mwe=False):
##        entry = Lex(word, self, cls=cls, mwe=mwe)
##        if word in self.words:
##            self.words[word].append(entry)
##        else:
##            self.words[word] = [entry]
##        self.changed = True
##        return entry
##
##    def add_lexeme(self, lexeme, cls=None):
##        if lexeme in self.words:
##            s = "Lexeme {} already in dictionary"
##            raise(LanguageError(s.format(lexeme)))
##        entry = Lex(lexeme, self, cls=cls)
##        # Maybe not a list since there's always only one
##        self.words[lexeme] = [entry]
##        self.changed = True
##        return entry

    def add_form(self, form, dct, reverse=True):
        """Form dict has root, features, cats.
        If reverse it True, also add the form to the genforms dicdt."""
        if form not in self.forms:
            self.forms[form] = dct
        else:
            entry = self.forms[form]
            if isinstance(entry, dict):
                # Make this the second entry
                self.forms[form] = [entry, dct]
            else:
                # There are already two or more entries in a list
                entry.append(dct)
        if reverse:
            lexeme = dct['root']
            features = dct['features']
            self.add_genform(form, lexeme, features)

    def add_genform(self, form, lexeme, features):
        """Add the form to a lexeme- and feature-keyed dict."""
        if lexeme not in self.genforms:
            self.genforms[lexeme] = {}
        featdict = self.genforms[lexeme]
        # features is a Features object; convert it to a list of tuples
        features = tuple(features.to_list())
        featdict[features] = form
#        feat = features.pop(0)
#        self.make_featdict(featdict, feat, features, form)

#    @staticmethod
#    def make_featdict(featdict, feat, features, form):
#        """Make a feat-value dict with the form as final value."""
#        if not features:
#            featdict[feat] = form
#            return
#        if feat not in featdict:
#            featdict[feat] = {}
#        new_feat = features.pop(0)
#        Language.make_featdict(featdict[feat], new_feat, features, form)

##    def add_class(self, cls):
##        if cls in self.words:
##            s = "Class {} already in dictionary"
##            raise(LanguageError(s.format(cls)))
##        entry = Lex(cls, self)
##        # Maybe not a list since there's always only one
##        self.words[cls] = [entry]
##        self.changed = True
##        return entry
##
##    def add_mwe(self, name, head, head_order=None, head_lexeme=False):
##        entry = MWE(name, self, head, head_order=head_order, head_lexeme=head_lexeme)
##        if head not in self.mwes:
##            self.mwes[head] = []
##        self.mwes[head].append(entry)
##        self.changed = True
##        return entry

    def add_group(self, tokens, head_index=-1, head='', name='', features=None):
        group = Group(tokens, head_index=head_index, head=head,
                      language=self, name=name, features=features)
#        print('Group {}, head {}'.format(group, group.head))
        if features:
            head_i = tokens.index(group.head)
            head_feats = features[head_i]
        else:
            head_feats = None
        self.add_group_to_lexicon(group.head, group, head_feats)
        self.groupnames[group.name] = group
        self.changed = True
        return group

    def add_group_to_lexicon(self, head, group, features):
        if not features:
            # Add the group to the list of groups for the head word/lexeme
            if head not in self.groups:
                self.groups[head] = {}
            if () not in self.groups[head]:
                self.groups[head][()] = []
            self.groups[head][()].append(group)
        else:
            # Convert fv dict to an alphabetized tuple of fv pairs
            fvs = list(features.items())
            fvs.sort()
            fvs = tuple(fvs)
            if head not in self.groups:
                self.groups[head] = {}
            if fvs not in self.groups[head]:
                self.groups[head][fvs] = []
            self.groups[head][fvs].append(group)

##    def add_gram(self, gram, feature, count=1):
##        """A gram, for example, 'plural', must have a feature, for example,
##        'number'."""
##        if gram in self.grams:
##            s = "Grammatical morpheme {} already in dictionary"
##            raise(LanguageError(s.format(gram)))
##        entry = Entry(gram, self)
##        self.grams[gram] = entry
##        entry.feature = feature
##        self.grams[gram] = entry
##        self.record_gram(gram, feature, count)
##        self.changed = True
##        return entry
##
##    def record_gram(self, name, feature, count):
##        """Record the gram value and its count under its feature name."""
##        if 'features' not in self.possible:
##            self.possible['features'] = {}
##        if feature not in self.possible['features']:
##            self.possible['features'][feature] = {}
##        self.possible['features'][feature][name] = count
##
##    def get_possible_feat_values(self, feature):
##        """Possible values and associated counts for grammatical feature."""
##        if 'features' not in self.possible:
##            self.possible['features'] = {}
##        return self.possible['features'].get(feature)

    ### Basic getters.

##    def get_words(self, word):
##        """Returns a list of word entries."""
##        return self.words.get(word)
##
##    def get_class(self, cls):
##        """Returns a single class entry."""
##        return self.words.get(cls)[0]
##
##    def get_gram(self, gram):
##        """Returns a single gram feature value entry."""
##        return self.grams.get(gram)
##
##    def get_lexeme(self, lexeme):
##        """Returns a single lexeme entry."""
##        return self.words.get(lexeme)[0]

    ### Generation of word forms

    def generate(self, root, features, verbosity=0):
        if verbosity:
            print("Generating {}:{}".format(root, features))
        if root not in self.genforms:
            return [root]
        if not features:
            features = Features({})
#        if not features:
#            # Just return the "root"
#            return [root]
#        if root not in self.genforms:
#            print("Impossible to generate root {}".format(root))
#            return
        gendict = self.genforms[root]
        # List of matching forms
        result = []
        for feat_list, form in gendict.items():
            if features.match_list(feat_list):
                result.append(form)
#            print('Feat list {}, form {}'.format())
        if not result:
            print("No forms found for {}:{}".format(root, features))
        return result

##    ## Dependencies (word, lexeme, class entries)
##
##    def record_label(self, label):
##        """Record the dependency label in the set of possible labels."""
##        if 'deplabels' not in self.possible:
##            self.possible['deplabels'] = []
##        if label not in self.possible['deplabels']:
##            self.possible['deplabels'].append(label)
##
##    def get_possible_labels(self):
##        return self.possible.get('deplabels')
##    
##    ## Order constraints
##    ## A constraint is a tuple of dependency labels and '^' representing the head
##
##    def record_order(self, constraint):
##        """Record the constraint tuple in the set of possible constraints for the language."""
##        if 'order' not in self.possible:
##            self.possible['order'] = []
##        if constraint not in self.possible['order']:
##            # Append a *copy* of the constraint list
##            self.possible['order'].append(constraint[:])
##
##    def get_possible_orders(self):
##        return self.possible.get('order')
##
##    ## Agreement constraints
##
##    def record_agr(self, constraint):
##        """An agreement constraint is a tuple consisting of
##        dep label, head feature, dependent feature."""
##        if 'agr' not in self.possible:
##            self.possible['agr'] = []
##        if constraint not in self.possible['agr']:
##            # Append a *copy* of the constraint list
##            self.possible['agr'].append(constraint[:])

class LanguageError(Exception):
    '''Class for errors encountered when attempting to update the language.'''

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)

