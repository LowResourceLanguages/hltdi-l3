#   
#   Learning Hiiktuu groups
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

# 2014.07.04
# -- Created
#    Possible classes:
#    Pattern -- head (root or POS), dependent (root or POS);
#       relative position; gaps
#    Corpus -- list (dict?) of sentences, consisting of lists
#       of word strings or word representations

# Need this to parse and interpret features

from .features import *
from .utils import *

class Corpus(list):
    """A list of sentences, each a tuple of words or word-representation Features objects."""

    def __init__(self, name=''):
        list.__init__(self)
        self.name = name or 'anon'
        # Store string->Features mapping here to save time in reading in corpus
        self.feat_cache = {}

    def read(self, file, lines=0, expand=True):
        """Extend the corpus with a list of lists of word-analysis strings.
        file is a sentence-by-line file with words analyzed by L3Morpho anal_file()
        with minim=True. If expand is True, expand word analyses into dicts."""
        with open(file, encoding='utf8') as f:
            n = 0
            for line in f:
                if lines and n >= lines:
                    return
                n += 1
                if n % 50000 == 0:
                    print("Read {} lines".format(n))
                words = line.split()
                if expand:
                    for i, word in enumerate(words):
                        if ';' in word:
                            # There is an analysis of the word
                            form, analyses = word.split(';')
                            w = [form]
                            for analysis in analyses.split('|'):
                                anal_attribs = analysis.split(':')
                                root = anal_attribs[0]
                                pos = False
                                feats = False
                                if root == '*':
                                    # Root is same as wordform, so don't record
                                    root = False
#                                if len(anal_attribs) > 1:
#                                    pos = anal_attribs[1]
                                if len(anal_attribs) > 2:
                                    fs = anal_attribs[2]
                                    if fs in self.feat_cache:
                                        feats = self.feat_cache[fs]
                                    else:
                                        feats = Features.from_string(fs)
                                        feats['p'] = anal_attribs[1]
                                        self.feat_cache[fs] = feats
                                elif len(anal_attribs) == 2:
                                    # POS but no additional grammatical constraints
                                    pos = anal_attribs[1]
                                    if pos in self.feat_cache:
                                        feats = self.feat_cache[pos]
                                    else:
                                        feats = Features({'p': anal_attribs[1]})
                                        self.feat_cache[pos] = feats
                                w.extend([root, feats])
                            words[i] = tuple(w)
                self.append(tuple(words))

    def __repr__(self):
        return "C~~{}".format(self.name)

    @staticmethod
    def get_root(word, word_tup):
        if isinstance(word_tup, str):
            return None
        root = word_tup[0]
        if not root:
            return word
        return root

    @staticmethod
    def get_pos(word, word_tup):
        gram = word_tup[1]
        if gram:
            return gram.get('p', False)
        return False

    @staticmethod
    def get_gram(word, word_tup):
        return word_tup[1]

    @staticmethod
    def get_form_anals(word):
        """word is a string (form) or a tuple consisting of form following by
        unsegmented pairs representing analyses. Return a tuple consisting of the
        wordform followed by pairs (root, features) representing analyses.
        """
        if isinstance(word, str):
            return word, ()
        else:
            form = word[0]
            anals = [list(word[i+1:i+3]) for i in range(0, len(word)-1, 2)]
            # Replace False root with form
            for index, (root, gram) in enumerate(anals):
                if not root:
                    anals[index][0] = form
            return form, anals

    def count_roots(self, roots, sort=True):
        """Return either a dict or a sorted list of roots by their frequency."""
        d = {}
        constraint = (None, (roots, None))
        for sent in self:
            for w in sent:
                match = Pattern.match_item(w, constraint)
                if match:
                    root = match[0]
                    if root in d:
                        d[root] += 1
                    else:
                        d[root] = 1
                        # Don't bother to look for another match with this word
                        continue
        if sort:
            # Sort by frequency
            l = list(d.items())
            l.sort(key=lambda x: x[1], reverse=True)
            return l
        else:
            return d

    def sents(self, constraints=(None, None)):
        """Find all sentences containing word with features matching feats if any.
        constraints is (forms, (root, gram))
        forms is a set of wordforms.
        root is None or a string or a set of strings.
        feats is None or a list/tuple of feat-val constraint tuples.
        Return list of pairs of sentence indices and word indices with sentences."""
        result = []
#        if isinstance(forms, str):
#            forms = {forms}
        for sindex, sent in enumerate(self):
            indices = []
            for index, w in enumerate(sent):
                if Pattern.match_item(w, constraints):
                    indices.append(index)
#                s_form, analyses = Corpus.get_form_anals(w)
#                if not root:
#                    if s_form in forms:
#                        indices.append(index)
#                else:
#                    for rg in analyses:
#                        if Pattern.match_constraints(rg, (root, feats)):
#                            indices.append(index)
#                            break
            if indices:
                result.append((sindex, indices))
        return result

class Pattern(list):
    """A list of items to look for in sentences.
    Each list element is a pair:
    ({set of word forms}, ({set of roots}, (tuple of grammatical constraints)}}
    Any of the three components may be None.
    """

    def __init__(self, lst):
        list.__init__(self, lst)
        self.complete()

    def __repr__(self):
        return "&{}".format(list.__repr__(self))

    def complete(self):
        """Expand incomplete items."""
        for index, item in enumerate(self):
            if isinstance(item, str):
                # A single form
                self[index] = ({item}, None)
            elif isinstance(item, set):
                # A set of forms
                self[index] = (item, None)
            elif isinstance(item, tuple):
                if isinstance(item[1], str):
                    # A single root string
                    self[index] = (None, ({item[1]}, None))
                elif isinstance(item[1], set):
                    # A set of roots
                    self[index] = (None, (item[1], None))

    @staticmethod
    def match_item(s_word, constraints=(None, None), gap=0):
        """Does word from sentence match various constraints?
        Either the form should match or one or more other constraints
        must."""
        s_form, s_anals = Corpus.get_form_anals(s_word)
        forms, rg = constraints
        if forms:
            if s_form in forms:
                return s_form
        else:
            for s_rg in s_anals:
                if Pattern.match_constraints(s_rg, rg):
                    return s_rg
        return None

    @staticmethod
    def match_constraints(w_rg, p_rg):
        """Does a pair of word properties (root, grammatical features/POS)
        match the corresponding constraints (if any) from a pattern?
        Pattern root constraint is a string or a set of root strings."""
        roots, grams = zip(w_rg, p_rg)
        wr, pr = roots
        if isinstance(pr, str):
            pr = {pr}
        if pr and wr not in pr:
            # Either there is no pattern root constraint or the
            # roots must be equal
            return False
        wg, pg = grams
        if pg and wg and not wg.match_list(pg):
            # Either there is no list of feature pair constraints in
            # the pattern or the word has no grammatical FS or the
            # word's FS must match the feature pair list
            return False
        return True

    def match(self, sentence, verbose=True):
        """Does the Pattern match a sequence in the sentence?
        If so, return the boundary indices of matching words within the
        sentence."""
        p_index = 0
        p_item = self[0]
        s_start = 0
        for s_index, word in enumerate(sentence):
            if verbose:
                print("Matching pattern item {} against sentence item #{}: {}".format(p_item, s_index, word))
            if Pattern.match_item(word, p_item):
                if verbose:
                    print("{} matches pattern element {}: {}".format(word, p_index, p_item))
                if p_index == 0:
                    s_start = s_index
                p_index += 1
                if p_index == len(self):
                    # Done with pattern; return bounds (end is last index + 1)
                    return s_start, s_index + 1
                # Not done, get next element
                p_item = self[p_index]
            elif p_index > 0:
                # Don't allow for gaps, so if the next item doesn't
                # match, go back to the beginning
                p_index = 0
                p_item = self[0]
        return False

    def search(self, corpus, verbose=False):
        """Search a corpus for instances of this pattern,
        returning a list of their locations in the corpus."""
        result = []
        for sentence in corpus:
            matched = self.match(sentence, verbose=verbose)
            if matched:
                result.append(matched)
        return result
