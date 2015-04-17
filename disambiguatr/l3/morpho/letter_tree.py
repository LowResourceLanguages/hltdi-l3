# -*- coding: utf-8 -*-
"""
This file is part of L3Morpho.

    L3Morpho is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    L3Morpho is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with L3Morpho.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------

Create a letter tree from a list of words.
Author: Michael Gasser <gasser@cs.indiana.edu>
"""

from .utils import *
import re

## Regular expressions for splitting lines in word file
RE_DEST = re.compile(r'([^ \t\[]+)(\s+[^ \t\[]+)?\s+([^ \t\[]+)\s*(\[.*\])?', re.U)
RE_NO_DEST = re.compile(r'([^ \t\[]+)(\s+[^ \t\[]+)?\s*(\[.*\])?', re.U)

def seg_units2chars(seg_units):
    """seg_units is [list, dict] for use in segmenting words."""
    # Initialize chars as a copy of the list of simple chars in seg_units
    chars = list(seg_units[0])
    for chs in seg_units[1].values():
        chars.extend(chs)
    return chars

def split_line(line, dest=False):
    """ -> input, output, weight
        -> input, output, dest, weight
    """
    match = RE_DEST.match(line) if dest else RE_NO_DEST.match(line)
    if not match:
        raise ValueError("Bad line in lex file: %r" % line)
    else:
        return match.groups()

def treeify_file(path, chars=[], seg_units=[], features=True, dest=False,
                 verbose=False):
    """Treeify words contained in a file, one word per line.

    input  (output)  (dest_state)  (features)

    dest=True means that the name of a destination FST state follows output (which
    must precede it)."""
    infile = open(path, encoding='utf-8')
    words = []
    any_out = False
    for line in infile:
        line = line.split('#')[0].strip() # strip comments
        if line:
#            if unic:
#                line = line.decode('utf8')
            elements = split_line(line, dest=dest)
            if dest:
                word, out, dst, feats = elements
                if out:
                    out = out.strip()
                    any_out = True
                words.append([word, out, (dst, feats)])
            else:
                word, out, feats = elements
                if out:
                    out = out.strip()
                    if out == "''":
                        out = None
                    if out:
                        any_out = True
                words.append([word, out, feats])
    infile.close()
    return treeify(words, chars=chars, seg_units=seg_units, output=any_out,
                   verbose=verbose)

def treeify(words, chars=[], seg_units=[], output=False, verbose=False):
    """Create a letter tree for words.

    If seg_units is given, words first need to be segmented.
    chars either given explicitly or generated from seg_units.
    If output is True, input and output words are zipped to create pairs of
    corresponding characters."""
    any_out = False
    words_stored = []
    if not chars:
        chars = seg_units2chars(seg_units)
    if seg_units:
        for word in words:
            in_word, out_word, feats = word
            if verbose > 1 and (in_word in words_stored):
                print(in_word, 'already stored')
            words_stored.append(in_word)
            if out_word:
                any_out = True
                # zip the input and output words together
                in_word = segment(in_word, seg_units)
                out_word = segment(out_word, seg_units)
                n_in = len(in_word)
                n_out = len(out_word)
                if n_in < n_out:
                    in_word.extend([''] * (n_out - n_in))
                elif n_out < n_in:
                    out_word.extend([''] * (n_in - n_out))
                # replace input and output with the zipped list
                word[:2] = [list(zip(in_word, out_word))]
            elif output:
                word[:2] = [[(c, c) for c in segment(in_word, seg_units)]]
            else:
                word[:2] = [segment(in_word, seg_units)]
            if not feats:
                # No weight, get rid of None in last position
                word[-1:] = []
    if any_out:
        return treeify_IO(words)
    else:
        return treeify1(words, chars)

def treeify_IO(words):
    tree = {}
    ls = []
    # use a copy of words because we'll delete some elements
    for w in words[:]:
        if not w[0]:
            ls.append(w[1] if len(w) > 1 else '')
            words.remove(w)
    if ls:
        tree[''] = ls
    for n, w in enumerate(words):
        cc = w[0][0]
#        print 'cc', cc
#        print 'word', w
        if not cc in tree:
            ls = [(w[0][1:], w[1] if len(w) > 1 else '')]
            for w1 in words[n+1:]:
                if w1[0] and w1[0][0] == cc:
                    ls.append((w1[0][1:], w1[1] if len(w1) > 1 else ''))
            if ls:
                if len(ls) == 1:
                    tree[cc] = ls[0]
                else:
                    tree[cc] = treeify_IO(ls)
    return tree

def treeify1(words, chars):
    tree = {}
    # words that are finished
    ls = []
    for w in words:
        if not w[0]:
            weight = w[1] if len(w) > 1 else ''
            if weight not in ls:
                ls.append(weight) # (w[1] if len(w) > 1 else '')
    if ls:
        tree[''] = ls
    for c in chars:
        ls = []
        for w in words:
            if w[0] and w[0][0] == c:
                ls.append((w[0][1:], w[1] if len(w) > 1 else ''))
        if ls:
            if len(ls) == 1:
                tree[c] = ls[0]
            else:
                tree[c] = treeify1(ls, chars)
    return tree

def print_tree(tree, level=0):
    for k,v in tree.items():
        if k:
            if isinstance(v, dict):
                print((' ' * level), k, end=' ')
                if '' in v:
                    print('<-', end=' ')
                    for lex in v['']:
                        print(lex, end=' ')
                print()
                print_tree(v, level=level+3)
            else:
                print((' ' * level), end=' ')
                print((k + ''.join(v[0])), end=' ')
                print('<-', end=' ')
                if v[1]: print(v[1], end=' ')
                print()

def search(word, tree):
    print('Searching for', word, 'in', tree)
    if word:
        entry = tree.get(word[0])
        if entry:
            if isinstance(entry, dict):
                return search(word[1:], entry)
            else:
                if word[1:] == list(entry[0]):
                    return [entry[1]]
    else:
        return tree.get('')
