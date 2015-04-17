########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2013, 2014
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
# 2013.10.27
# -- Created.
#    Process a corpus, either parsing or translating it, possibly also
#    learning new entries or crosslexes.

from .xdg import *

class Corpus:

    CHAR = '$'

    def __init__(self, name,
                 # Source and target language abbreviations
                 source=None, target=None,
                 # Whether there is semantics
                 semantics=False,
                 # Grammar to use for the language(s)
                 grammar='chunk',
                 # Files
                 infiles=None, outfile=None,
                 # Text
                 text=None,
                 # Whether to learn new lexical entries for unknown words/lexemes
                 learn_lex=True):
        self.name = name
        self.grammar = grammar
        self.learn_lex = learn_lex
        languages = self.load(source, target, grammar)
        self.source = languages[0]
        self.target = languages[1] if target else None
        self.bitext = True if target else False
        self.semantics = semantics
        if self.learn_lex:
            self.learner = Learner(source=self.source,
                                   target=self.target,
                                   semantics=self.semantics,
                                   grammar=self.grammar)
        # File(s) for reading in corpus
        self.infiles = infiles
        # File for writing analysis / translation
        self.outfile = outfile
        # Corpus text
        # Either a list of sentences (strings) or a list of lists of sentences.
        self.text = text

    def __repr__(self):
        return '{}{}'.format(Corpus.CHAR, self.name)

    def read(self, file1, file2=None):
        """Read in corpus text. Files contain sentence-segmented texts.
        If self.bitext is True, there is a file2, and the sentences in
        file1 and file2 are aligned."""
        text = []
        with open(file1, encoding='utf8') as f1:
            text = [s for s in f1]
        if file2:
            with open(file2, endoding='utf8') as f2:
                text = zip(text, [s for s in f2])
        self.text = text

    def process(self):
        """Process corpus."""

    def load(self, src_abbrev, targ_abbrev, grammar, debug=0):
        """Load lexicon and morphology for language(s)."""
        lang_abbrevs = [src_abbrev]
        if targ_abbrev:
            lang_abbrevs.append(targ_abbrev)
        return Language.load_langs(lang_abbrevs, grammar=grammar,
                                   force=True,
                                   # later get rid of this
                                   flatten=True,
                                   pickle=True,
                                   learn=self.learn_lex,
                                   verbosity=debug)

    def proc_sentence(self, sentence, debug=0):
        """Parse and possibly translate sentence. If this fails and self.learn_lex is True,
        attempt to learn a new entry or crosslex."""
        if self.bitext:
            # Translate the sentence from source to target language
            xdg = XDG(sentence, self.source,
                      target=self.target,
                      load_semantics=self.semantics,
                      reload=False,
                      process=TRANSLATE,
#                      pre_arcs=arcs, pre_agrs=agrs,
                      transfer_xlex=not self.semantics,
                      grammar=self.grammar,
#                      distributor=distributor,
                      verbosity=debug, report=1 if debug else 0)
        else:
            # Analyze the source sentence
            xdg = XDG(sentence, self.source, target=None,
                      load_semantics=self.semantics,
                      reload=False,
                      process=PARSE,
#                      pre_arcs=arcs, pre_agrs=agrs,
                      transfer_xlex=False,
                      grammar=self.grammar,
#                      distributor=distributor, 
                      verbosity=debug, report=1 if debug else 0)
        sols = xdg.solve(verbose=False)
        if sols:
            output = []
            for s in sols:
                if self.bitext:
                    output.append(s.io())
                else:
                    s.display()
        else:
            # Processing failed; look for unknown word
            print("Couldn't process \"{}\"".format(sentence))
            novel = []
            for node in xdg.nodes:
                if node.is_novel():
                    novel.append(node)
            if novel and self.learn_lex:
                # Only for source language (monolingual) case
                self.learner.mono(self.source, sentence, sols, novel)
        return sols
