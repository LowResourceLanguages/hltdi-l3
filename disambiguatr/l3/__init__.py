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

Author: Michael Gasser <gasser@cs.indiana.edu>
"""

# _version = '2.1.1'
_version = '1.0'

from . import morpho

print('\n>>>>> This is L3Morpho, version', _version, '<<<<<\n')

# print('\n>>>>> This is HornMorpho, version', _version, '<<<<<\n')

def load_lang(language, phon=False, segment=False, load_morph=True, verbose=False):
    """Load a language's morphology.

    @param language: a language label
    @type  language: string
    """
    morpho.load_lang(language, phon=phon, segment=segment, load_morph=load_morph,
                     verbose=verbose)

def seg_word(language, word, root=False, citation=False, gram=False,
             roman=False, raw=False):
    '''Segment a single word and print out the results.
    
    @param language: abbreviation for a language
    @type  language: string
    @param word:     word to be analyzed
    @type  word:     string or unicode
    @param root:     whether a root is to be included in the analyses
    @type  root:     boolean
    @param citation: whether a citation form is to be included in the analyses
    @type  citation: boolean
    @param gram:     whether a grammatical analysis is to be included
    @type  gram:     boolean
    @param roman:    whether the language is written in roman script
    @type  roman:    boolean
    @param raw:      whether the analyses should be returned in "raw" form
    @type  raw:      boolean
    @return:         a list of analyses (only if raw is True)
    @rtype:          list of (root, feature structure) pairs
    '''
    language = morpho.get_language(language, phon=False, segment=True)
    if language:
        analysis = language.anal_word(word, preproc=not roman,
                                      postproc=not roman and not raw,
                                      root=root, citation=citation, gram=gram,
                                      segment=True, only_guess=False,
                                      string=not raw)
        if raw:
            if gram:
                return [(anal[1], anal[-1]) for anal in analysis]
            else:
                return analysis

def seg_file(language, infile, outfile=None, root=False, citation=False, gram=False,
             preproc=True, postproc=True, start=0, nlines=0):
    '''Analyze the words in a file, writing the analyses to outfile.

    @param infile:   path to a file to read the words from
    @type  infile:   string
    @param outfile:  path to a file where analyses are to be written
    @type  outfile:  string
    @param root:     whether a root is to be included in the analyses
    @type  root:     boolean
    @param citation: whether a citation form is to be included in the analyses
    @type  citation: boolean
    @param gram:     whether a grammatical analysis is to be included
    @type  gram:     boolean
    @param preproc:  whether to preprocess inputs
    @type  preproc:  boolean
    @param postproc: whether to postprocess outputs
    @type  postproc: boolean
    @param start:    line to start analyzing from
    @type  start:    int
    @param nlines:   number of lines to analyze (if not 0)
    @type  nlines:   int
    '''
    language = morpho.get_language(language, phon=False, segment=True)
    if language:
        language.anal_file(infile, outfile, root=root, citation=citation, gram=gram,
                           pos=None, preproc=preproc, postproc=postproc,
                           segment=True, only_guess=False, guess=False,
                           start=start, nlines=nlines)

def anal_word(language, word, root=True, citation=True, gram=True,
              non_roman=True, roman=False, segment=False, guess=False,
              raw=False):
    '''Analyze a single word, trying all available analyzers, and print out
    the analyses.
    
    @param language: abbreviation for a language
    @type  language: string
    @param word:     word to be analyzed
    @type  word:     string or unicode
    @param root:     whether a root is to be included in the analyses
    @type  root:     boolean
    @param citation: whether a citation form is to be included in the analyses
    @type  citation: boolean
    @param gram:     whether a grammatical analysis is to be included
    @type  gram:     boolean
    @param non_roman: whether the language is written in non-roman script
                      (included for backwards compatibility)
    @type  non_roman: boolean
    @param roman:    whether the language is written in roman script
    @type  roman:    boolean
    @param segment:  whether to return the segmented input string rather than
                     the root/stem
    @type  segment:  boolean
    @param guess:    try only guesser analyzer
    @type guess:     boolean
    @param raw:      whether the analyses should be returned in "raw" form
    @type  raw:      boolean
    @return:         a list of analyses (only if raw is True)
    @rtype:          list of (root, feature structure) pairs
    '''
    language = morpho.get_language(language, phon=False, segment=segment)
    if language:
        analysis = language.anal_word(word, preproc=non_roman and not roman,
                                      postproc=(non_roman and not roman) and not raw,
                                      root=root, citation=citation, gram=gram,
                                      segment=segment, only_guess=guess,
                                      string=not raw)
        if raw:
            return [(anal[1], anal[-1]) for anal in analysis]

def anal_file(language, infile, outfile=None,
              root=True, citation=True, gram=True,
              preproc=True, postproc=True, guess=False,
              start=0, nlines=0):
    '''Analyze the words in a file, writing the analyses to outfile.

    @param infile:   path to a file to read the words from
    @type  infile:   string
    @param outfile:  path to a file where analyses are to be written
    @type  outfile:  string
    @param root:     whether a root is to be included in the analyses
    @type  root:     boolean
    @param citation: whether a citation form is to be included in the analyses
    @type  citation: boolean
    @param gram:     whether a grammatical analysis is to be included
    @type  gram:     boolean
    @param preproc:  whether to preprocess inputs
    @type  preproc:  boolean
    @param postproc: whether to postprocess outputs
    @type  postproc: boolean
    @param guess:    try only guesser analyzer
    @type guess:     boolean
    @param start:    line to start analyzing from
    @type  start:    int
    @param nlines:   number of lines to analyze (if not 0)
    @type  nlines:   int
    '''
    language = morpho.get_language(language)
    if language:
        language.anal_file(infile, outfile, root=root, citation=citation, gram=gram,
                           pos=None, preproc=preproc, postproc=postproc,
                           only_guess=guess,
                           start=start, nlines=nlines)

##def anal_gui(language, infile, outfile=None):
##    '''Open a window for reading in a file where words can be clicked for analysis.'''
##    language = morpho.get_language(language)
##    if language:
##        app = morpho.anal_gui.App(language, fname=infile)
##        app.MainLoop()

def gen(language, root, features=[], pos=None, guess=False, phon=False, non_roman=True):
    '''Generate a word, given stem/root and features (replacing those in default).
    If pos is specified, check only that POS; otherwise, try all in order until one succeeeds.

    @param root:     root or stem of a word
    @type  root:     string (roman)
    @param features: grammatical features to be added to default
    @type  features: string containing bracketed expression, e.g., '[sb=[+p1,+plr]]'
    @param pos:      part-of-speech: use only the generator for this POS
    @type  pos:      string
    @param guess:    whether to use guess generator if lexical generator fails
    @type  guess:    boolean
    @param non_roman: whether the language uses a non-roman script
    @type  non_roman: boolean
    '''
    language = morpho.get_language(language, segment=False, phon=phon)
    if language:
        morf = language.morphology
        if pos:
            posmorph = morf[pos]
            output = posmorph.gen(root, update_feats=features,
                                  postproc=non_roman, guess=guess)
            if output:
                print(output[0][0])
                return
        else:
            for posmorph in list(morf.values()):
                output = posmorph.gen(root, update_feats=features,
                                      postproc=non_roman, guess=guess)
                if output:
                    print(output[0][0])
                    return
        print("This word can't be generated!")

def phon_word(lang_abbrev, word, gram=False, raw=False,
              postproc=False):
    '''Convert a form in non-roman to roman, making explicit features that are missing in the orthography.
    @param lang_abbrev: abbreviation for a language
    @type  lang_abbrev: string
    @param word:     word to be analyzed
    @type  word:     string or unicode
    @param gram:     whether a grammatical analysis is to be included
    @type  gram:     boolean
    @param postproc: whether to run postpostprocess on the form
    @type  postproc: boolean
    @return:         a list of analyses
    @rtype:          list of (root, feature structure) pairs
    '''
    language = morpho.get_language(lang_abbrev, phon=True, segment=False)
    if language:
        return language.ortho2phon(word, gram=gram, raw=raw, return_string=False,
                                   postpostproc=postproc)

def phon_file(lang_abbrev, infile, outfile=None, gram=False,
              word_sep='\n', anal_sep=' ', print_ortho=True,
              postproc=False,
              start=0, nlines=0):
    '''Convert non-roman forms in file to roman, making explicit features that are missing in the orthography.
    @param lang_abbrev: abbreviation for a language
    @type  lang_abbrev: string
    @param infile:   path to a file to read the words from
    @type  infile:   string
    @param outfile:  path to a file where analyses are to be written
    @type  outfile:  string
    @param gram:     whether a grammatical analysis is to be included
    @type  gram:     boolean
    @param word_sep: separator between words (when gram=False)
    @type  word_sep: string
    @param anal_sep: separator between analyses (when gram=False)
    @type  anal_sep: string
    @param print_ortho: whether to print out orthographic form (when gram=False)
    @type  print_ortho: boolean
    @param postproc: whether to run postpostprocess on the form
    @type  postproc: boolean
    @param start:    line to start analyzing from
    @type  start:    int
    @param nlines:   number of lines to analyze (if not 0)
    @type  nlines:   int
    '''
    language = morpho.get_language(lang_abbrev, phon=True, segment=False)
    if language:
        language.ortho2phon_file(infile, outfile=outfile, gram=gram,
                                 word_sep=word_sep, anal_sep=anal_sep, print_ortho=print_ortho,
                                 postpostproc=postproc,
                                 start=start, nlines=nlines)

def get_features(language, pos=None):
    '''Return a dict of features and their possible values for each pos.

    @param language:  abbreviation for a language
    @type  language:  string
    @param pos:       part-of-speech; if provided, return only
                      features for this POS
    @type  pos:       string
    @return:          dictionary of features and possible values; if
                      there is more than one POS, list of such
                      dictionaries.
    @rtype:           dictionary of feature (string): possible values (list)
                      pairs or list of (pos, dictionary) pairs
    '''
    language = morpho.get_language(language)
    if language:
        morf = language.morphology
        if pos:
            return morf[pos].get_features()
        elif len(morf) == 1:
            return list(morf.values())[0].get_features()
        else:
            feats = []
            for pos, posmorph in list(morf.items()):
                feats.append((pos, posmorph.get_features()))
            return feats
