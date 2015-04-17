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

Author: Michael Gasser <gasser@cs.indiana.edu>

Language objects, with support mainly for morphology (separate
Morphology objects defined in morphology.py).
"""

import os, sys

FST_DIRECTORY = os.path.join(os.path.dirname(__file__),
                             os.path.pardir,
                             'FST')

from .morphology import *
# from Graphics.graphics import *
from .anal import *

class LLL:
    version = 1.0

class Language:
    '''A single Language, currently only handling morphology.'''

    def __init__(self, label, abbrev='', preproc=None, postproc=None,
                 # There may be a further function for post-processing
                 postpostproc=None,
                 seg_units=None,
                 citation_separate=True, msgs=None):
        """
        Set some basic language-specific attributes.

        @param preproc            Whether to pre-process input to analysis, for example,
                                  to convert non-roman to roman characters
        @param postproc           Whether to post-process output of generation, for
                                  example, to convert roman to non-roman characters
        @param seg_units          Segmentation units (graphemes)
        @param citation_separate  Whether citation form of words is separate from roots
        @param msgs               Messages in the languages (or some other)
        """
        self.label = label
        self.abbrev = abbrev or label[:3]
        self.morphology = None
        self.preproc = preproc
        self.postproc = postproc
        self.postpostproc = postpostproc
        self.seg_units = seg_units or []
        self.citation_separate = citation_separate
        self.msgs = msgs or {}

    def __str__(self):
        return self.label

    def preprocess(self, form):
        '''Preprocess a form.'''
        if self.preproc:
            return self.preproc(form)
        return form

    def postprocess(self, form):
        '''Postprocess a form.'''
        if self.postproc:
            return self.postproc(form)
        return form

    def postpostprocess(self, form):
        '''Postprocess a form that has already been postprocessed.'''
        if self.postpostproc:
            return self.postpostproc(form)
        return form

    def preprocess_file(self, filein, fileout):
        '''Preprocess forms in filein, writing them to fileout.'''
        fin = codecs.open(filein, 'r', 'utf-8')
        fout = codecs.open(fileout, 'w', 'utf-8')
        for line in fin:
            fout.write(str(self.preproc(line), 'utf-8'))
        fin.close()
        fout.close()

    def set_morphology(self, morphology, verbosity=0):
        '''Assign the Morphology object for this Language.'''
        self.morphology = morphology
        morphology.language = self
        morphology.directory = os.path.join(FST_DIRECTORY, self.abbrev)
        morphology.seg_units = self.seg_units
        morphology.phon_fst = morphology.restore_fst('phon')

    def load_morpho(self, fsts=None, simplified=False, ortho=True, phon=False,
                    segment=False, recreate=False, verbose=False):
        """Load words and FSTs for morphological analysis and generation."""
        fsts = fsts or self.morphology.pos
        opt_string = ''
        if segment:
            opt_string = 'segmentation'
        elif phon:
            opt_string = 'phonetic'
        if not self.has_cas(generate=phon, simplified=simplified, guess=False,
                            phon=phon, segment=segment):
            print('No {} FST available for {}!'.format(opt_string, self))
            return False
        msg_string = self.msgs.get('loading', 'Loading morphological data for') + ' {0}{1} ...'
        if opt_string: opt_string = ' (' + opt_string + ')'
#        else:
#            opt_string = ' (unsegmented, orthographic)'
        print(msg_string.format(self, opt_string))
        if ortho:
            # Load unanalyzed words
            self.morphology.set_words(simplify=simplified, ortho=True)
            # Load pre-analyzed words
            self.morphology.set_analyzed(ortho=True)
        if phon:
            # Load unanalyzed words
            self.morphology.set_words(simplify=simplified, ortho=False)
            # Load pre-analyzed words
            self.morphology.set_analyzed(ortho=False)
        for pos in fsts:
            # Load pre-analyzed words if any
            if ortho:
                self.morphology[pos].set_analyzed(ortho=True)
            if phon:
                self.morphology[pos].set_analyzed(ortho=False)
            # Load lexical anal and gen FSTs (no gen if segmenting)
            if ortho:
                self.morphology[pos].load_fst(gen=not segment, simplified=simplified,
                                              phon=False, segment=segment,
                                              recreate=recreate, verbose=verbose)
            if phon:
                self.morphology[pos].load_fst(gen=True, simplified=simplified,
                                              phon=True, segment=segment,
                                              recreate=recreate, verbose=verbose)
            # Load guesser anal and gen FSTs
            if not segment:
                if ortho:
                    self.morphology[pos].load_fst(gen=True, guess=True, phon=False, segment=segment,
                                                  recreate=recreate, verbose=verbose)
                if phon:
                    self.morphology[pos].load_fst(gen=True, guess=True, phon=True, segment=segment,
                                                  recreate=recreate, verbose=verbose)
        return True

    def get_fsts(self, generate=False, phon=False, segment=False):
        '''Return all analysis FSTs (for different POSs) satisfying phon and segment contraints.'''
        fsts = []
        for pos in self.morphology.pos:
            if phon:
                fst = self.morphology[pos].get_fst(generate=True, phon=True)
            else:
                fst = self.morphology[pos].get_fst(generate=generate, segment=segment)
            if fst:
                fsts.append(fst)
        return fsts

    def has_cas(self, generate=False, simplified=False, guess=False,
                phon=False, segment=False):
        """Is there at least one cascde file for the given FST features?"""
        for pos in self.morphology.pos:
            if self.morphology[pos].has_cas(generate=generate, simplified=simplified,
                                            guess=guess, phon=phon, segment=segment):
                return True
        return False

    ### Analyze words or sentences

    def anal_file(self, pathin, pathout=None, preproc=True, postproc=True, pos=None,
                  root=True, citation=True, segment=False, gram=True,
                  knowndict=None, guessdict=None,
                  phon=False, only_guess=False, guess=True,
                  nlines=0, start=0):
        """Analyze words in file, either writing results to pathout, storing in
        knowndict or guessdict, or printing out.
        """
        preproc = preproc and self.preproc
        postproc = postproc and self.postproc
        citation = citation and self.citation_separate
        storedict = True if knowndict != None else False
        try:
            filein = codecs.open(pathin, 'r', 'utf-8')
            # If there's no output file and no outdict, write analyses to terminal
            out = sys.stdout
            if segment:
                print(self.msgs.get('segmenting', 'Segmenting words in'), pathin)
            else:
                print(self.msgs.get('analyzing', 'Analyzing words in'), pathin)
            if pathout:
                # Where the analyses are to be written
                fileout = codecs.open(pathout, 'w', 'utf-8')
                print(self.msgs.get('writing', 'Writing to'), pathout)
                out = fileout
            fsts = pos or self.morphology.pos
            n = 0
            # Save words already analyzed to avoid repetition
            saved = {}
            # If nlines is not 0, keep track of lines read
            lines = filein.readlines()
            if start or nlines:
                lines = lines[start:start+nlines]
            for line in lines:
                # Separate punctuation from words
                line = self.morphology.sep_punc(line)
                # Segment into words
                for word in line.split():
                    if word in saved:
                        # Don't bother to analyze saved words
                        analysis = saved[word]
                    else:
                        # If there's no point in analyzing the word (because it contains
                        # the wrong kind of characters or whatever), don't bother.
                        # (But only do this if preprocessing.)
                        analysis = preproc and self.morphology.trivial_anal(word)
                        if analysis:
                            analysis = self.msgs.get('Word', 'Word') + ': ' + analysis + '\n'
                        else:
                            # Attempt to analyze the word
                            form = word
                            if preproc:
                                form = self.preproc(form)
                            analyses = self.anal_word(form, fsts=fsts, guess=guess, simplified=False,
                                                      phon=phon, only_guess=only_guess,
                                                      segment=segment,
                                                      root=root, stem=True, citation=citation, gram=gram, 
                                                      preproc=False, postproc=postproc, only_anal=storedict)
                            # If we're storing the analyses in a dict, don't convert them to a string
                            if storedict:
                                analysis = analyses
                            # Otherwise (for file or terminal), convert to a string
                            else:
                                if analyses:
                                    # Convert the analyses to a string
                                    analysis = self.analyses2string(word, analyses,
                                                                    form_only=segment and not gram)
                                else:
                                    analysis = '?' + self.msgs.get('Word', 'Word') + ': ' + word + '\n'
                        # Store the analyses (or lack thereof)
                        saved[word] = analysis
                    # Either store the analyses in the dict or write them to the terminal or the file
                    if storedict:
                        if analysis:
                            add_anals_to_dict(self, analysis, knowndict, guessdict)
                    else:
                        print(analysis, file=out)
            filein.close()
            if pathout:
                fileout.close()
        except IOError:
            print('No such file or path; try another one.')

    def analyses2string(self, word, analyses, form_only=False):
        '''Convert a list of analyses to a string.'''
        if form_only:
            return word + ': ' + ', '.join(analyses) + '\n'
        s = ''
        if not analyses:
            s += '?'
        s += self.msgs.get('Word', 'Word') + ': ' + word + '\n'
        for analysis in analyses:
            pos = analysis[0]
            if pos:
                pos = pos.replace('?', '')
                if pos in self.morphology:
                    s += self.morphology[pos].anal2string(analysis)
                elif self.morphology.anal2string:
                    s += self.morphology.anal2string(analysis)
        return s

    def analysis2dict(self, analysis, record_none=False, ignore=[]):
        """Convert an analysis (a FeatStruct) to a dict."""
        dct = {}
        for k, v in analysis.items():
            if isinstance(v, FeatStruct):
                v_dict = self.analysis2dict(v, record_none=record_none, ignore=ignore)
                if v_dict:
                    # Could be {}
                    dct[k] = v_dict
            elif not v:
                # v is None, False, '', or 0
                if record_none:
                    dct[k] = None
            elif k not in ignore:
                dct[k] = v
        return dct

    def anal_word(self, word, fsts=None, guess=True, only_guess=False, simplified=False,
                  phon=False, segment=False,
                  root=True, stem=True, citation=True, gram=True,
                  to_dict=False, preproc=False, postproc=False, string=False,
                  only_anal=False):
        '''Analyze a single word, trying all existing POSs, both lexical and guesser FSTs.

        [ [POS, {root|citation}, FSSet] ... ]
        '''
        preproc = preproc and self.preproc
        postproc = postproc and self.postproc
        citation = citation and self.citation_separate
        analyses = []
        fsts = fsts or self.morphology.pos
        if preproc:
            # Convert to roman
            form = self.preproc(word)
        else:
            form = word
        # See if the word is unanalyzable ...
        unal_word = self.morphology.is_word(form, simple=simplified)
        if unal_word:
            if only_anal:
                return []
            analyses.append(self.simp_anal([unal_word], postproc=postproc, segment=segment))
        # ... or is already analyzed
        elif form in self.morphology.analyzed:
            if only_anal:
                return []
            analyses.extend(self.proc_anal_noroot(form, self.morphology.get_analyzed(form)))
        if not analyses:
            if not only_guess:
                for pos in fsts:
                    #... or already analyzed within a particular POS
                    preanal = self.morphology[pos].get_analyzed(form, simple=simplified)
                    if preanal:
                        analyses.extend(self.proc_anal(form, [preanal], pos,
                                                       show_root=root, citation=citation, stem=stem,
                                                       segment=segment,
                                                       simplified=False, guess=False,
                                                       postproc=postproc, gram=gram))
            if not analyses:
                if not only_guess:
                    # We have to really analyze it; first try lexical FSTs for each POS
                    for pos in fsts:
                        analysis = self.morphology[pos].anal(form, simplified=simplified,
                                                             phon=phon, segment=segment,
                                                             to_dict=to_dict)
                        if analysis:
                            # Keep trying if an analysis is found
                            analyses.extend(self.proc_anal(form, analysis, pos,
                                                           show_root=root, citation=citation and not segment,
                                                           segment=segment,
                                                           stem=stem, simplified=simplified,
                                                           guess=False, postproc=postproc, gram=gram))
                # If nothing has been found, try guesser FSTs for each POS
                if not analyses and guess:
                    # Accumulate results from all guessers
                    for pos in fsts:
                        analysis = self.morphology[pos].anal(form, guess=True,
                                                             phon=phon, segment=segment,
                                                             to_dict=to_dict)
                        if analysis:
                            analyses.extend(self.proc_anal(form, analysis, pos,
                                                           show_root=root,
                                                           citation=citation and not segment,
                                                           segment=segment,
                                                           simplified=False, guess=True, gram=gram,
                                                           postproc=postproc))
        if string:
            # Print out stringified version
            print(self.analyses2string(word, analyses, form_only=segment and not gram))
        return analyses

    def simp_anal(self, analysis, postproc=False, segment=False):
        '''Process analysis for unanalyzed cases.'''
        if postproc:
            # Convert the word to Geez.
            analysis[0] = self.postproc(analysis[0])
        if segment:
            return analysis[0]
        return [None, analysis[0]]

    def proc_anal_noroot(self, form, analyses):
        '''Process analyses with no roots/stems.'''
        return [(analysis.get('pos'), None, None, analysis, None) for analysis in analyses]

    def proc_anal(self, form, analyses, pos, show_root=True, citation=True,
                  segment=False, stem=True, simplified=False, guess=False,
                  postproc=False, gram=True, string=False):
        '''Process analyses according to various options, returning a list of analysis tuples.'''
        cat = '?' + pos if guess else pos
        results = set()
        if segment and not gram:
            return [analysis[0] for analysis in analyses]
        for analysis in analyses:
            root = analysis[0]
            grammar = analysis[1]
            if not show_root and not segment:
                analysis[0] = None
            if postproc and self.morphology[pos].postproc:
                self.morphology[pos].postproc(analysis)
            proc_root = analysis[0]
            for g in grammar:
                if citation and self.morphology[pos].citation:
                    cite = self.morphology[pos].citation(root, g, simplified, guess, stem)
                    if postproc:
                        cite = self.postprocess(cite)
                else:
                    cite = None
                    # Prevent analyses with same citation form and FS
                    # Include the grammatical at the end in case it's needed
                results.add((cat, proc_root, cite, g if gram else None, g))
        return list(results)

    def ortho2phon(self, word, gram=False, raw=False, return_string=False,
                   gram_pre='-- ', postpostproc=False):
        '''Convert a form in non-roman to roman, making explicit features that are missing in orthography.
        @param word:     word to be analyzed
        @type  word:     string or unicode
        @param gram:     whether a grammatical analysis is to be included
        @type  gram:     boolean
        @param return_string: whether to return string analyses (needed for phon_file)
        @type  return_string: boolean
        @param gram_pre: prefix to put before form when grammatical analyses are included
        @type  gram_pre: string
        @param postpostproc: whether to call postpostprocess on output form
        @type  postpostproc: boolean
        @return:         a list of analyses
        @rtype:          list of (root, feature structure) pairs
        '''
        preproc = self.preprocess(word)
        results = {}
        # Is the word in the word or analyzed lists?
        analyzed = self.morphology.ortho2phon(preproc)
        if analyzed:
            # Just add each form with no analysis to the dict
            if postpostproc:
                analyzed = [self.postpostprocess(a) for a in analyzed]
            results = dict([(a, '') for a in analyzed])
        else:
            # Try to analyze it with FSTs
            for posmorph in self.morphology.values():
                output = posmorph.ortho2phon(preproc)
                if output:
                    # Analyses found for posmorph; add each to the dict
                    for form, anal in output.items():
                        if gram:
                            if not raw:
                                anal = [posmorph.anal2string(a) for a in anal]
                            else:
                                anal = [(a[1], a[3]) for a in anal]
                        if postpostproc:
                            form = self.postpostprocess(form)
                        results[form] = results.get(form, []) + anal
            if not results:
                # No analysis
                # First phoneticize the form and mark as unknown ('?')
                form = self.morphology.phonetic(preproc) + '?'
                if postpostproc:
                    form = self.postpostprocess(form)
                # Then add it to the dict
                results = {form: ''}
        # Now do something with the results
        if gram:
            # Include grammatical analyses
            if not raw:
                if return_string:
                    # Return the results as a string
                    return list(results.items())
                # Print out the results
                for form, anals in results.items():
                    print(gram_pre + form)
                    for anal in anals:
                        print(anal, end='')
            else:
                # Return the raw results
                return results
        elif raw or return_string:
            # Return only the forms
            return list(results.keys())
        else:
            # Print out only the forms
            for anal in results.keys():
                print(anal, end=' ')
            print()

    def ortho2phon_file(self, infile, outfile=None, gram=False,
                        word_sep='\n', anal_sep=' ', print_ortho=True,
                        postpostproc=False,
                        start=0, nlines=0):
        '''Convert non-roman forms in file to roman, making explicit features that are missing in the orthography.
        @param infile:   path to a file to read the words from
        @type  infile:   string
        @param outfile:  path to a file where analyses are to be written
        @type  outfile:  string
        @param gram:     whether a grammatical analysis is to be included
        @type  gram:     boolean
        @param word_sep:  word separator (only when gram=False)
        @type  word_sep:  string
        @param anal_sep:  analysis separator (only when gram=False)
        @type  anal_sep:  string
        @param print_ortho: whether to print the orthographic form first
        @type  print_ortho: boolean
        @param postpostproc: whether to call postpostprocess on output form
        @type  postpostproc: boolean
        @param start:    line to start analyzing from
        @type  start:    int
        @param nlines:   number of lines to analyze (if not 0)
        @type  nlines:   int
        '''
        try:
            filein = codecs.open(infile, 'r', 'utf-8')
            # Whether to write analyses to terminal
            out = sys.stdout
            # Dictionary to store analyzed words in
            saved_dct = {}
            print('Analyzing words in', infile)
            if outfile:
                # Where the analyses are to be written
                out = codecs.open(outfile, 'w', 'utf-8')
                print('Writing analysis to', outfile)
            lines = filein.readlines()
            if start or nlines:
                lines = lines[start:start+nlines]
            begun = False
            for line in lines:
                # Separate punctuation from words
                line = self.morphology.sep_punc(line)
                # Segment into words
                for word in line.split():
                    if word in saved_dct:
                        # Don't bother to analyze saved words
                        analysis = saved_dct[word]
                    else:
                        # Analyze the word
                        analysis = self.ortho2phon(word, gram=gram,
                                                   postpostproc=postpostproc,
                                                   raw=False, return_string=True)
                        saved_dct[word] = analysis
                    # Write the analysis to file or stdout
                    if gram:
                        print("{0}".format(word), file=out)
                        for anal in analysis:
                            print("-- {0}".format(anal[0]), file=out)
                            for a in anal[1]:
                                print("{0}".format(a), end='', file=out)
                        print(file=out)
                    else:
                        # Start with the word_sep string
                        if begun:
                            print(file=out, end=word_sep)
                        if print_ortho:
                            # Print the orthographic form
                            print("{0} ".format(word), end='', file=out)
                        for anal in analysis[:-1]:
                            # Print an analysis followed by the analysis separator
                            print("{0}".format(anal), end=anal_sep, file=out)
                        # Print the last analysis with no analysis separator
                        if analysis:
                            print("{0}".format(analysis[-1]), end='', file=out)
                    begun=True
            if not gram:
                # Final newline
                print(file=out)
            filein.close()
            if outfile:
                out.close()
        except IOError:
            print('No such file or path; try another one.')

##class Multiling(dict):
##
##    def __init__(self, *lang_pos):
##        """Constructor takes one or more pairs: (language, pos)."""
##        dict.__init__(self, [(lang.abbrev, lang.morphology[pos]) for lang, pos in lang_pos])
##
##    def trans_word(self, form, source, dest, trace=False):
##        pass
##
##    def graphics(self):
##        start_graphics(self.values())
##
##    def load_fst(self):
##        for pos in self.values():
##            pos.load_fst()
##
##    def set_transfer_fs(self, fss):
##        '''Set the transfer FSs.'''
##        self.transfer_fss = fss
##
##    def transfer1(self, source, source_fs, target):
##        source_trans = FeatStruct()
##        source_trans[source] = source_fs
##        target_morphpos = self[target]
##        for fs in self.transfer_fss:
##            unify_fs = unify(source_trans, fs)
##            if unify_fs:
##                target_morphpos.assign_defaults(unify_fs[target])
##                return unify_fs
##
##    def transfer(self, source_lang, source_fss, target_lang):
##        """Root, FS pairs for generating target word(s)."""
##        target = []
##        for fs_set in source_fss:
##            for fs in fs_set:
##                target_fs = self.transfer1(source_lang, fs, target_lang)
##                if target_fs:
##                    # The source FS unifies with some transfer FS
##                    if target_lang in target_fs:
##                        target_glosses = target_fs[target_lang]['g'], split[',']
##                        for gloss in target_gloses:
##                            target.append((gloss, target_fs))
##        return target
                    
