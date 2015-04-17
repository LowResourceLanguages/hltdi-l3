#!/usr/bin/env python3

#   Implementation of Extensible Dependency Grammar, as described in
#   Debusmann, R. (2007). Extensible Dependency Grammar: A modular
#   grammar formalism based on multigraph description. PhD Dissertation:
#   Universität des Saarlandes.
#
#   Extended to accommodate multiple languages (with Semantics treated as
#   a language), insertion of nodes not found in input, and weighted
#   constraints and variables.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2011, 2012, 2013, 2014
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

__version__ = 2.0
import l3xdg
# Profiling
import cProfile
import pstats
# Test constraint satisfaction
from l3xdg.tests.testcs import *
# Test constraints and projectors
# from l3xdg.tests.testconstraints import *

###
### This file brings together a bunch of handy routines for testing
### the program. They should probably be in l3xdg/__init__.py or
### l3xdg/xdg.py
###

##########################################################################
###########
### xdg  ##
###########
### To create XDGs for sentences in l3xdg/tests/testcs.py (ENGLISH, etc.)
### or other sentences the grammars can handle.
### xdg() returns either the XDG objects for each sentence or
### a list of solutions for each sentence.
###
### Examples:
###
### >>> E = xdg(ENGLISH[0], solve=False)
### >>> E[0].solve()
### ...
###
### >>> Q = xdg(QUECHUA, 'qu')
### >>> for q in Q:
###        for sol in q:
###           sol.display()
### ...
###
### >>> EA = xdg(ENGLISH, 'en', 'am')
### >>> for e in EA:
###        for sol in e:
###           sol.display()
###
##########################################################################
################
###   parse   ##
################
### Analyzes a sentence in a language, by default including semantics.
### If solve is True, displays the parses and returns the solutions as Multigraphs.
### If solve is False, returns an XDG instance (which can be solved with
### the solve() method).
###
### Example:
###
### >>> parse(AMHARIC[4], 'am')
### ====================  SOLUTION <MG b: እኔ ቤቱን ጠረግኩት ።>  ====================
### Input (Amharic): እኔ ቤቱን ጠረግኩት ።
### Semantics: I HOUSE CLEAN ROOT *ZERO_THING *ZERO_THING
### ...
### ====================  SOLUTION <MG a: እኔ ቤቱን ጠረግኩት ።>  ====================
### Input (Amharic): እኔ ቤቱን ጠረግኩት ።
### Semantics: I HOUSE CLEAN ROOT *ZERO_THING *ZERO_THING
### ...
### [<MG b: እኔ ቤቱን ጠረግኩት ።>, <MG a: እኔ ቤቱን ጠረግኩት ።>]
###
##########################################################################
################
###   trans   ##
################
### Translates a sentence from a source to a target language, by default
### using Semantics as an intermediate language.
### If solve is True, displays the translation and returns the solutions as Multigraphs.
### If solve is False, returns an XDG instance (which can be solved with
### the solve() method).
###
### Example:
### 
### >>> trans(AMHARIC[1], 'am', 'en')
### =========================  SOLUTION <MG : ሞተች ።>  =========================
### Input (Amharic): ሞተች ።
### Semantics: DIE ROOT SHE
### Output (English): she died .
### ...
### [<MG : ሞተች ።>]
###
##########################################################################
################
###    gen    ##
################
### Generates a sentence in a language, starting from semantic input in the form
### of a string of semantics "words" and optionally particular intial arcs and
### feature values.
### If solve is True, displays the output and returns the solutions as Multigraphs.
### If solve is False, returns and XDG instance (which can be solved with
### the solve() method).
###
### Example:
###
### >>> gen("I SEE SHE", 'en', arcs={'arg2': (1, 2)}, agrs={'reltime': [1, (0,)]})
### =================  SOLUTION <MG aa: I SEE SHE STATEMENT>  =================
### Output (English): I see her .
### ______________________________ DIMENSION sem ______________________________
### I          SEE        SHE        STATEMENT  
###            ROOT                             
### <---arg1---
###            ---arg2--->
### _____________________________ DIMENSION en-lp _____________________________
### I          SEE        SHE        STATEMENT  
###            ROOT                             
###            ---mf2---->
### <----vf----
### _____________________________ DIMENSION en-id _____________________________
### I          SEE        SHE        STATEMENT  
###            ROOT                             
### <----sb----
###            ----ob---->
###
### Alternately, the input can take the form of a dict including the "words",
### arcs, and agrs.
###
### Example:
###
### >>> gen({'root': ['SEE', {'arg1': 'PETER',
###                           'arg2': ['WOMAN', {}, {'num': (1,)}]},
###	                     {'reltime': (0,)}]},
###         'gn')
###
##########################################################################
##########
### l3  ##
##########
### Does parse or trans depending on whether a target language is
### is given.
###
### >>> l3(AMHARIC[1], 'am')
###
### >>> l3(AMHARIC[1], 'am', 'en')
###
##########################################################################
##########################################################################
### The following functions call xdg for particular languages or language combinations.
### project=True causes projectors to be used for constraint satisfaction;
### with project=False, it's propagators. With solve=False (the default), the
### XDG object is returned. Its solve() method must then be called to initiate
### constraint satisfaction. To display the Multigraphs that result, call their
### display() method.

def gn(s='omano',
       project=False, solve=False, dims=None, semantics=True,
       all_sols=False,
       reload=False, timeit=False, flatten=True, pickle=True,
       verbosity=0):
    return xdg(s, 'gn',
               dims=dims, semantics=semantics, all_sols=all_sols,
               reload=reload, flatten=flatten, pickle=pickle,
               project=project, solve=solve, timeit=timeit, verbosity=verbosity)[0]

def en(s='the woman cleaned the house in the city',
       project=False, solve=False, dims=None, reload=False,
       semantics=True,
       flatten=True, pickle=True, timeit=False):
    return xdg(s, 'en',
               semantics=semantics,
               project=project,
               dims=dims, reload=reload, flatten=flatten, pickle=pickle,
               solve=solve, timeit=timeit)[0]

def am(s=AMHARIC[6],
       project=False, solve=False, dims=None, reload=False,
       semantics=True,
       flatten=True, pickle=True, timeit=False):
    return xdg(s, 'am',
               dims=dims, semantics=semantics,
               project=project,
               reload=reload,
               solve=solve, flatten=flatten, pickle=pickle,
               timeit=timeit)[0]

def es(s='la mujer vio la casa en la ciudad',
       project=False, solve=False, dims=None, semantics=True,
       reload=False, timeit=False, flatten=True, pickle=True):
    return xdg(s, 'es',
               dims=dims, semantics=semantics,
               reload=reload, flatten=flatten, pickle=pickle,
               project=project, solve=solve, timeit=timeit)[0]

def enam(s='the woman saw the hill', target='am', project=False,
         reload=False,
         transfer=False, solve=False,
         pickle=True, flatten=True, timeit=False, dims=None):
    return xdg(s, 'en', target,
               transfer=transfer,
               semantics= not transfer,
               reload=reload,
               timeit=timeit, pickle=pickle, flatten=flatten,
               project=project, solve=solve)[0]

def amen(s='ሴቷ ኮረብታውን አየችው', target='en', project=False,
         reload=False,
         transfer=False, solve=False,
         pickle=True, flatten=True, timeit=False, dims=None):
    return xdg(s, 'am', target,
               transfer=transfer,
               semantics= not transfer,
               reload=reload,
               timeit=timeit, pickle=pickle, flatten=flatten,
               project=project, solve=solve)[0]

def esgn(s='la mujer que se muere habla', solve=False,
         all_sols=True,
         transfer=False,
         project=False,
         timeit=False, pickle=True, flatten=True,
         verbosity=0,
         dims=None):
    return xdg(s, 'es', 'gn',
               transfer=transfer,
               semantics= not transfer,
               all_sols=all_sols,
               timeit=timeit, pickle=pickle, flatten=flatten,
               verbosity=verbosity,
               project=project, solve=solve)[0]

def gnes(s='Peru omano', solve=False,
         all_sols=True,
         transfer=False,
         project=False,
         timeit=False, pickle=True, flatten=True,
         dims=None):
    return xdg(s, 'gn', 'es',
               transfer=transfer,
               semantics= not transfer,
               all_sols=all_sols,
               timeit=timeit, pickle=pickle, flatten=flatten,
               project=project, solve=solve)[0]

### xdg: Create XDG instance, returning it without solving by default.

def xdg(sentences, source='en', target=[],
        solve=True, create_princs=True, process=PARSE,
        distributor=None, arcs=None, agrs=None,
        semantics=True, transfer=False, weaken=None, project=False,
        dims=None, princs=None, grammar='tiny',
        reload=False, flatten=True, all_sols=True, pickle=True,
        verbosity=0, timeit=False):
    '''
    reload: whether to recreate the lexicon for the languages
    '''
    if not isinstance(sentences, list):
        sentences = [sentences]
    if target and not isinstance(target, list):
        target = [target]
    xdgs = [l3xdg.XDG(sentence, source, target=target,
                      load_semantics=semantics, reload=reload,
                      process=process,
                      pre_arcs=arcs, pre_agrs=agrs,
                      flatten_lexicon=flatten,
                      transfer_xlex=transfer,
                      weaken=weaken, dims=dims, princs=princs,
                      grammar=grammar, create_princs=create_princs,
                      project=project, pickle=pickle,
                      distributor=distributor, 
                      verbosity=verbosity) \
                      for sentence in sentences]
    if solve and create_princs:
        return [x.solve(all_sols=all_sols, timeit=timeit, verbose=verbosity) for x in xdgs]
    else:
        return xdgs

def l3(sentence, source, target='', dims=None, grammar='tiny',
       semantics=True, solve=True, timeit=False, verbosity=0):
    '''Either parse or translate the sentence.'''
    if target:
        return trans(sentence, source, target, semantics=semantics,
                        dims=dims, grammar=grammar,
                        solve=solve, verbosity=verbosity, timeit=timeit)
    else:
        return parse(sentence, source, semantics=semantics, solve=solve,
                        dims=dims, grammar=grammar,
                        verbosity=verbosity, timeit=timeit)

def parse(sentence, language, dims=None, grammar='tiny',
          all_sols=True, project=False,
          semantics=True, solve=False, timeit=False, verbosity=0):
    '''Parse a single sentence, returning the solutions as Multigraphs.'''
    x = \
        xdg(sentence, source=language, solve=solve, dims=dims,
            grammar=grammar, timeit=timeit, all_sols=all_sols,
            project=project,
            semantics=semantics, verbosity=verbosity)[0]
    if not solve:
        return x
    # Display the solutions
    Multigraph.d(x)
    return x

def gen(sentence, target,
        arcs=None, agrs=None,
        all_sols=True, solve=False,
        grammar='tiny',  project=False,
        timeit=False, verbosity=0):
    """Generate a sentence, given
    either
    a semantic string and possibly arcs and grammatical features (agrs)
    or
    a dict representation of the semantics, including arcs and agrs.
    """
    if isinstance(sentence, dict):
        # Convert to sentence, arcs, agrs
        sentence, arcs, agrs, pos = XDG.sem_dict2string(sentence)
    if arcs and not 'sem' in arcs:
        # Add dimension to arc dict.
        arcs = {'sem': arcs}
    if agrs and not 'sem' in agrs:
        # Add dimension to agr dict.
        agrs = {'sem': agrs}
    x = \
      xdg([sentence], source='sem', target=target,
          solve=solve, semantics=False, all_sols=all_sols,
          arcs=arcs, agrs=agrs, project=project,
          process=GENERATE,
          verbosity=verbosity)[0]
    if not solve:
        return x
    # Display the solutions
    Multigraph.d(x)
    return x

def trans(sentence, source, target, dims=None, grammar='tiny',
          semantics=True, transfer=False, all_sols=True, project=False,
          solve=True, timeit=False, verbosity=0):
    '''Translate a single sentence, returning the solutions as Multigraphs.'''
    x = \
        xdg(sentence, source, target, dims=dims,
            grammar=grammar, project=project,
            semantics=semantics, transfer=transfer, all_sols=all_sols,
            solve=solve, timeit=timeit,
            verbosity=verbosity)[0]
    if not solve:
        return x
    # Display the solutions
    Multigraph.d(x)
    return x

### Chunk analysis and translation

def chunk(s, language='es',
          project=False, solve=False, dims=None,
          all_sols=False,
          reload=False, timeit=False, flatten=True, pickle=True):
    return xdg(s, source=language,
               grammar='chunk', dims=dims, semantics=False,
               all_sols=all_sols, solve=solve, project=project,
               reload=reload, flatten=flatten, pickle=pickle,
               timeit=timeit)[0]

def trunk(s, source='es', target='gn',
          all_sols=True, solve=False,
          timeit=False, project=False):
    return xdg(s, source, target,
               transfer=True, semantics=False, grammar='chunk',
               all_sols=all_sols, solve=solve, 
               project=project, timeit=timeit)[0]

##########################################################################
##########################################################################
### To load a set of languages that will participate in parsing,
### generation, or translation. Lexicons are loaded for each language,
### and by default, they are flattened, linked, and pickled. Finally,
### morphology is loaded for each language that has it. The languages
### are returned as a list.
###
### Example:
###
### >>> load_langs(['es', 'sem', 'gn'])
### ...
### [español, Semantics, guaraní]
###

def load_langs(langs, grammar='tiny', force=True,
               flatten=True, pickle=True, learn=False):
    return l3xdg.Language.load_langs(langs, grammar=grammar,
                                     force=force,
                                     flatten=flatten,
                                     learn=learn,
                                     pickle=pickle)

##########################################################################
##########################################################################
### To load only the morphological analyzers and generators for a language.
### You can then call the language methods for analysis and generation:
### analyze(), analyze_file(), generate()
###
### Example:
###
### >>> g = morpho('gn')
### >>> g.analyze("noñe'ẽiva'ekue")
### [["ñe'ẽ", 'va', "[asp=[-asev,-dubit,-prim,-reit],caso=None,cat='a',-inter,mod='ind',+neg,+neg1,-nte1,-nte2,oj=[-1,-2,-r],pos='v',-rel,-rztrans,sj=[-1,-2],subcat=0,tasp=[-ant,-cont,-inmit,+plus,-rem],tmp='pret',-trans,voz='smp']"], ["ñe'ẽ", 'va', "[asp=[-asev,-dubit,-prim,-reit],caso=None,cat='a',-inter,mod='ind',+neg,+neg1,-nte1,-nte2,oj=[-1,-2,-r],pos='v',+rel,-rztrans,sj=[-1,-2],subcat=0,tasp=[-ant,-cont,-inmit,-rem],tmp='pret',-trans,voz='smp']"]]

def morpho(lang_abbrev):
    """Load morphology for language with abbreviation lang_abbrev.
    No lexicon/grammar is loaded. Note: this assumes the language has a 'chunk'
    grammar."""
    return l3xdg.Language.load(lang_abbrev, force=True,
                               morpho_only=True, grammar='chunk')

def main():
    print('L^3 XDG, version {}\n'.format(__version__))
    print("GENERAL PARSING, GENERATION, AND TRANSLATION")
    print('To load and link a set of languages, do')
    print('>>> load_langs(list_of_abbrevs, grammar)')
    print('For example,')
    print(">>> grn, sem, esp = load_langs(['gn', 'sem', 'es'], 'tiny')")
    print("(The 'grammar' option defaults to 'tiny'.)")
    print("Of course the grammars must exist and be debugged.")
    print("If a set of languages is already loaded and linked, or if the languages are")
    print("pickled in linked form, you can go ahead and do one of the following:")
    print(">>> parse(sentence, language)")
    print(">>> gen(sentence, language)")
    print(">>> trans(sentence, source, target)")
    print()
    print("CHUNKING")
    print("To load and link chunk grammars, do")
    print(">>> load_langs([source, target], 'chunk')")
    print("To use a chunk grammar to parse, do")
    print(">>> chunk(sentence, language)")
    print("To do transfer translation (no semantics) with a chunk grammar, do")
    print(">>> trunk(sentence, source, target)")
    print()
    print("MORPHOLOGY")
    print("Morphological analyzers and generators are normally loaded along with")
    print("grammar/lexicons. To load only the morphology for a language, do")
    print(">>> morpho(language)")
    print("You can then use the language methods analyze() and analyze_file(). For example,")
    print(">>> g = morpho('gn')")
    print(">>> g.analyze(\"noñe'ẽiva'ekue\")")
#    print("[[\"ñe'ẽ\", 'va', \"[asp=[-asev,-dubit,-prim,-reit],...]]")
#    print(">>> g.analyze_file('l3xdg/languages/gn/data/escurra.txt',")
#    print("                   'l3xdg/languages/gn/data/escurra_out.txt',")
#    print("                   pos=False, gram=False, nlines=100)")
    print()
    print("For details, including options for all the functions, see main.py.")
    print()

if __name__ == "__main__": main()

### Load, link, and pickle Es, Gn, and Sem tiny grammars.
def load(e=True, g=True, s=True):
    l = []
    if g:
        l.append('gn')
    if s:
        l.append('sem')
    if e:
        l.append('es')
    return load_langs(l)

### Test generation from semantics.
def g1(all_sols=True):
    return gen('WOMAN REL DIE SPEAK', 'es',
               arcs={'sem': {'coref': (0, 1), 'arg1': (3, 0)}},
               agrs={'sem': {'reltime': [(2, (0,)), (3, (0,))],
                             'num': [(0, (1,)), (1, (1,))],
                             'def': [(0, (1,)), (1, (1,))]}},
               all_sols=all_sols)

### Load, link, and pickle Es and Gn chunk grammars.
def lc(learn=True):
    return load_langs(['es', 'gn'], grammar='chunk', learn=learn)

### Profiling

def profile(call, file="prof.txt"):
    cProfile.run(call, file)
    p = pstats.Stats(file)
    p.sort_stats('time').print_stats(20)

### Corpus

def corp():
    return l3xdg.Corpus('c1', 'es', 'gn')

### Groups

##def test_group(es_lexicon):
##    Group.make('a tu casa', es_lexicon)

### Distribution

##def test_dist(sentences=SPANISH, source='es', target='qu', 
##              dist=0):
##    '''To test different distribution algorithms.'''
##    if dist == 0:
##        # select variables from front of list
##        distributor = Distributor(var_select=lambda x: x[0])
##    elif dist == -1:
##        # select variables from end of list
##        distributor = Distributor(var_select=lambda x: x[-1])
##    else:
##        # random variable selection
##        distributor = Distributor()
##    print('Testing sentences with distributor', distributor)
##    xdgs = [l3xdg.XDG(sentence, source, target=[target] if target else [], 
##                      grammar='tiny', 
##                      distributor=distributor, 
##                      verbosity=0) \
##                      for sentence in sentences]
##    res = []
##    for x in xdgs:
##        sols = x.solve(verbose=False)
##        res.append((x, len(sols)))
##    return res
