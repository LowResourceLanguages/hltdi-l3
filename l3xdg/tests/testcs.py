#!/usr/bin/env python3

#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2011 The HLTDI L^3 Team <gasser@cs.indiana.edu>
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

import unittest
from .. xdg import *

####
#### Test constraint satisfaction for parsing and translation.
####
#### Tiny grammars.
####

SEMANTICS = \
    [{'root': ['SEE', {'arg1': 'PETER',
                       'arg2': ['WOMAN', {}, {'num': (1,)}]},
               {'reltime': (0,)}]},
     {'root': ['WOMAN_PRED',
               {'arg1': 'ESTHER'},
               {'reltime': (0,), 'num': (1,), 'def': (1,)}]}
     ]

GUARANI = [## predicate nominals
           "Ester kuña",                 #0
           ## relative clauses
           "pe kuña omanóva oñe'ẽ",      #1
           "avati Peru oñotýva omano",   #2
           ## intransitive
           "Peru imandu'a kuña rehe",    #3
           "Peru hesarái kuñágui",       #4
           'Peru omano',                 #5
           "ha'ekuéra omano",            #6
           "añe'ẽ",                      #7
           "imandu'a",                   #8
           ## transitive
           'Peru ohecha hóga',           #9
           'Peru oñoty avati',
           'che añoty avati',
           'añoty avati',
           "rohecha ichupekuéra",
           "ha'e cherecha",
           "nderecha",
           "pohecha",
           'Peru oñoty',
           'Peru ohecha',
           'Peru ohecha kuñanguérame',
           'ñane retãme',
           "Peru imandu'a avati rehe"]

ENGLISH = ['Esther filtered the water',
           'I saw him',
           'she cleans the house',
           'the woman cleans the house',
           'she is cleaning the house',
           'I am cleaning a house',
           'Esther is dirty',
           'my teacher sees her house']

AMHARIC = [## intransitive
           # explicit sbj
           'አስቴር ሞተች',      # Esther died
           # null sbj
           'ሞተች',           # she died
           'ትሞታለች',        # she dies
           # def art suffix
           'ሴትዋ ሞተች',      # the woman died
           'ሴቶቹ ሞቱ',       # the women died
           # indef noun
           'ሴት ሞተች',       # a woman died
           # ADJ + COP
           'ውሃ ቆሻሻ ነው',     # the water is dirty
           'አስቴር ቆሻሻ ነች',   # Esther is dirty
           'ቆሻሻ ነኝ',        # I am dirty
           ## transitive
           # explicit sbj and obj
           'እኔ ቤቱን ጠረግኩት',       # I cleaned the house
           'አስቴር ውሃውን አጠለለችው',  # Esther filtered the water
           # Esther saw the hill
           'አስቴር ኮረብታውን አየችው',
           # null sbj, explicit obj
           'ሴቶቹን አየኋቸው',     # I saw the women
           'ቤቱን ጠረግኩት',      # I cleaned the house
           # explicit sbj, null obj
           'እኔ ጠረግኩት',       # I cleaned it
           'እሷ ጠረገችው',      # she cleaned it
           # the women cleaned the house
           'ሴቶቹ ቤቱን ጠረጉት',
           # null sbj, null obj
           'ጠረግኩት',         # I cleaned it
           'አየኋት',           # I saw her
           ## impersonal verbs
           'ደከማት',          # she is tired
           ## relative clauses
           'የታመመችው ሴት ሞተች',    # sb rel; IV rel; 'the woman who was sick died'
           'የሞተችውን ሴት አየኋት',     # ob rel; IV rel; 'I saw the woman who died'
           'የተከራያችሁት ቤት ፈረሰ',    # sb rel; TV rel; 'the house you rented collapsed'
           'የተከራያችሁትን ቤት ጠረጉት', # ob rel; TV rel; 'they cleaned the house you rented'
           # same without N "heads"
           'የታመመችው ሞተች',
           'የሞተችውን አየኋት',
           'የተከራያችሁት ፈረሰ',
           'የተከራያችሁትን ጠረጉት'
           ]

SPANISH = [# relative clauses
           'el muchacho que habla ve el maíz que planté',
           # predicate nominals
           'Ester es una mujer',
           'Pedro recuerda maíz',          # translation to Gn
           'ella se murió',
           'se murió',                     # null sbj
           'se muere',                     # null sbj; try ->qu w/ and w/o transfer
           'yo limpié la casa',
           'yo veo la casa',
           'la mujer ve la casa',
           'la mujer tiene gripe',
           'limpié la casa',               # null sbj
           'la limpié',                    # null sbj, pro obj
           'la mujer la limpia',           # pro obj
           'la mujer limpia la casa',      # 2 nouns (currently ambiguous)
           'está muriendo',                # aux, intrans verb
           'yo estoy limpiando la casa',   # aux, trans verb
           'la está limpiando',            # aux, trans verb, null sbj
           # groups
           'Pedro tiene miedo de la mujer'
           ]

QUECHUA = [# (the) woman (top) cleaned (the) house
           'warmiqa wasita picharqa',
           # (the) woman has the flu
           'warmiqa chhulliwanmi kashan',
           # (the) woman died in the house
           'warmiqa wasipi wañurqa',
           # (the) women (top) cleaned (the) houses
           'warmikunaqa wasikunata picharqanku',
           # she/he cleaned (the) house; null sbj
           'wasita picharqa',
           # she/he died
           'pay wañurqa',
           # I cleaned it/them; explicit sbj, null obj
           'nuqaqa picharqani',
           # I cleaned it/them; null sbj, null obj
           'picharqani']

class XDGTestCase(unittest.TestCase):
    '''Superclass for test cases.'''

    def indexed_xdg(self, sentences, source='en', target=[], index=0, semantics=True):
        return xdg(sentences[index], source=source, target=target,
                   semantics=semantics)

    def xdg(self, sentence, source='en', target=[], semantics=True):
        '''Return an XDG object for a source language, (possibly)
        target languages, and sentence, with principles instantiated.'''
        return XDG(sentence, source, 
                   target=target, 
                   load_semantics=semantics,
                   verbosity=0,
                   grammar='tiny')

    def solve(self, x, verbose_cs=False, verbose_out=0):
        '''Find, print, and return the solutions for an XDG object.'''
        solutions = x.solve(verbose=verbose_cs)
        if verbose_out:
            print('SOLUTIONS:')
            for s in solutions:
                if verbose_out > 1:
                    s.pprint()
                else:
                    s.io()
        return solutions

class ParseTestCase(XDGTestCase):
    '''Tests for parsing with particular languages.'''

    def parse_test(self, language, sentences):
        '''Test whether there is at least one solution for each sentence.'''
        problems = [self.xdg(s, language) for s in sentences]
        solutions = [self.solve(p) for p in problems]
        for p, s in zip(problems, solutions):
            n_sols = len(s)
            self.assertNotEqual(n_sols, 0,
                               '{} has no solutions'.format(p))
            self.assertLess(n_sols, 8,
                            '{} has more than 8 solutions'.format(p))

    def english(self):
        self.parse_test('en', ENGLISH)

    def quechua(self):
        self.parse_test('qu', QUECHUA)

    def amharic(self):
        self.parse_test('am', AMHARIC)

    def spanish(self):
        self.parse_test('es', SPANISH)

class TranslateTestCase(XDGTestCase):
    '''Tests for translating between particular pairs of languages.'''

    def translation_test(self, source, target, sentences):
        '''Test whether there is at least one solution for each sentence.'''
        problems = [self.xdg(s, source, target=target) for s in sentences]
        solutions = [self.solve(p) for p in problems]
        for p, s in zip(problems, solutions):
            self.assertGreater(len(s), 0,
                               '{} has no solutions'.format(p))

    def enam(self):
        self.translation_test('en', ['am'], ENGLISH)

    def enqu(self):
        self.translation_test('en', ['qu'], ENGLISH)

    def esqu(self):
        self.translation_test('es', ['qu'], SPANISH)

if __name__ == '__main__':
    unittest.main()

### Old test sentences
# x = xdg("kuña omano", 'gn', semantics=False)
        
# x = xdg('veo la mujer que limpia la casa', 'es', solve=False)[0]
# y = xdg('tuve miedo de la casa', 'es', solve=False)[0]
# x = xdg('ve', 'es', solve=False, verbosity=1)[0]
# z = xdg('moriste en la casa', 'es', 'qu', solve=False)[0]
#x = xdg('limpia la casa', 'es', 'qu', transfer=True,
#        semantics=False, solve=False)[0]
# x = xdg(SPANISH[0], 'es', 'qu', transfer=False, solve=False, verbosity=1)[0]
# y = xdg('la mujer ve la casa', 'es', 'qu', solve=False, verbosity=1)[0]

#### Old stuff
# Grammatical Amharic
# a1 = l3xdg.XDG('አስቴር ሞተች', 'am')
# a2 = l3xdg.XDG('አስቴር ውሃውን አጠለለችው', 'am')
# a3 = l3xdg.XDG('ወንድ ውሃ አጠለለው', 'am')
# a4 = l3xdg.XDG('አስቴር ውሃ አጠለለች', 'am')
# a5 = l3xdg.XDG('ውሃ ቆሻሻ ነው', 'am')
# a6 = l3xdg.XDG('አንቺ ቆሻሻ ነሽ', 'am')
# 2 other tenses
# a7 = l3xdg.XDG('አስቴር ውሃውን ታጠልለዋለች', 'am')
# a8 = l3xdg.XDG('ውሃው ተበክሏል', 'am')

# Ungrammatical Amharic
# Ungrammatical because subject is accusative
# au0 = l3xdg.XDG('አስቴርን ውሃውን አጠለለችው', 'am')
# Ungrammatical because definite object is not accusative
# au1 = l3xdg.XDG('አስቴር ውሃው አጠለለችው', 'am')
# Ungrammatical because object is not definite
# au2 = l3xdg.XDG('አስቴር ውሃን አጠለለችው', 'am')

# Grammatical English
# e0 = l3xdg.XDG('Esther filtered the water')
# e1 = l3xdg.XDG('Esther filtered water')
# e2 = l3xdg.XDG('John cleaned water')
# Group (ambiguous)
# e3 = l3xdg.XDG('John broke the ice')
# e4 = l3xdg.XDG('some water flowed')
# e5 = l3xdg.XDG('the water is contaminated')
# e6 = l3xdg.XDG('the houses are contaminated')
# e7 = l3xdg.XDG('I am contaminated')
# e8 = l3xdg.XDG('the water was contaminated')
# e9 = l3xdg.XDG('you are dirty')
# e10 = l3xdg.XDG('the water is dirty')

# Ungrammatical English
# eu0 = l3xdg.XDG('the houses is contaminated')
# eu1 = l3xdg.XDG('the water are contaminated')

## English to Amharic

# ea1 = l3xdg.XDG('Esther filtered water', target=['am'])
# ea2 = l3xdg.XDG('Esther filtered the water', target=['am'])
# ea3 = l3xdg.XDG('Esther died', target=['am'])
# ea4 = l3xdg.XDG('the water is dirty', target=['am'])
# ea5 = l3xdg.XDG('you are dirty', target=['am'])
# Different tenses possible
# ea6 = l3xdg.XDG('Esther filters the water', target=['am'])
# Significant syntactic differences: COP + adj -> PRES PERF; 2 empty nodes
# (which create spurious ambiguity because of their positions)
# ea7 = l3xdg.XDG('the water is contaminated', target=['am'])

## Swahili

# Grammatical Swahili
#s1 = l3xdg.XDG('Ali alisema', 'sw')
# Object prefix on verb
#s2 = l3xdg.XDG('Ali anaziona nyumba', 'sw')
# Group (-piga simu): ambiguous
#s6 = l3xdg.XDG('Ali alipiga simu', 'sw')
# No object prefix on verb
#s3 = l3xdg.XDG('watoto walinunua simu', 'sw')
#s4 = l3xdg.XDG('watoto walinunua nyumba', 'sw')
#s5 = l3xdg.XDG('ali aliona motokaa', 'sw')
#s5 = l3xdg.XDG('ali alipiga nyumba', 'sw')

## Ungrammatical Swahili
# Agreement is wrong
#s7 = l3xdg.XDG('ali anawaona nyumba', 'sw')
# Order is wrong
#s8 = l3xdg.XDG('nyumba anaiona ali', 'sw')

## English to Swahili

# es1 = l3xdg.XDG('Ali spoke', target=['sw'])
# es4 = l3xdg.XDG('Ali saw me', target=['sw'])
# es6 = l3xdg.XDG('Ali bought the water', target=['sw'])




