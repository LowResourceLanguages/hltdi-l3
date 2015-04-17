#!/usr/bin/env python3

# Hiiktuu. Parsing and translation with minimal dependency grammars.
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

__version__ = 1.0

import hiiktuu

# Profiling
#import cProfile
#import pstats

def europarl_corpus(corpus=None, suffix='a', lines=0):
    corpus = corpus or hiiktuu.Corpus('ep')
    corpus.read("../../LingData/Es/Europarl/es-en/es-ep7" + suffix + ".anl", lines=lines)
    return corpus

def monton():
    return hiiktuu.Pattern(['montón', 'de', (None, (None, {('p', 'n')}))])

def test(verbosity=0):
    piece_of_mind_parse_ung(verbosity=verbosity)
    piece_of_mind_trans(verbosity=verbosity)
    kick_the_bucket(verbosity=verbosity)
    end_of_world(verbosity=verbosity)
    never_eaten_fish(verbosity=verbosity)
    never_eaten_fish_ungr(verbosity=verbosity)
    cantar_las_cuarenta_I(verbosity=verbosity)
    cantar_las_cuarenta_she(verbosity=verbosity)

def piece_of_mind_parse_ung(verbosity=0, all_sols=True):
    """
    Eng parse.
    Illustrates
    (1) within SL agreement (fails because 'my' doesn't agree with 'gives')
    """
    eng = hiiktuu.Language.load('eng')[0]
    s = hiiktuu.Sentence(raw='Mary gives them a piece of my mind',
                         language=eng,
                         verbosity=verbosity)
#    print("Parsing: {}".format(s.raw))
    s.initialize(verbosity=verbosity)
    s.solve(translate=False, verbosity=verbosity, all_sols=all_sols)
    return s

def piece_of_mind_trans(verbosity=0, all_sols=True):
    """
    Eng->Spa
    Illustrates
    (1) within SL agreement (succeeds because 'her' agrees with 'gives')
    (2) SL-TL feature agreement
    (3) SL-TL word count mismatch (SL > TL)
    """
    eng, spa = hiiktuu.Language.load('eng', 'spa')
    s = hiiktuu.Sentence(raw='Mary gives them a piece of her mind',
                         language=eng, target=spa,
                         verbosity=verbosity)
#    print("Translating {} to {}".format(s.raw, s.target))
    s.initialize(verbosity=verbosity)
    s.solve(translate=True, verbosity=verbosity, all_sols=all_sols)
    return s

def kick_the_bucket(verbosity=0, all_sols=True):
    """
    Eng->Spa
    Illustrates
    (1) SL group ambiguity (search for solutions)
    (2) SL-TL feature agreement
    """
    eng, spa = hiiktuu.Language.load('eng', 'spa')
    s = hiiktuu.Sentence(raw='John kicked the bucket', language=eng, target=spa,
                         verbosity=verbosity)
#    print("Translating {} to {}".format(s.raw, s.target))
    s.initialize(verbosity=verbosity)
    s.solve(verbosity=verbosity, all_sols=all_sols)
    return s

def end_of_world(verbosity=0, all_sols=True):
    """
    Eng->Spa
    it's the end of the world -> es el fin del mundo
    Illustrates
    (1) SL-TL word count mismatch (SL > TL)
    """
    eng, spa = hiiktuu.Language.load('eng', 'spa')
    s = hiiktuu.Sentence(raw="it's the end of the world", language=eng, target=spa,
                         verbosity=verbosity)
#    print("Translating {} to {}".format(s.raw, s.target))
    s.initialize(verbosity=verbosity)
    s.solve(verbosity=verbosity, all_sols=all_sols)
    return s

def ate_fish(verbosity=0, all_sols=True):
    """
    Amh->Orm
    አሳ በላ (he ate fish) -> qurxummii nyaate.
    Illustrates
    (1) SL-TL feature agreement
    """
    amh, orm = hiiktuu.Language.load('amh', 'orm')
    s = hiiktuu.Sentence(raw="አሳ በላ", language=amh, target=orm, verbosity=verbosity)
#    print("Translating {} to {}".format(s.raw, s.target))
    s.initialize(verbosity=verbosity)
    s.solve(verbosity=verbosity, all_sols=all_sols)
    return s

def never_eaten_fish(verbosity=0, trans=True, all_sols=True):
    """
    Amh አሳ በልቶ አያውቅም 'he's never eaten fish'
    Either parse (trans=False) or translate -> Orm: qurxummii nyaate hin beeku.
    Illustrates
    (1) SL-TL feature agreement
    (2) SL-TL word count mismatch (SL < TL)
    """
    amh, orm = hiiktuu.Language.load('amh', 'orm')
    s = hiiktuu.Sentence(raw="አሳ በልቶ አያውቅም", language=amh, target=orm,
                        verbosity=verbosity)
    s.initialize(verbosity=verbosity)
    if trans:
#        print("Translating {} to {}".format(s.raw, s.target))
        s.solve(verbosity=verbosity, all_sols=all_sols)
    else:
#        print("Parsing: {}".format(s.raw))
        s.solve(translate=False, verbosity=verbosity, all_sols=all_sols)
    return s

def never_eaten_fish_ungr(trans=True, verbosity=0, all_sols=True):
    """
    Amh አሳ በልተው አያውቅም 'he's never eaten fish' (ungrammatical because the
    በልተው is 3rd person *plural* so it doesn't agree with አያውቅም).
    Like the last case except since this is ungrammatical, no solution is
    found that covers all of the words.
    """
    amh, orm = hiiktuu.Language.load('amh', 'orm')
    s = hiiktuu.Sentence(raw="አሳ በልተው አያውቅም", language=amh, target=orm,
                        verbosity=verbosity)
#    print("Attempting to translate {} to {}".format(s.raw, s.target))
    s.initialize(verbosity=verbosity)
    s.solve(verbosity=verbosity, all_sols=all_sols)
    return s

def cantar_las_cuarenta_she(trans=True, verbosity=0, all_sols=True):
    """
    Spa->Eng
    Paula les cantó las cuarenta -> Paula read them the riot act.
                                 -> Paula gave them a piece of her mind.
    Illustrates
    (1) SL-TL feature agreement
    (2) SL-TL mismatch in word count (SL < TL)
    (3) SL-TL mismatch in word order
    (4) SL word not associated with any group
    (5) within-TL-group agreement
    """
    spa, eng = hiiktuu.Language.load('spa', 'eng')
    s = hiiktuu.Sentence(raw="Paula les cantó las cuarenta",
                        language=spa, target=eng if trans else None,
                        verbosity=verbosity)
#    print("Translating {} to {}".format(s.raw, s.target))
    s.initialize(verbosity=verbosity)
    s.solve(translate=trans, verbosity=verbosity, all_sols=all_sols)
    return s

def cantar_las_cuarenta_I(trans=True, verbosity=0, all_sols=True):
    """
    Spa->Eng
    les canté las cuarenta -> read them the riot act.
                           -> gave them a piece of my mind.
    Illustrates
    (1) SL-TL feature agreement
    (2) SL-TL mismatch in word count (SL < TL)
    (3) SL-TL mismatch in word order
    (4) SL word not associated with any group
    (5) within-TL-group agreement
    """
    spa, eng = hiiktuu.Language.load('spa', 'eng')
    s = hiiktuu.Sentence(raw="les canté las cuarenta",
                        language=spa, target=eng if trans else None,
                        verbosity=verbosity)
#    print("Translating {} to {}".format(s.raw, s.target))
    s.initialize(verbosity=verbosity)
    s.solve(translate=trans, verbosity=verbosity, all_sols=all_sols)
    return s

def ui():
    """Create a UI and two languages."""
    u = hiiktuu.UI()
    e, s = hiiktuu.Language("English", 'eng'), hiiktuu.Language("español", 'spa')
    return u, e, s

##def agr_test1():
##    # This should constraint seq vars seq0 and seq2 to be {2} and {3}
##    sel = hiiktuu.DetVar('sel', {(0, 1, ('sn', 'sn'), ('sp', 'sp')),
##                                (2, 3, ('tam', 'tns'))})
##    seq = [hiiktuu.Var('seq0', set(), {1, 2}, 1, 1), hiiktuu.DetVar('seq1', {0}),
##           hiiktuu.Var('seq2', set(), {3, 5}, 1, 1), hiiktuu.DetVar('seq3', {4})]
##    feat = [hiiktuu.DetLVar('f0', [hiiktuu.Features({'sn': 0, 'sp': 3})]),
##            hiiktuu.DetLVar('f1', [hiiktuu.Features({'sn': 1})]),
##            hiiktuu.DetLVar('f2', [hiiktuu.Features({'sn': 0, 'sp': 3, 'sg': 1})]),
##            hiiktuu.DetLVar('f3', [hiiktuu.Features({'tam': 'ps'})]),
##            hiiktuu.DetLVar('f4', [hiiktuu.Features({'tns': 'ps'})]),
##            hiiktuu.DetLVar('f5', [hiiktuu.Features({'tam': 'pr'})])]
##    agr = hiiktuu.AgrSelection(feat, sel, seq)
##    return agr
##
##def agr_test2():
##    # This should constrain feat var f0 to [{sn: 1, sp: 3}]
##    sel = hiiktuu.DetVar('sel', {(0, 1, ('sn', 'sn'), ('sp', 'sp')),
##                                (2, 3, ('tam', 'tns'))})
##    seq = [hiiktuu.DetVar('seq0', {2}), hiiktuu.DetVar('seq1', {0}),
##           hiiktuu.Var('seq2', set(), {3, 5}, 1, 1), hiiktuu.DetVar('seq3', {4})]
##    feat = [hiiktuu.LVar('f0', [], [hiiktuu.Features({'sn': 0, 'sp': 3}),
##                                   hiiktuu.Features({'sn': 0, 'sp': 2}),
##                                   hiiktuu.Features({'sn': 1, 'sp': 3})],
##                        1, 1),
##            hiiktuu.DetLVar('f1', [hiiktuu.Features({'sn': 1})]),
##            hiiktuu.DetLVar('f2', [hiiktuu.Features({'sn': 0, 'sp': 3, 'sg': 1})]),
##            hiiktuu.DetLVar('f3', [hiiktuu.Features({'tam': 'ps'})]),
##            hiiktuu.DetLVar('f4', [hiiktuu.Features({'tns': 'ps'})]),
##            hiiktuu.DetLVar('f5', [hiiktuu.Features({'tam': 'pr'})])]
##    agr = hiiktuu.AgrSelection(feat, sel, seq)
##    return agr
##
##def agr_test3():
##    # This should fail.
##    sel = hiiktuu.DetVar('sel', {(0, 1, ('sn', 'sn'), ('sp', 'sp')),
##                                (2, 3, ('tam', 'tns'))})
##    seq = [hiiktuu.DetVar('seq0', {2}), hiiktuu.DetVar('seq1', {0}),
##           hiiktuu.Var('seq2', set(), {3, 5}, 1, 1), hiiktuu.DetVar('seq3', {4})]
##    feat = [hiiktuu.LVar('f0', [], [hiiktuu.Features({'sn': 0, 'sp': 3}),
##                                   hiiktuu.Features({'sn': 0, 'sp': 2}),
##                                   hiiktuu.Features({'sn': 1, 'sp': 3})],
##                        1, 1),
##            hiiktuu.DetLVar('f1', [hiiktuu.Features({'sn': 1})]),
##            hiiktuu.DetLVar('f2', [hiiktuu.Features({'sn': 0, 'sp': 1, 'sg': 1})]),
##            hiiktuu.DetLVar('f3', [hiiktuu.Features({'tam': 'ps'})]),
##            hiiktuu.DetLVar('f4', [hiiktuu.Features({'tns': 'ps'})]),
##            hiiktuu.DetLVar('f5', [hiiktuu.Features({'tam': 'pr'})])]
##    agr = hiiktuu.AgrSelection(feat, sel, seq)
##    return agr
##
##def agr_test4():
##    # This should be entailed.
##    sel = hiiktuu.DetVar('sel', {(0, 1, ('sn', 'sn'), ('sp', 'sp')),
##                                (2, 3, ('tam', 'tns'))})
##    seq = [hiiktuu.DetVar('seq0', {2}), hiiktuu.DetVar('seq1', {0}),
##           hiiktuu.Var('seq2', set(), {3, 5}, 1, 1), hiiktuu.DetVar('seq3', {4})]
##    feat = [hiiktuu.LVar('f0', [], [hiiktuu.Features({'sn': 0, 'sp': 1}),
##                                   hiiktuu.Features({'sn': 0, 'sp': 1, 'sg': 1}),
##                                   hiiktuu.Features({'sn': 0, 'sg': 3})],
##                        1, 1),
##            hiiktuu.DetLVar('f1', [hiiktuu.Features({'sn': 1})]),
##            hiiktuu.DetLVar('f2', [hiiktuu.Features({'sn': 0, 'sp': 1, 'sg': 1})]),
##            hiiktuu.DetLVar('f3', [hiiktuu.Features({'tam': 'ps'})]),
##            hiiktuu.DetLVar('f4', [hiiktuu.Features({'tns': 'ps'})]),
##            hiiktuu.DetLVar('f5', [hiiktuu.Features({'tam': 'ps', 'sn': 2})])]
##    agr = hiiktuu.AgrSelection(feat, sel, seq)
##    return agr

if __name__ == "__main__":
    print('HIIKTUU, version {}\n'.format(__version__))

