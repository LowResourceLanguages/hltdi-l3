########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010, 2011, 2012, 2013
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
#    Author: Michael Gasser <gasser@cs.indiana.edu>
#
# 2009.11.18
#
# 2009.11.30
# Updated to include morphology
#
# 2010.04.15
# Semantics added (some time back)
# Labels updated to include 'rel': from root into
# relative clause verb
#
# 2010.10.23
# -- extract function for converting feature values from morphological
#    analysis to integers
# 2010.12.23
# -- added water grammar
# 2011.01.01
# -- dict2fs takes value of defob into account, generating no obj
#    agreement if its False (== (0,))
# 2011.01.11
# -- fixed how rl feature is handled
# 2011.01.13
# -- add copula to dict2fs
# 2011.01.16
# -- tense, aspect, mood features in extract and dict2fs
# -- (this module is getting ugly; about time to clean it up!)
# 2011.02.25 - 03.09
# -- changes to accommodate new PNG features
# 2012.02.18
# -- non-possessive nouns get poss=(0,)
# 2013.01.03
# -- function to correct definiteness of demonstratives, as output
#    by morphology.

from ... import language
from ...morphology import morphology
from ...morphology.geez import *

TUP2FEATS = (# 1 person
             {0: (('p1', False),), 1: (('p1', True),)},
             # 2 person
             {0: (('p2', False),), 1: (('p2', True),)},
             # number
             {0: (('plr', False),), 1: (('plr', True),)},
             # gender
             {0: (('fem', False),), 1: (('fem', True),), '*': (('fem', False),)},
             # formality
             {0: (('frm', False),), 1: (('frm', True),), '*': (('frm', False),)},
             # applicative
             {0: (('prp', False), ('b', False), ('l', False)),
              1: (('prp', True), ('b', False), ('l', True)),
              2: (('prp', True), ('b', True), ('l', False)),
             '*': (('prp', False), ('b', False), ('l', False))}
              )

ASFEATS = {1: 'smp', 2: 'rc', 3: 'it'}
VCFEATS = {1: 'smp', 2: 'ps', 3: 'tr', 4: 'cs'}
TAM = ['imf', 'prf', 'ppf', 'j_i', 'ger', 'prs', 'pst']

def simplify_fv(fv):
    '''Drop a sublist of -1s from the end of the list.'''
    pos = len(fv)-1
    while fv[pos] == -1 and pos >= 0:
        pos -= 1
#    for pos in range(len(fv)-1, -1, -1):
#        if fv[pos] != -1:
#            break
    return fv[:pos+1]

def preprocess(form):
    return geez2sera(GEEZ_SERA['am'][0], form, lang='am')

def postprocess(form):
    return sera2geez(GEEZ_SERA['am'][1], form, lang='am')

def correct_morpho(pos, root, fs):
    """Fix 'errors' in morphological analysis."""
    fs = fs.unfreeze()
    if pos == 'n':
        if root in ['yh', 'yhc', 'yc_i', 'ya', 'yac_i']:
            fs['def'] = True
#        if root in ['yhc', 'yc_i', 'yac_i', 'sEt', "'astEr"]:
#            fs['fem'] = True
    return fs

### Convert FeatStruct to feature dict for analysis

def extract(analysis):
    """Extract relevant features from FSs in analysis, returning as dict.
    """
    pos = analysis[0]
    root = analysis[1]
    citation = analysis[2]
    fs = analysis[3]
    # Dict of feat-values to replace fs
    res = dict()
    # Possibly new feat-values to add to set for language
    fvs = set()
    fs = correct_morpho(pos, root, fs)
    if pos == 'n':
        # 'png' features
        if not 'png' in res:
            res['png'] = {}
        val = argvals2ints(fs, False)
        # Later allow for indeterminate number?
        if fs.get('plr'):
            res['num'] = {(2,)}
        else:
            res['num'] = {(1,)}
        res['png'] = {val}
        fvs.add(('png', val))
    # Other features
    for feat in ['sb', 'ob', 'poss', 'tm', 'sub', 'rel', 'neg', 'def', 'acc', 'gen', 'pp', 'cnj', 'cj1', 'cj2', 'rl']:
        val = fs.get(feat)
#        if feat == 'def':
#            # Adjust for -def of demonstratives
#            if root in {'yh', 'yhc', 'yc_i', 'ya', 'yac_i'}:
#                val = True
        if val != None:
            # FeatStruct value
            if feat in ['sb', 'ob', 'poss'] and isinstance(val, morphology.FeatStruct):
                # Handle possession later
                if feat in ['poss']:
                    if val.get('expl', False) == False:
#                        val = set()
#                        val = (-2,)
                        # Not possessive
                        val = (0,)
                    else:
                        val = argvals2ints(val)
#                        val = (1,)
                elif val.get('expl', True) == False:
                    if fs.get('def', False) == True:
                        # +def, ob=[-expl]; prevent this analysis for transitive verbs
                        res['trans'] = {(0,)}
                        fvs.add(('trans', (0,)))
                    # Don't do anything else for non-explicit object
                    continue
                else:
                    # Convert argument feat values to tuple of ints
                    val = argvals2ints(val, feat == 'ob')
                    if feat == 'ob':
                        res['trans'] = {(1,)}
                        fvs.add(('trans', (1,)))
                        res['defob'] = {(1,)}
                        fvs.add(('defob', (1,)))
            # String value
            elif feat in ['tm']:
                val = tam2int(val, fs)
                val = (val,)
            elif feat in ['rl']:
                val = role2ints(val, definite=fs.get('def'))
            # Boolean value; convert to tuple of one integer
            else:
                val = (int(val),)
            # Values must appear in sets
#            print('res', res, 'feat', feat, 'val', val)
            if isinstance(val, set):
                res[feat] = val
            else:
                res[feat] = {val}
                fvs.add((feat, val))
#    print('Analysis:', res)
    return citation, res, fvs

def tam2int(val, fs):
    if val == 'ger':
        aux = fs.get('ax')
        if aux == 'al':
            return 2
        else:
            return 4
    elif val == 'prs':
        # Treat present like imperfective
        return 0
    else:
        return TAM.index(val)

def boolfeat2int(values, ints, val_ints, index=0):
    """Convert boolean features to integers, append to ints list."""
    val, integ = val_ints[index]
    # (val1 == False), (val2 == False), ... represented as (val1, val2, ...)
    if isinstance(val, tuple) and all([values.get(v, None) == False for v in val]):
        ints.append(integ)
    elif val == '*' or values.get(val, None) == True:
        ints.append(integ)
    else:
        boolfeat2int(values, ints, val_ints, index=index+1)

def argvals2ints(argvals, obj=False):
#    print('argvals2ints', argvals)
    ints = []
    # Person 1
    boolfeat2int(argvals, ints, [('p1', 1), ('*', 0)])
    # Person 2
    boolfeat2int(argvals, ints, [('p2', 1), ('*', 0)])
    # Number
    boolfeat2int(argvals, ints, [('plr', 1), ('*', 0)])
    # Gender; if not p1 and not plural
    if not argvals.get('p1') and not argvals.get('plr'):
        boolfeat2int(argvals, ints, [('fem', 1), ('*', 0)])
#    # Formality; if formality is explicit ...
#    if 'frm' in argvals:
#        boolfeat2int(argvals, ints, [('frm', 1), ('*', 0)])
#    # ... otherwise for all other second person singular, make not formal
#    elif argvals.get('p2') and not argvals.get('plr'):
#        ints.append(0)
#    # For objs only, applicative
#    if obj:
#        boolfeat2int(argvals, ints, [('l', 1), ('b', 2), ('*', 0)])
#    ints = simplify_fv(ints)
#    print('ints', ints)
    return tuple(ints)
    
def role2ints(rolevals, definite=None):
    """Convert values of role feature to ints."""
#    print('Getting rolevals', rolevals, definite)
    # Why was this here? Should indefinite nouns have *no* role?
#    if not definite:
#        return set()
    acc = rolevals.get('acc')
    prep = rolevals.get('p')
    if acc:
        return (1,)
    elif prep:
        return (2,)
    return (0,)

### Convert feature dict to FeatStruct for generation

def dict2fs(dct):
    fs = morphology.FeatStruct()
    pos = dct.get('pos')
    if pos == 'v':
        fs['pos'] = 'v'
        # Verbs need acc, as, ax, cj1, cj2, def, neg, ob, pp, rel, rl, sb, sub, tm, vc, ye; pos
        fs['acc'], fs['def'], fs['neg'] = False, False, False
        fs['rel'], fs['sub'], fs['ye'] = False, False, False
        fs['cj1'], fs['cj2'], fs['pp'] = None, None, None
        fs['rl'] = morphology.FeatStruct('[-acc,-p]')
        # sb, ob
        sbj = dct.get('sb', ())
        # Values in dct are tuples of ints; convert them to FSs
        if sbj:
            fs['sb'] = inttup2feats(sbj)
        # Definite object? If not, no obj agreement
        defobj = dct.get('defob', None)
        obj = dct.get('ob', None)
        if defobj != (0,) and obj:
            fs['ob'] = inttup2feats(obj, True)
        else:
            fs['ob'] = morphology.FeatStruct('[-expl]')
        inttup2der(fs, dct.get('der'))
        # TAM and aux: fix later
        fs['tm'], fs['ax'] = get_tam(dct)
    elif pos == 'cop':
        # Copula needs cj2, neg, sb; ob=[-expl], -rel, -sub, tm='prs'
        fs['pos'] = 'cop'
        fs['rel'], fs['sub'], fs['neg'] = False, False, False
        fs['ob'] = morphology.FeatStruct('[-expl]')
        # Fix this later
        fs['tm'] = 'prs'
        fs['cj2'] = None
        sbj = dct.get('sb', ())
        # Values in dct are tuples of ints; convert them to FSs
        if sbj:
            fs['sb'] = inttup2feats(sbj)
    else:
        # nouns
        png = dct.get('png', ())
        poss = dct.get('poss')
        num = dct.get('num')
        fs['pos'] = 'n'
        fs['fem'], fs['p1'], fs['p2'], fs['plr'] = False, False, False, False
        if len(png) > 3 and png[3] == 1:
            fs['fem'] = True
        if len(png) > 0 and png[0] == 1:
            fs['p1'] = True
        if len(png) > 1 and png[1] == 1:
            fs['p2'] = True
        if len(png) > 2 and png[2] == 1:
            fs['plr'] = True
            # fem must be - for plural
            fs['fem'] = False
        fs['def'] = dct.get('def') == (1,)
        fs['rl'] = inttup2role(dct)
        fs['acc'] = fs['rl']['acc']
        fs['prp'] = dct.get('prp') == (1,)
        fs['ass'], fs['dis'], fs['gen'], fs['itu'] = False, False, False, False
        fs['cnj'], fs['pp'], fs['v'] = None, None, None
        if poss and poss != (0,):
            fs['poss'] = inttup2feats(poss, True)
        else:
            fs['poss'] = morphology.FeatStruct('[-expl]')
#    print('Dict', dct)
#    print('FS', fs.__repr__())
    return morphology.FSSet(fs)

def get_tam(dct):
    tam = dct.get('tm')
    tam_int = tam[0] if tam else 0
    feat_val = TAM[tam_int]
    if feat_val == 'ppf':
        # Present perfect is gerundive + -al
        return 'ger', 'al'
    elif feat_val == 'imf':
        # Imperfective requires -al aux
        return 'imf', 'al'
    else:
        # tm value, ax value
        return feat_val, None

def inttup2role(dct, pos='n'):
    '''+acc means *morphologically* accusative (-n), not syntactically,
    use +acc and rl=[+acc,...] only if dct.get('def').
    Note: does not yet handle genitive or case-marked (prepositional) nouns.'''
    definite = dct.get('def', False) == (1,)
    rl = dct.get('rl')
#    acc = dct.get('acc')
    if rl == (1,) and definite:
        return morphology.FeatStruct('[+acc,-gen,-p]')
    else:
        return morphology.FeatStruct('[-acc,-gen,-p]')
    
def inttup2feats(tup, obj=False):
#    print('tup {}'.format(tup))
    fs = morphology.FeatStruct()
    for integ, dct in zip(tup, TUP2FEATS):
        featvalues = dct[integ]
        for feat, value in featvalues:
            fs[feat] = value
    # Features not included in tuple
    for dct in TUP2FEATS[len(tup):]:
        featvalues = dct.get('*')
        if featvalues:
            for feat, value in featvalues:
                fs[feat] = value
    if obj:
        fs['expl'] = True
    return fs

def inttup2der(fs, tup):
    '''Assign aspect and voice values from integer tuple of features.'''
    fs['vc'] = VCFEATS[tup[0]]
    fs['as'] = ASFEATS[tup[1]]

# Functions that simplifies Amharic orthography
#AMHARIC.morphology.simplify = lambda word: simplify(word)
#AMHARIC.morphology.orthographize = lambda word: orthographize(word)

def simplify(word):
    """Simplify Amharic orthography."""
    word = word.replace("`", "'").replace('H', 'h').replace('^', '').replace('_', '')
    return word

def orthographize(word):
    '''Convert phonological romanization to orthographic.'''
    word = word.replace('_', '').replace('I', '')
    return word

SEG = [["a", "e", "E", "i", "I", "o", "u", "H", "w", "y", "'", "`", "_", "|", "*"],                            
       {"b": ["b", "bW"], "c": ["c", "cW"], "C": ["C", "CW"], "d": ["d", "dW"],
        "f": ["f", "fW"], "g": ["g", "gW"], "h": ["h", "hW"], "j": ["j", "jW"],
        "k": ["k", "kW"], "l": ["l", "lW"], "m": ["m", "mW"], "n": ["n", "nW"],
        "p": ["p", "pW"], "P": ["P", "PW"], "N": ["N", "NW"], "q": ["q", "qW"],
        "r": ["r", "rW"], "s": ["s", "sW"], "S": ["S", "SW"], "t": ["t", "tW"],
        "T": ["T", "TW"], "v": ["v", "vW"], "x": ["x", "xW"], "z": ["z", "zW"],
        "Z": ["Z", "ZW"], "^": ["^s", "^S", "^h", "^hW", "^sW", "^SW"]}]

AMHARIC = {'': language.Language('አማርኛ', 'am', morph_processing=True,
                                 seg_units=SEG,
                                 labels={'am-syn': ['sb', 'ob', 'top', 'pob', 'adv', 'sub',
                                                    # links FROM modifiers to noun
                                                    'det', 'adj', 'rel',
                                                    # del for 0 arguments?
                                                    'del',
                                                    'prp', 'mv', 'root']},
                                 extract=extract, dict2fs=dict2fs,
                                 postproc=postprocess, preproc=preprocess,
                                 eos_chars=['።', '፧', '!', '?']),
           'water': language.Language('አማርኛ', 'am', morph_processing=True,
                                      seg_units=SEG,
                                      labels={'am-id': ['sb', 'ob', 'top',
                                                        # indirect object?
                                                        'pob', 'adv',
                                                        # predicate adjective or nominative
                                                        'pred',
                                                        # subordinate
                                                        'sub',
                                                         # links FROM modifiers to noun
                                                         'det', 'adj', 'rel',
                                                         # del for 0 arguments?
                                                         'del',
                                                         'prp', 'mv', 'root'],
                                              'am-lp': [# where complements go
                                                        'compf',
                                                        # where predicative adj and noun go
                                                        'predf',
                                                        # post-relative clause in cleft Ss
                                                        'prelf',
                                                        # noun position in NPs?
                                                        'nf',
                                                        'del', 'root']},
                                      lexicon_name='water',
                                      extract=extract, dict2fs=dict2fs,
                                      postproc=postprocess, preproc=preprocess,
                                      eos_chars=['።', '፧', '!', '?']),
           'tiny': language.Language('አማርኛ', 'am', morph_processing=True,
                                      seg_units=SEG,
                                      labels={'am-id': ['sb', 'ob', 'top', 'del', 'root',
                                                        # Added 2011.9.9
                                                        'pred',
                                                        # Added 2013.1.1: for zero possessives
                                                        'poss',
                                                        # Added 2013.1.2: heads of NPs with modifiers
                                                        'nhead',
                                                        # Added 2013.1.12: empty rel clause antecedent
                                                        'antec'
                                                        ],
                                              'am-lp': ['compf', 'del', 'root',
                                                        # Added 2011.9.9
                                                        'predf',
#                                                        # Added 2012.12.30
#                                                        'detf'
                                                        # Added 2013.1.2: heads of NPs with modifiers
                                                        'nheadf'
                                                        ]},
                                      lexicon_name='tiny',
                                      extract=extract, dict2fs=dict2fs,
                                      postproc=postprocess, preproc=preprocess,
                                      eos_chars=['።', '፧', '!', '?'])
        }

for gram in AMHARIC.values():
    morph = morphology.Morphology(pos_morphs=['cop', 'n', 'v'], 
                                  # Exclude ^ and - (because it can be used in compounds)
                                  punctuation=r'[“‘”’–—:;/,<>?.!%$()[\]{}|#@&*\_+=\"፡።፣፤፥፦፧፨]',
                                  # Include digits?
                                  characters=r'[a-zA-Zሀ-ፚ\'`^]')
    gram.set_morphology(morph)
    morph['v'].defaultFS = morphology.FeatStruct(
'''[pos=v,tm=prf,as=smp,vc=smp,\
sb=[-p1,-p2,-plr,-fem,-frm],ob=[-expl,-p1,-p2,-plr,-fem,-b,-l,-prp,-frm],\
cj1=None,cj2=None,pp=None,ax=None,-neg,-rel,-sub,-def,-acc,-ye,\
rl=[-acc,-p,-adv,-comp]]''')
    morph['v'].FS_implic = {'rel': ['sub'], 'cj1': ['sub'], 'pp': ['rel', 'sub'],
                            'def': ['rel', 'sub'],
                            'l': ['prp'], 'b': ['prp'], 'ob': [['expl']]}
    morph['v'].citationFS = morphology.FeatStruct(
'''[pos=v,tm=prf,sb=[-p1,-p2,-plr,-fem],\
ob=[-expl],cj1=None,cj2=None,pp=None,ax=None,-ye,\
-neg,-rel,-sub,-def,-acc,rl=[-p,-acc,-adv,-comp]]''')

    morph['n'].defaultFS = morphology.FeatStruct(
'''[pos=n,-acc,-def,-neg,-itu,as=smp,\
cnj=None,-dis,-gen,\
poss=[-expl,-p1,-p2,-plr,-fem,-frm],\
-p1,-p2,-plr,-fem,-frm,\
pp=None,v=None,vc=smp,\
rl=[-acc,-p,-gen]]''')
    morph['n'].FS_implic = {'poss': [['expl']]}
    # defaultFS with voice and aspect unspecified
    morph['n'].citationFS = morphology.FeatStruct(
'''[-acc,-def,-neg,-fem,cnj=None,\
-dis,-gen,-plr,poss=[-expl],pp=None,v=inf,\
rl=[-acc,-p,-gen]]''')
    morph['cop'].defaultFS = morphology.FeatStruct(
'''[cj2=None,-neg,ob=[-expl],-rel,\
sb=[-fem,-p1,-p2,-plr,-frm],-sub,tm=prs]''')
