########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2011, 2012, 2013
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
# 2011.03.13
# -- created
# 2011.03.14
# -- agreement tuples: (p1, 2, pl); gender: (0, 1)
#     yo: (1,0,0)
#     tú: (0,1,0,0)
#     usted: (0,0,0)
#     él: (0,0,0); (0)
#     ella: (0,0,0); (1)
#     nosotros: (1,-1,1)
#     nosotras: (1,-1,1); (1)
#     vosotros: (0,1,1)
#     vosotras: (0,1,1); (1)
#     ustedes: (0,0,1)
#     ellos: (0,0,1); (0)
#     ellas: (0,0,1); (1)
#    Ambiguity of (0,0,0) and (0,0,1) is reflected in translation of
#     of usted, él, etc. to Semantics
# -- TAM
#    0: pres, 1: pret, 2: fut, 3: impf, 4: imprv, 5: cond, 6: subj pres, 7: subj impf
#    For now only handle pres, pret, fut.
# -- Case
#    0: sb, 1: ojd, 2: oji, 3: prep
# -- Reflexive verbs
#    rfl: (1), sb must agree with ojd or oji pn feature; ojd or oji must also have rfl=(1)
# 2012.11
# -- Chunk grammar
# -- Subject and object slots in LF (preargf, postargf)
# 2012.12.08
# -- Some arc labels changed to make them more Spanish

from ... import language
from ...morphology import morphology

TUP2FEATS = (# 1 person
             {0: (('1', False),), 1: (('1', True),)},
             # 2 person
             {0: (('2', False),), 1: (('2', True),)},
             # number
             {0: (('p', False),), 1: (('p', True),)}
             )

### Convert FeatStruct to feature dict for analysis

def chunk_extract(analysis):
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
    pos2 = fs.get('pos')
    if pos2 == 'n':
        # Save for later
        pass
    # Other features
    elif pos2 == 'adj':
        pass
    elif pos2 == 'adv':
        res['tam'] = {(-2,)}
        res['as'] = {(-2,)}
    else:
        tam = fs.get('tam')
        asp = fs.get('as')
        if not tam or not asp or asp.get('cnt') or asp.get('prf'):
            res['sj'] = {(-2,)}
        tam_val = tam2int(tam or {}, asp or {})
        res['tam'] = {(tam_val,)}
        if asp:
            asp_val = as2int(asp)
            res['as'] = {(asp_val,)}
#        print('root', root, 'tam', res.get('tam'), 'asp', res.get('as'))
        for feat in ['sj', 'ojd', 'oji']:
            val = fs.get(feat)
            synfeat = feat
#            if feat in ['ojd', 'oji']:
#                synfeat = 'oj'
#                if val == None or val.get('xpl') == True:
#                    # (-1) represents no pronoun object
#                    fvs.add((synfeat, {(-1,)}))
            if val != None and val.get('xpl') != False:
                # FeatStruct value
                if isinstance(val, morphology.FeatStruct):
                    # Convert argument feat values to tuple of ints
                    val = argvals2ints(val, 'o' in feat)
#                else:
#                    val = (int(val),)
#                # Values must appear in sets
                    res[synfeat] = {val}
                    fvs.add((synfeat, val))
    return citation, res, fvs

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
    pos2 = fs.get('pos')
    if pos2 == 'n':
        # Save for later
        pass
#        # 'png' features
#        if not 'png' in res:
#            res['png'] = {}
#        val = argvals2ints(fs, False)
#        # Later allow for indeterminate number?
#        if fs.get('p'):
#            res['num'] = {(2,)}
#        else:
#            res['num'] = {(1,)}
#        res['png'] = {val}
#        fvs.add(('png', val))
    # Other features
    elif pos2 == 'adj':
        pass
    elif pos2 == 'adv':
        res['tam'] = {(-2,)}
        res['as'] = {(-2,)}
    else:
        tam = fs.get('tam')
#        asp = fs.get('as')
#        if not tam or not asp or asp.get('cnt') or asp.get('prf'):
#            res['sj'] = {(-2,)}
        if tam.get('ger'):
            # Gerundio; ambos tiempos posibles, -cont, +-prf
#            res['tam'] = {(0,), (1,)}
            res['cont'] = {(1,)}
            res['inf'] = {(0,)}
            res['fin'] = {(0,)}
        elif tam.get('part'):
#            res['tam'] = {(0,), (1,)}
            res['prf'] = {(1,)}
            res['inf'] = {(0,)}
            res['fin'] = {(0,)}
        elif tam.get('inf'):
            res['cont'] = {(0,)}
            res['prf'] = {(0,)}
            res['inf'] = {(1,)}
            res['fin'] = {(0,)}
        else:
            tam_val = tam2int(tam or {})
            res['cont'] = {(0,)}
            res['prf'] = {(0,)}
            res['inf'] = {(0,)}
            res['fin'] = {(1,)}
            res['tam'] = {(tam_val,)}
#        if asp:
#            asp_val = as2int(asp)
#            res['as'] = {(asp_val,)}
#        print('root', root, 'tam', res.get('tam'), 'asp', res.get('as'))
        for feat in ['sj', 'od', 'oi']:
            val = fs.get(feat)
            synfeat = feat
#            if feat == 'sj':
#                synfeat = 'sj'
            if val != None and val.get('xpl') != False:
                # FeatStruct value
                if isinstance(val, morphology.FeatStruct):
                    # Convert argument feat values to tuple of ints
                    val = argvals2ints(val, 'o' in feat)
#                else:
#                    val = (int(val),)
#                # Values must appear in sets
                    res[synfeat] = {val}
                    fvs.add((synfeat, val))
    return citation, res, fvs

def tam2int(fs):
    '''Convert a FS with boolean values prt, fut, imf, imv, sub, tns to an int.'''
    if fs.get('prt'):
        # Either pret or subj pret
        return 1
    elif fs.get('fut'):
        return 2
    elif fs.get('imv'):
        return 4
    else:
        return 0

def as2int(fs):
    if fs.get('cnt'):
        return 1
    elif fs.get('prf'):
        return 2
    else:
        return 0
        
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
    '''Convert FS for sj, ojd, or oji to a tuple: (1, 2, p).'''
#    print('argvals2ints', argvals)
    ints = []
    # Person 1
    boolfeat2int(argvals, ints, [('1', 1), ('*', 0)])
    # Person 2
    boolfeat2int(argvals, ints, [('2', 1), ('*', 0)])
    # Number
    boolfeat2int(argvals, ints, [('p', 1), ('*', 0)])
#    # Gender; if not 1
#    if not argvals.get('1'):
#        boolfeat2int(argvals, ints, [('fem', 1), ('*', 0)])
#    # Formality; if formality is explicit ...
#    if 'frm' in argvals:
#        boolfeat2int(argvals, ints, [('frm', 1), ('*', 0)])
#    # ... otherwise for all other second person singular, make not formal
#    elif argvals.get('2') and not argvals.get('p'):
#        ints.append(0)
#    # For objs only, applicative
#    if obj:
#        boolfeat2int(argvals, ints, [('l', 1), ('b', 2), ('*', 0)])
#    ints = simplify_fv(ints)
    return tuple(ints)
    
### Convert feature dict to FeatStruct for generation

def dict2fs(dct, verbose=False):
    fs = morphology.FeatStruct()
    pos = dct.get('pos')
    if pos == (1,):
        # Verbs have sj, tns; sometimes ojd, oji, refl
        fs['refl'] = dct.get('refl', False)
        fs['tam'] = get_tam(dct)
        # sb, ob
        sbj = dct.get('sj', ())
        # Values in dct are tuples of ints; convert them to FSs
        if sbj:
            fs['sj'] = inttup2feats(sbj)
        # No objects for now
        fs['od'] = morphology.FeatStruct("[-xpl]")
        fs['oi'] = morphology.FeatStruct("[-xpl]")
    else:
        print("Don't know how to generate", pos)
    fs = morphology.FSSet(fs)
    if verbose:
        print('FS {}'.format(fs.__repr__()))
    return fs

def get_tam(dct):
    # Only does past (1) and present (0) so far.
    tam = dct.get('tam')
    if tam == (1,):
        return morphology.FeatStruct("[-ipf,-cnd,-fut,-imv,+prt,-sub,+tmp]")
    else:
        return morphology.FeatStruct("[-ipf,-cnd,-fut,-imv,-prt,-sub,+tmp]")

def inttup2feats(tup, obj=False):
    fs = morphology.FeatStruct()
    for integ, dct in zip(tup, TUP2FEATS):
        featvalues = dct[integ]
        for feat, value in featvalues:
            fs[feat] = value
    # Features not included in tuple
#    for dct in TUP2FEATS[len(tup):]:
#        featvalues = dct['*']
#        for feat, value in featvalues:
#            fs[feat] = value
    if obj:
        fs['xpl'] = True
    return fs

SEG=[['a', 'b', 'd', 'e', 'f', 'g', 'h', 'i', 'j',
      'm', 'n', 'ñ', 'o', 'p', 's', 't', 'u', 'v',
      'x', 'y', 'z', 'á', 'é', 'í', 'ó', 'ú', 'ü',
      # foreign words
      'k', 'w',
      # upper case
      'A', 'B', 'D', 'E', 'F', 'G', 'H', 'I', 'J',
      'M', 'N', 'Ñ', 'O', 'P', 'S', 'T', 'U', 'V',
      'X', 'Y', 'Z', 'Á', 'É', 'Í', 'Ó', 'Ú', 'Ü', 'K', 'W'
#       # morphophonemic characters
#      'E', 'O', 'I', 'U', '!',
#      'C', 'K', 'J', 'Z', 'G', "'", "`", '_'
      ],
     {'c': ['c', 'ch'],
      'l': ['l', 'll'],
      'q': ['qu'],
      'r': ['r', 'rr'],
      'C': ['C', 'Ch'],
      'L': ['L', 'Ll'],
      'Q': ['Qu'],
      'R': ['R', 'Rr']}]

SPANISH = {'': language.Language('español', 'es', morph_processing=True,
                                 seg_units=SEG,
                                 labels={'es-syn': ['sj', 'ojd', 'oji', 'vmain',
                                                    'det', 'del', 'root']},
                                 extract=extract, dict2fs=dict2fs),
           'chunk': language.Language('español', 'es', morph_processing=True,
                                      seg_units=SEG,
                                      labels={'es-syn': [# NP
                                                         'det', 'preadj', 'postadj', 'cuan',
                                                         # PP
                                                         'pcomp',
                                                         # V
                                                         # 2013.08.20: added 'aux'; later change to 'prf'/'cont'
                                                         'arg', 'neg', 'pron', 'aux',
                                                         # 2013.10: predicate adjective/nominative/preposition
                                                         'apred', 'npred', 'ppred',
                                                         # CONJ
                                                         'conj1', 'conj2',
                                                         # other
                                                         'root', 'del',
                                                         '?'                  # unknown words
                                                         ]
                                              },
                                      feats=['pos', 'sj', 'oj', 'ng', 'tam', 'pn', 'rfl', 'neg', 'fin', 'cont', 'prf', 'inf'],
                                      hide_feats=['pos', 'fin'],
                                      lexicon_name='chunk',
                                      extract=extract, dict2fs=dict2fs),
           'tiny': language.Language('español', 'es', morph_processing=True,
                                     seg_units=SEG,
                                     labels={'es-id': ['sj', 'ojd', 'oji',
                                                       # AUX to MAIN verb
                                                       'vmain',
                                                       # Noun phrases
                                                       'rel', 'det',
                                                       # Prepositional phrases
                                                       # in    out
                                                       'pmod', 'pcomp',
                                                       # Added 11.12.08; VT -> a -> OJD
                                                       'ojdp',
                                                       # Added 12.07.31; reflexive object pronoun
                                                       'ojr',
                                                       # Added 12.12.08; pleonastic object pronoun
                                                       'ojpl',
                                                       # Added 12.09.25; relative pronoun antecedent
                                                       # (why ID graph is not a tree anymore...)
                                                       'antec',
                                                       # Added 12.12.08; pleonastic pronoun antecedent
                                                       'antple',
                                                       # Added 12.10.11; predicate nominal and adjective
                                                       'npred', 'apred',
                                                       'del', 'root'],
                                             'es-lp': [# Adverbs, prep phrase modifiers
                                                       'precf', 'postcf',
                                                       # Subjects and objects before and after verbs
                                                       'preargf', 'postargf',
                                                       # Determiners
                                                       'detf',
                                                       # Prepositional complements
                                                       'pcompf',
                                                       # Main verbs after auxiliaries
                                                       'vmainf',
                                                       # Relative clause verb after head noun
                                                       'relf',
                                                       # Relative pronoun
                                                       'relpf',
                                                       # Adjectives before and after noun
                                                       'preaf', 'postaf',
                                                       # Added 11.12.03; PP modifying nouns
                                                       'prpaf',
                                                       # Added 11.12.28; object pronouns
                                                       'ojprof',
                                                       'del', 'root']},
                                     lexicon_name='tiny',
                                     extract=extract, dict2fs=dict2fs)
           }

for gram in SPANISH.values():
    morph = morphology.Morphology(pos_morphs=['v'])
    gram.set_morphology(morph)

## agr_maps dictionary for translation to Gn: sj and oj mappings

SPANISH['chunk'].agr_maps = {'gn': {('sj', 'sj'): {(1,0,1): ((1,0,1), (1,1,1))},
                                    ('oj', 'oj'): {(-1,): ((0,0),), (1,0,1): ((1,0,1), (1,1,1))},
                                    ('ng', 'pl'): {(0,0): ((0,),), (0,1): ((0,),), (1,0): ((1,),), (1,1): ((1,),)}
                                    # Es continuous -> Gn aspect 2
#                                    ('cont', 'asp'): {(1,): ((2,),)},
#                                    # Es perfect -> Gn aspect 1 (not actually needed unless codes change)
#                                    ('prf', 'asp'): {(1,): ((1,),)}}}
                                    }}
                             

#    morph['v'].defaultFS = morphology.FeatStruct(
#'''[pos=v,tm=prf,as=smp,vc=smp,\
#sb=[-1,-2,-p,-fem,-frm],ob=[-expl,-1,-2,-p,-fem,-b,-l,-prp,-frm],\
#cj1=None,cj2=None,pp=None,ax=None,-neg,-rel,-sub,-def,-acc,-ye,\
#rl=[-acc,-p,-adv,-comp]]''')
#    morph['v'].FS_implic = {'rel': ['sub'], 'cj1': ['sub'], 'pp': ['rel', 'sub'],
#                            'def': ['rel', 'sub'],
#                            'l': ['prp'], 'b': ['prp'], 'ob': [['expl']]}
#    morph['v'].citationFS = morphology.FeatStruct(
#'''[pos=v,tm=prf,sb=[-1,-2,-p,-fem],\
#ob=[-expl],cj1=None,cj2=None,pp=None,ax=None,-ye,\
#-neg,-rel,-sub,-def,-acc,rl=[-p,-acc,-adv,-comp]]''')
