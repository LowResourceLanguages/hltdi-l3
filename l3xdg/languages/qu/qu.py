########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010 The HLTDI L^3 Team <gasser@cs.indiana.edu>
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
# 2011.02.04
# -- Tiny grammar
#    Generation (dict2fs) still doesn't work (it's just copied from
#    Amharic)
# 2011.03.10
# -- Generation (dict2fs, etc.) fixed for limited cases.

from ... import language
from ...morphology import morphology

### Subject/object agreement
### Person-number (pn): (1p, 2p, pl)
### (1,0,0): 1 p s
### (0,1,0): 2 p s
### (0,0,0): 3 p s (subj)
### (1,0,1): 1 p pl excl
### (1,1,1): 1 p pl incl
### (0,1,1): 2 p pl
### (0,0,1): 3 p pl (subj)
### (0,0):   3 p, number unspecified (obj)
### subj pn: [[1,0,0],[0,1,0],[0,0,0],[1,0,1],[1,1,1],[0,1,1],[0,0,1]]
### obj pn:  [[1,0,0],[0,1,0],[1,0,1],[1,1,1],[0,1,1],[0,0]]
### poss:    [[0],[1,1,0,0],[1,0,1,0],[1,0,0,0],[1,1,0,1],[1,1,1,1],[1,0,1,1],[1,0,0,1]]
###  (first position means +-explicit)
###
### Case
### nom,gen,intrc,pos,acc,ben,ill,abl,ins,trm,caus,loc,prol,dstr
### Put nom, acc, and gen in a separate position so they can be distinguished
### from "peripheral" cases
### 0: 1 (nom), 2 (acc), 3 (gen)
### 1: -pura (intrc='among'), -npa (pos), -nka (dstr)?, -nta (prol)? [-pa/-q (gen)]
### 2: -pi (loc), -paq (ben), -man (ill), -manta (abl), -rayku (caus) [-ta (acc)]
### 3: -kama (trm), -wan (ins)
### 1: 0, 1(intrc), 2(pos), 3(dstr), 4(prol)
### 2: 0, 1(loc), 2(ben), 3(ill), 4(abl), 5(caus)
### 3: 0, 1(ins), 2(trm)
### nom: (1,0,0,0), acc: (2,0,0,0), ins: (0,0,0,1)
### case0: 0, 1, 2, 3
### case1: 0,1,2,3,4
### case2: 0,1,2,3,4,5
### case3: 0,1,2
### case: [[1,0,0,0],[2,0,0,0],[3,0,0,0],
###        [0,0,1,0],[0,0,2,0],[0,0,3,0],[0,0,4,0],[0,0,5,0],
###        [0,0,0,1],[0,0,0,2]]
### (no multiple case markers)
###
### Pseudo-case
### -lla (der=[+lim,-incl]), -ntin (der=[+incl,-lim])
### Ignore for now?
###
### Number
### +- plural
### plur: [[0],[1]]
###
### Tense/aspect/mood
### ps,pp,ft,cd,im
### Present, past, future, present perfect, conditional, imperative
### For now, assume all are independent of one another
### tm = (0,):pres, (1,):past, (2,):fut, (3,):pp, (4,):cond, (5,):imp
### progressive: 0 or 1
### tm: [[0],[1],[2],[3],[4],[5]]
### prog: [[0],[1]]
###
### Nominalization
### No subject/possessor:: infinitive(1): -y, agent(2): -q
### Subject/possessor:: near future/oblig(3): -na, gerund(4): -spa, participle(5): -sqa, subordinate(6): -qti
### nom: [[0],[1],[2],[3],[4],[5],[6]]
###
### "Independent" suffixes
### 1: -puni
### 2: -pas/-pis (add), -wan (cop)
### 3: -ña (-cont), -raq (+cont) [0: cont=None]
### 4: -taq (seq)
### 5: -chu (non-assertive)
### 6: -mi/-n, -má: evidentiality=valid; -s(i), -sá evidentiality=reported;
###    -ri (responsive);
###    -ch(a), -chá: (prognosticator)
###    -suna, -sina (doubt)
###    -qa (topic) [evidentiality=None]
###    -yá (emotive), -tá (interj)
### For now, handle
### -pas/-pis, -wan; -ña; -taq(?); -chu; -mi/-n, -má, -s/-si; -ch/-chi; -qa
### conj: [[0],[1],[2]] (0, -pas/pis, -wan)
### assrt: [[0],[1]] (0, -chu)
### cont: [[0],[1],[2]] (0, -ña, -raq)
### top:  [[0],[1]] (0, -qa)
### ev:   [[0],[1],[2],[3],[4]] (0, -n/mi, -s/si, -má, -cha)
###
### Parts of speech
### pos=v, pos=n, pos=vn

CASE = {'case0': ['nom', 'acc', 'gen'],
        'case1': ['intrc', 'pos', 'dstr', 'prol'],
        'case2': ['loc', 'ben', 'ill', 'abl', 'caus'],
        'case3': ['ins', 'trm']}

TAM = ['pres', 'past', 'fut', 'impv', 'pp', 'cond']

### Convert FeatStruct to feature dict for analysis

def tam2tups(tamfs):
    if tamfs.get('ps'):
        return (1,)
    elif tamfs.get('ft'):
        return (2,)
    elif tamfs.get('pp'):
        return (3,)
    elif tamfs.get('cd'):
        return (4,)
    elif tamfs.get('im'):
        return (5,)
    else:
        return (0,)

def case2tups(casefs):
    # Default is nominative
    case0, case1, case2, case3 = 1, 0, 0, 0
    for index, feat in enumerate(CASE['case0']):
        if casefs.get(feat):
            case0 = index+1
            break
    for index, feat in enumerate(CASE['case1']):
        if casefs.get(feat):
            case1 = index+1
            case0 = 0
    for index, feat in enumerate(CASE['case2']):
        if casefs.get(feat):
            case2 = index+1
            case0 = 0
    for index, feat in enumerate(CASE['case3']):
        if casefs.get(feat):
            case3 = index+1
            case0 = 0
    return (case0, case1, case2, case3)

def pn2tup(fs, obj=False, poss=False):
    feats = [1] if poss else []
    p1 = fs.get('p1')
    p2 = fs.get('p2')
    feats.append(1 if p1 else 0)
    feats.append(1 if p2 else 0)
    if not obj or (p1 or p2):
        feats.append(1 if fs.get('pl') else 0)
    return tuple(feats)

def indep2tups(fs):
    conj = fs.get('conj')
    prag = fs.get('prag')
    contin = fs.get('asp', {}).get('contin')
    conjtup = (0,)
    assrttup = (0,)
    conttup = (0,)
    evtup = (0,)
    toptup = (0,)
    if conj:
        if conj.get('add'):
            conjtup = (1,)
        elif conj.get('cop'):
            conjtup = (2,)
    if contin:
        cont = contin.get('cont', None)
        if cont is True:
            conttup = (2,)
        elif cont is False:
            conttup = (1,)
    if prag:
        if prag.get('nonassr'):
            assrttup = (1,)
        ev = prag.get('ev', None)
        if ev is 'vald':
            if prag.get('emph'):
                evtup = (3,)
            else:
                evtup = (1,)
        elif ev is 'rprt':
            evtup = (2,)
        elif prag.get('progn'):
            evtup = (4,)
        if prag.get('top'):
            toptup = (1,)
    return conjtup, conttup, assrttup, toptup, evtup

def extract(analysis):
    """Extract relevant features from FSs in analysis, returning as dict.
    """
    root = analysis[1]
    citation = analysis[2]
    fs = analysis[3]
    # Doesn't allow for mixed POS, like 'vn'
    pos = fs.get('pos')
    # Dict of feat-values to replace fs
    res = dict()
    # Possibly new feat-values to add to set for language
    # (Not currently used)
    fvs = set()
    ### INDEPENDENT SUFFIXES
    conj, cont, qneg, top, ev = indep2tups(fs)
    res['conj'] = {conj}
    res['cont'] = {cont}
    res['qneg'] = {qneg}
    res['top'] = {top}
    res['ev'] = {ev}
    ### NOUNS
    if pos == 'n':
        ## POSSESSOR
        # If there is an explicit "sb" FS, treat it as the possessor
        poss = fs.get('sb')
        if poss and poss.get('expl'):
            val = pn2tup(poss, poss=True)
            res['poss'] = {val}
        else:
            res['poss'] = {(0,)}
        ## PERSON-NUMBER
        pn = pn2tup(fs)
        res['pn'] = {pn}
        if fs.get('pl'):
            res['num'] = {(2,)}
        else:
            res['num'] = {(1,)}
        ## CASE
        case = fs.get('cs')
        res['case'] = {case2tups(case)}
    ### VERBS
    elif pos == 'v':
        ## AGREEMENT WITH ARGUMENTS
        sb = fs.get('sb')
        val = pn2tup(sb)
        res['sb'] = {val}
        ob = fs.get('ob')
        # This makes the object 3p if there's no agreement on the verb
        # (rather than non-explicit/intransitive)
        val = pn2tup(ob, obj=True)
        res['ob'] = {val}
        ## TENSE/ASPECT/MOOD
        res['tm'] = {tam2tups(fs.get('tam'))}
        ## PROGRESSIVE
        res['prog'] = {(1,)} if fs.get('asp', {}).get('prg') else {(0,)}

    return citation, res, fvs

def simplify_fv(fv):
    '''Drop a sublist of -1s from the end of the list.'''
    pos = len(fv)-1
    while fv[pos] == -1 and pos >= 0:
        pos -= 1
#    for pos in range(len(fv)-1, -1, -1):
#        if fv[pos] != -1:
#            break
    return fv[:pos+1]

### Convert feature dict to FeatStruct for generation

def dict2fs(dct):
    fs = morphology.FeatStruct()
    pos = dct.get('pos')
    if pos == 'v':
        fs['pos'] = 'v'
        fs['pos2'] = 'v'
        fs['rpos'] = 'v'
        fs['tam'] = get_tam(dct)
        sb = dct.get('sb', ())
        ob = dct.get('ob', ())
        fs['sb'] = inttup2feats(sb, False)
        fs['ob'] = inttup2feats(ob, True)
        # Defaults for everything else
        fs['asp'] = morphology.FeatStruct('[contin=None,-prg]')
        fs['conj'] = morphology.FeatStruct('[-add,-cop,-seq]')
        fs['cs'] = None
        fs['der'] = morphology.FeatStruct('[-aug,-caus,-cisloc,-cnsc,-des,-dim,-fct,-inch,-lim,-pos,-rcp,-rfl]')
        fs['prag'] = morphology.FeatStruct('[-dbt,-emot,-emph,ev=None,-intj,-nonassr,-progn,-resp,-top,-xplc]')
#        fs['tr'] = False
    else:
        fs['pos'] = 'n'
        # 2nd POS
        pos2 = dct.get('pos2')
        if pos2 == (2,):
            fs['pos2'] = 'pron'
        else:
            fs['pos2'] = 'cn'
        # root POS
        fs['rpos'] = 'n'
        pn = dct.get('pn', ())
        fs['p1'], fs['p2'], fs['pl'] = False, False, False
        if len(pn) > 0 and pn[0]:
            fs['p1'] = True
        if len(pn) > 1 and pn[1]:
            fs['p2'] = True
        if len(pn) > 2 and pn[2]:
            fs['pl'] = True
        case = dct.get('case')
        fs['cs'] = inttup2case(case)
        # Pragmatic features: only topic so far
        topic = dct.get('top')
        if topic == (1,):
            fs['prag'] = morphology.FeatStruct('[-dbt,-emot,-emph,ev=None,-intj,-nonassr,-progn,-resp,+top,-xplc]')
        else:
            fs['prag'] = morphology.FeatStruct('[-dbt,-emot,-emph,ev=None,-intj,-nonassr,-progn,-resp,-top,-xplc]')
        # Defaults for everything else
        fs['asp'] = morphology.FeatStruct('[contin=None]')
        fs['conj'] = morphology.FeatStruct('[-add,-cop,-seq]')
        fs['der'] = morphology.FeatStruct('[-aug,-cnsc,-dim,-fct,-inch,-incl,-lim,-pos,-rcp,-rfl]')
        # Possessive
        if fs['pos2'] == 'cn':
            fs['sb'] = morphology.FeatStruct('[-p1,-p2,-pl,-xpl]')
#    print('FS', fs.__repr__())
    return morphology.FSSet(fs)

TUP2FEATS = (# 1 person
             {0: (('p1', False),), 1: (('p1', True),), '*': (('p1', False),)},
             # 2 person
             {0: (('p2', False),), 1: (('p2', True),), '*': (('p2', False),)},
             # number
             {0: (('pl', False),), 1: (('pl', True),), '*': (('pl', False),)}
              )

def inttup2feats(tup, obj=False):
    fs = morphology.FeatStruct()
    tup2feats = TUP2FEATS
    if obj:
        # Exclude plural for objects
        tup = tup[:2]
        tup2feats = TUP2FEATS[:2]
    for integ, dct in zip(tup, tup2feats):
        featvalues = dct[integ]
        for feat, value in featvalues:
            fs[feat] = value
    # Features not included in tuple
    for dct in tup2feats[len(tup):]:
        featvalues = dct.get('*')
        if featvalues:
            for feat, value in featvalues:
                fs[feat] = value
    if obj:
        # Object marking is not explicit for 3 person
        if not fs['p1'] and not fs['p2']:
            fs['expl'] = False
        else:
            fs['expl'] = True
    return fs

def get_tam(dct):
    # Only past, present, future so far
    tm = dct.get('tm')
    tm_int = tm[0] if tm else 0
    feat_val = TAM[tm_int]
    if feat_val == 'pres':
        return morphology.FeatStruct('[-cd,-ft,-im,-pp,-ps]')
    elif feat_val == 'past':
        return morphology.FeatStruct('[-cd,-ft,-im,-pp,+ps]')
    else:
        # Future
        return morphology.FeatStruct('[-cd,+ft,-im,-pp,-ps]')

def inttup2case(casetup):
    fs = morphology.FeatStruct('[-abl,-acc,-ben,-caus,-dstr,-gen,-ill,-ins,-intrc,-loc,-pos,-prol,-trm]')
    if casetup[0] == 2:
        fs['acc'] = True
    if casetup[3] == 1:
        fs['ins'] = True
    if casetup[2] == 1:
        fs['loc'] = True
    if casetup[2] == 2:
        fs['ben'] = True
    return fs

SEG = [['a', 'e', 'f', 'h', 'i', 'j', 'm', 'n',
        'ñ', 'o', 'r', 'u', 'w', 'y',
        # foreign consonants
        'b', 'd', 'g', 'v', 'x', 'z',
        # accented vowels
        'á', 'é', 'í', 'ó', 'ú',
        # capitalized
        'A', 'E', 'F', 'H', 'I', 'J', 'M', 'N',
        'Ñ', 'O', 'R', 'U', 'W', 'Y',
        'B', 'D', 'G', 'V', 'X', 'Z',
        # used in some compound words
        '-'],
       {'c': ['c', 'ch', 'chh', "ch'"],
        'k': ['k', 'kh', "k'"],
        'l': ['l', 'll'],
        'p': ['p', 'ph', "p'"],
        'q': ['q', 'qh', "q'"],
        's': ['s', 'sh'],
        't': ['t', 'th', "t'"],
        'C': ['C', 'Ch', 'Chh', "Ch'"],
        'K': ['K', 'Kh', "K'"],
        'L': ['L', 'Ll'],
        'P': ['P', 'Ph', "P'"],
        'Q': ['Q', 'Qh', "Q'"],
        'S': ['S', 'Sh'],
        'T': ['T', 'Th', "T'"]
        }]

QUECHUA = {'': language.Language('Quechua', 'qu', morph_processing=True,
                                 seg_units=SEG,
                                 labels={'qu-syn': ['sb', 'ob', 'adv',
                                                    # links FROM modifiers to noun
                                                    'det', 'adj', 'rel',
                                                    # del for 0 arguments?
                                                    'del',
                                                    'prp', 'mv', 'root']},
                                 extract=extract, dict2fs=dict2fs),
           'tiny': language.Language('Quechua', 'qu', morph_processing=True,
                                      seg_units=SEG,
                                      labels={'qu-id': ['sb', 'ob', 'perif', 'del', 'root'],
                                              'qu-lp': ['compf', 'del', 'root']},
                                      lexicon_name='tiny',
                                      extract=extract, dict2fs=dict2fs)
        }

for gram in QUECHUA.values():
    morph = morphology.Morphology(pos_morphs=['all'])
    gram.set_morphology(morph)
##    morph['v'].defaultFS = morphology.FeatStruct(
##'''[pos=v,tm=prf,as=smp,vc=smp,\
##sb=[-p1,-p2,-plr,-fem,-frm],ob=[-expl,-p1,-p2,-plr,-fem,-b,-l,-prp,-frm],\
##cj1=None,cj2=None,pp=None,ax=None,-neg,-rel,-sub,-def,-acc,-ye,\
##rl=[-acc,-p,-adv,-comp]]''')
##    morph['v'].FS_implic = {'rel': ['sub'], 'cj1': ['sub'], 'pp': ['rel', 'sub'],
##                            'def': ['rel', 'sub'],
##                            'l': ['prp'], 'b': ['prp'], 'ob': [['expl']]}
##    morph['v'].citationFS = morphology.FeatStruct(
##'''[pos=v,tm=prf,sb=[-p1,-p2,-plr,-fem],\
##ob=[-expl],cj1=None,cj2=None,pp=None,ax=None,-ye,\
##-neg,-rel,-sub,-def,-acc,rl=[-p,-acc,-adv,-comp]]''')
##
##    morph['n'].defaultFS = morphology.FeatStruct(
##'''[pos=n,-acc,-def,-neg,-itu,as=smp,\
##cnj=None,der=[-ass],-dis,-gen,\
##poss=[-expl,-p1,-p2,-plr,-fem,-frm],\
##-p1,-p2,-plr,-fem,-frm,\
##pp=None,v=None,vc=smp,\
##rl=[-acc,-p,-gen]]''')
##    morph['n'].FS_implic = {'poss': [['expl']]}
##    # defaultFS with voice and aspect unspecified
##    morph['n'].citationFS = morphology.FeatStruct(
##'''[-acc,-def,-neg,-fem,cnj=None,der=[-ass],\
##-dis,-gen,-plr,poss=[-expl],pp=None,v=inf,\
##rl=[-acc,-p,-gen]]''')
##    morph['cop'].defaultFS = morphology.FeatStruct(
##'''[cj2=None,-neg,ob=[-expl],-rel,\
##sb=[-fem,-p1,-p2,-plr,-frm],-sub,tm=prs]''')
