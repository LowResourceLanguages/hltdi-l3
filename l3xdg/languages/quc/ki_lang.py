"""
This file is part of Morpho.

    Morpho is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Morpho is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Morpho.  If not, see <http://www.gnu.org/licensQU/>.

------------------------------------------------------
Author: Michael Gasser <gasser@cs.indiana.edu>

Create Language, Morphology, and POSMorphology objects for K'iche'.
"""

from . import language

def v_get_citation(root, fs, guess=False):
    '''Return the canonical form for the root and language.FeatStructs in language.FeatStruct set fss (now just incpl 3s, 3s)
    '''
    # Return root if no citation is found
    result = root
    # Unfreeze the feature structure
    fs = fs.unfreeze()
    # Update the feature structure to incorporate default (with or without vc and as)
    fs.update(KI.morphology['v'].citationFS)
    # Refreeze the feature structure
    fs.freeze()
    # Find the first citation form compatible with the updated feature structure
    citation = KI.morphology['v'].gen(root, fs, from_dict=False, simplified=False, guess=guess)
    if citation:
        return citation[0][0]

def v_anal2string(anal):
    '''Convert a verb analysis to a string.

    anal is ("(*)v", root, citation, gramFS)
    '''
    pos = 'verbo'
    root = anal[1]
    citation = anal[2]
    fs = anal[3]
    esp = fs.get('es')
    POS = '?CL: ' if '?' in anal[0] else 'CL: '
    s = POS + pos
    if root:
        s += ', raíz: <' + root + '>'
    if esp:
        s += ', español: ' + esp
    if citation:
        s += ', citación: ' + citation
    s += '\n'
    if fs:
        abs = fs['ab']
        s += '  absolutivo:'
        s += arg2string(abs)
        erg = fs.get('er')
        if erg and erg.get('xpl'):
            s += '  ergativo:'
            s += arg2string(erg, True)
        s += '  otras propiedades:'
        tm = fs.get('tam')
        if tm.get('cmp'):
            s += ' completivo'
        elif tm.get('imv'):
            s += ' imperativo'
        elif tm.get('prh'):
            s += ' imperativo negativo'
        elif tm.get('prf'):
            s += ' perfectivo'
        elif tm.get('stv'):
            s += ' estativo'
        elif tm.get('fut'):
            s += ' futuro'
        else:
            s += ' incompletivo'
        der = fs.get('der')
        if der.get('aps'):
            s += ', antipasivo'
        elif der.get('pas'):
            s += ', pasivo'
        if der.get('frq'):
            s += ' frecuentativo'
        if der.get('imm'):
            s += ' inmediativo'

        if fs.get('cas'):
            s += ', causativo'

        if fs.get('pos'):
            s += ', posicional'

        mov = fs.get('mov')
        if mov and mov.get('xpl'):
            if mov.get('go'):
                s += ' movimiento: ir'
            else:
                s += ' movimiento: venir'

        s += '\n'
    return s

def arg2string(fs, erg=False):
    '''Convert an argument Feature Structure to a string.'''
    s = ''
    plr = fs.get('plr')
    p1 = fs.get('p1')
    p2 = fs.get('p2')
    fml = fs.get('fml')
    if p1:
        s += ' 1'
    elif p2:
        s += ' 2'
        if fml:
            s += ', frml'
    else:
        s += ' 3'
    if plr:
        s += ', plur'
    else:
        s += ', sing'
    s += '\n'
    return s

def agr_to_list(agr, cat):
    '''Category, then person, then number.'''
    gram = [cat]

    if agr.get('p1'):
        gram.append('1')
    elif agr.get('p2'):
        gram.append('2')
    else:
        gram.append('3')

    if agr.get('plr'):
        gram.append('plural')
    else:
        gram.append('singular')

    return gram

def fs_to_feats(root, fs):
    gram = {}
    gram[str('RAÍZ', 'utf-8')] = root

    sbj = fs['sbj']
    obj = fs['obj']
    der = fs.get('der')
    mod = fs.get('mod')
    tns = fs.get('tns')
    asp = fs.get('asp')
    neg = fs.get('neg')
    inter = fs.get('int')
    ass = fs.get('ass')

    # Agreement
    agr_to_feats(sbj, 'SBJ', gram, excl=True)
    agr_to_feats(obj, 'OBJ', gram, excl=True)

    # Tense
    if tns.get('fut'):
        gram['TAMfut'] = True
    elif tns.get('ps'):
        gram['TAMpas'] = True
    elif tns.get('pp'):
        gram['TAMpp'] = True
    else:
        gram['TAMpres'] = True

    if mod:
        if mod.get('sub'):
            gram['TAMsubj'] = True
        elif mod.get('imp'):
            gram['TAMimpv'] = True

    if asp:
        if asp.get('prg'):
            gram['TAMprog'] = True
        
    # DER
    if der:
        if der.get('rcp'):
            gram['DERrecip'] = True
        elif der.get('rfl'):
            gram['DERrefl'] = True

    if neg:
        gram['PERSPneg'] = True
    elif inter:
        gram['PERSPinter'] = True
    elif ass:
        gram['PERSPasrt'] = True

    return gram

def feats_to_fs(gram):
    fs = language.FeatStruct()

    fs['sbj'] = feats_to_agr(gram, 'SBJ')
    fs['obj'] = feats_to_agr(gram, 'OBJ')

    if gram.get('TAMpres'):
        fs['tns'] = language.FeatStruct('[-fut, -ps, -pp]')
    elif gram.get('TAMpas'):
        fs['tns'] = language.FeatStruct('[-fut, +ps, -pp]')
    elif gram.get('TAMfut'):
        fs['tns'] = language.FeatStruct('[+fut, -ps, -pp]')
    elif gram.get('TAMpp'):
        fs['tns'] = language.FeatStruct('[-fut, -ps, +pp]')

    if gram.get('TAMprog'):
        fs['asp'] = language.FeatStruct('[+prg]')
    else:
        fs['asp'] = language.FeatStruct('[-prg]')

    if gram.get('TAMsubj'):
        fs['mod'] = language.FeatStruct('[+sub,-imp]')
    elif gram.get('TAMimpv'):
        fs['mod'] = language.FeatStruct('[-sub,+imp]')
    else:
        fs['mod'] = language.FeatStruct('[-sub,-imp]')

    if gram.get('DERrefl'):
        fs['der'] = language.FeatStruct('[+rfl,-rcp]')
    elif gram.get('DERrecip'):
        fs['der'] = language.FeatStruct('[-rfl,+rcp]')

    if gram.get('PERSPneg'):
        fs['neg'] = True
    else:
        fs['neg'] = False
    if gram.get('PERSPinter'):
        fs['int'] = True
    else:
        fs['int'] = False
    if gram.get('PERSPasrt'):
        fs['ass'] = True
    else:
        fs['ass'] = False

    return FSSet(fs)

def v_anal_to_dict(root, fs):
    args = []
    # List of features that are true
    bools = []
    strings = {}

    gram = {}

    gram['root'] = root

    sbj = fs['sb']
    obj = fs.get('ob', None)
    vc = fs['vc']
    asp = fs['as']
    tm = fs['tm']

    # Arguments
    # The first item in args is a list of category labels
    labels = ['person', 'number']
    args.append(labels)
    # The second item in args is a list of argument category lists
    args1 = []
    args1.append(agr_to_list(sbj, 'subject'))
    if obj.get('expl'):
        args1.append(agr_to_list(obj, 'object'))
    args.append(args1)

    # TAM
    if tm == 'imf':
        strings['tense/mood'] = 'imperfective'
    elif tm == 'prf':
        strings['tense/mood'] = 'perfective'
    elif tm == 'ger':
        strings['tense/mood'] = 'gerundive'
    else:
        strings['tense/mood'] = 'jussive/imperative'

    # DERIVATIONAL STUFF
    if vc == 'ps':
        strings['voice'] = 'passive'
    elif vc == 'tr':
        strings['voice'] = 'transitive'

    if asp == 'it':
        strings['aspect'] = 'iterative'
    elif asp == 'rc':
        strings['aspect'] = 'reciprocal'

    gram['args'] = args
    gram['strings'] = strings
    gram['bools'] = bools

    return gram

def list_to_arg(dct, prefix):
    '''Person, number.'''
    arg = language.FeatStruct()
    person = dct.get(prefix + '_pers')
    number = dct.get(prefix + '_num')
    gender = dct.get(prefix + '_gen')
    arg['expl'] = True

    # Person
    if person == '1':
        arg['p1'] = True
        arg['p2'] = False
    elif person == '2':
        arg['p2'] = True
        arg['p1'] = False
    else:
        # 3rd person the default
        arg['p1'] = False
        arg['p2'] = False
    # Number
    if number == 'plur':
        arg['plr'] = True
    else:
        # Singular the default
        arg['plr'] = False

    return arg

def v_dict_to_anal(root, dct, freeze=True):
    fs = language.FeatStruct()
    root = root or dct['root']

    # Arguments
    sbj = list_to_arg(dct, 'sbj')
    if dct.get('obj'):
        obj = list_to_arg(dct, 'obj')
    else:
        obj = language.FeatStruct()
        obj['expl'] = False
    fs['sb'] = sbj
    fs['ob'] = obj
    
    # TAM: labels are the same as FS values
    fs['tm'] = dct.get('tam', 'prf')

    # DERIVATIONAL STUFF
    fs['as'] = dct.get('asp', 'smp')
    fs['vc'] = dct.get('voice_ti', 'smp')

    # OTHER GRAMMAR

    return [root, FSSet(fs)]

def anal_to_gram(anals, morph_cats):
    grams = []
    for anal in anals:
        root = anal[0]
        for fs in anal[1]:
            gram = {}
            gram['root'] = root
            fs_to_gram(fs, gram)
            grams.append((fs_to_morphs(root, fs, morph_cats),
                          gram))
    return grams

def fs_to_morphs(root, fs, morph_cats):
    """morph_cats a list of morph categories."""
    morphs = []
    for morph_cat in morph_cats:
        if morph_cat == 'root':
            morphs.append(root)
        else:
            morphs.append(fs.get(morph_cat))
    return morphs

def gram_to_fs(gram):
    fs = language.FeatStruct()

    erg = gram.get('erg')
    abs = gram['abs']
    trans = gram.get('trans')
    intr = gram.get('intr')
    mov = gram.get('mov')
    tam = gram['tam']
    asp2 = gram.get('asp2')
    
    fs['erg'] = gram_to_agr(erg, polite=True)
    fs['abs'] = gram_to_agr(abs, polite=True)

    if tam == 'cmpl':
        fs['tam'] = language.FeatStruct('[+cmp, -imp, -prf, -prh]')
    elif tam == 'incmpl':
        fs['tam'] = language.FeatStruct('[-cmp, -imp, -prf, -prh]')
    elif tam == 'impv':
        fs['tam'] = language.FeatStruct('[-cmp, +imp, -prf, -prh]')
    elif tam == 'perf':
        fs['tam'] = language.FeatStruct('[-cmp, -imp, +prf, -prh]')
    elif tam == 'impv neg':
        fs['tam'] = language.FeatStruct('[-cmp, -imp, -prf, +prh]')

    if not mov:
        fs['mov'] = language.FeatStruct('[-expl]')
    elif mov == 'ir':
        fs['mov'] = language.FeatStruct('[+expl,+go]')
    else:
        fs['mov'] = language.FeatStruct('[+expl,-go]')

    der_fs = language.FeatStruct('[-apas, -caus, -freq, -imm, -pas]')
    if intr:
        if intr == 'pass':
            der_fs['pas'] = True
        elif intr == 'antipass':
            der_fs['apas'] = True
    if trans:
        der_fs['caus'] = True
    if asp2:
        if asp2 == 'immed':
            der_fs['imm'] = True
        elif asp2 == 'freq':
            der_fs['freq'] = True
    fs['der'] = der_fs

    return fs

def fs_to_gram(fs, gram=None):
    gram = gram or {}

    erg = fs['erg']
    abs = fs['abs']
    der = fs['der']
    mov = fs['mov']
    tam = fs['tam']

    # Erg
    gram['erg'] = agr_to_gram(erg, polite=True)
    # Abs
    gram['abs'] = agr_to_gram(abs, polite=True)

    # TAM
    if tam['cmp']:
        gram['tam'] = 'cmpl'
    elif tam['prf']:
        gram['tam'] = 'perf'
    elif tam['prh']:
        gram['tam'] = 'impv neg'
    elif tam['imp']:
        gram['tam'] = 'impv'
    else:
        gram['tam'] = 'incmpl'

    # DER
    if der.get('pas'):
        gram['intr'] = 'pass'
    elif der.get('apas'):
        gram['intr'] = 'antipass'
    else:
        gram['intr'] = False

    if der.get('caus'):
        gram['trans'] = 'caus'
    else:
        gram['trans'] = False

    if der.get('freq'):
        gram['asp2'] = 'freq'
    elif der.get('imm'):
        gram['asp2'] = 'immed'

    # MOV
    if not mov['expl']:
        gram['mov'] = False
    elif mov['go']:
        gram['mov'] = 'ir'
    else:
        gram['mov'] = 'venir'

    return gram

## Create Language object for K'iche', including segmentation units (phones).
KI = language.Language("K'iche'", 'Ki',
                       seg_units=[['a', 'e', 'i', 'j', 'l', 'm', 'n', 'o', 'r',
                                   's', 'u', 'w', 'x', 'y', "'",
                                   # Also include long vowels?
                                   'ä', 'ë', 'ï', 'ö', 'ü',
                                   # Only in foreign words
                                   'd', 'f', 'g', 'h', 'v', 'z',
                                   # Morphophonological characters
                                   'B'],
                                  # b only in foreign words
                                  {'b': ['b', "b'"],
                                   'c': ['ch', "ch'"],
                                   'k': ['k', "k'"],
                                   'p': ['p', "p'"],
                                   'q': ['q', "q'"],
                                   't': ['t', "t'", 'tz', "tz'"]}],
                       # Should be K'iche'
                       msgs={'loading': 'Cargando datos morfológicos para',
                             'Word': 'Palabra'})

## Create Morphology object for verb POSMorphology objects for K'iche',
## including punctuation and ASCII characters that are part of the romanization.
KI.set_morphology(language.Morphology((),
                                      pos_morphs=[('v', [], [], [])],
                                      # Exclude - (because it can be used in compounds)
                                      punctuation=r'[“‘”’–—:;/,<>?.!%$()[\]{}|#@&*\_+=\"^]',
                                      # Include digits?
                                      characters=r'[a-zA-Zñáéíóúäëïöü]'))

### Assign various attributes to Morphology and POSMorphology objects

# Functions that simplify orthography
# KI.morphology.simplify = lambda word: simplify(word)
# KI.morphology.orthographize = lambda word: orthographize(word)

# Function that performs trivial analysis on forms that don't require romanization
KI.morphology.triv_anal = lambda form: no_convert(form)

## Set pre-analyzed words for each POS
# KI.morphology['v'].set_analyzed()
# KI.morphology['n'].set_analyzed()

## Morpheme labels
#KI.morphology['v'].morphs = ['TAM', 'ABS', 'MOV', 'ERG', 'DER1', 'DER2', 'CAT', 'FUT', 'FORM']

## Functions converting between feature structurQU and simple dicts
KI.morphology['v'].anal_to_dict = lambda stem, anal: v_anal_to_dict(stem, anal)
KI.morphology['v'].dict_to_anal = lambda stem, anal: v_dict_to_anal(stem, anal)

## Default feature structure for POSMorphology objects
## Used in generation and production of citation form
# 3,3 incompletive
KI.morphology['v'].defaultFS = \
    language.FeatStruct("[tam=[-imv,-prh,-prf,-cmp,-stv,-fut],"\
                            + "der=[-cas,-aps,-frq,-imm,-pas],pos=v,"\
                            + "mov=[-xpl],-trm,-pst,"\
                            + "ab=[-p1,-p2,-plr,-frm],er=[-p1,-p2,-plr,-frm,-xpl]]")
KI.morphology['v'].FS_implic = {'er': [['xpl']]}
# defaultFS: for now same as default
KI.morphology['v'].citationFS = \
    language.FeatStruct("[tam=[-imv,-prh,-prf,-cmp,-stv,-fut],"\
                            + "der=[-aps,-cas,-frq,-imm,-pas],-trm,-pst,pos=v,mov=[-xpl],"\
                            + "ab=[-p1,-p2,-plr,-frm],er=[-p1,-p2,-plr,-frm]]")

## Functions that return the citation forms for words
KI.morphology['v'].citation = lambda stem, fss, simplified, guess, ignore: v_get_citation(stem, fss, guess)

## Functions that convert analysQU to strings
KI.morphology['v'].anal2string = lambda fss: v_anal2string(fss)

## Test sets

INTR =      ["kinwarik", "katwarik", "kwarik", "kojwarik", "kixwarik", "kewarik", "kwar la", "kwar alaq"]
TRANS_DER = ["katinkunaj", "kinkunaj", "kixinkunaj", "ke'inkunaj", "kinkunaj la", "kinkunaj alaq",
             "kinakunaj", "kakunaj", "kojakunaj", "ke'akunaj",
             "kinukunaj", "katukunaj", "kukunaj", "kojukunaj", "kixukunaj", "ke'ukunaj",
             "katqakunaj", "kqakunaj", "kaqakunaj", "kixqakunaj", "keqakunaj", "kqakunaj la", "kqakunaj alaq",
             "kinikunaj", "kikunaj", "kojikunaj", "ke'ikunaj",
             "kinkikunaj", "katkikunaj", "kkikunaj", "kakikunaj", "kojkikunaj", "kixkikunaj", "kekikunaj",
             "kkunaj la", "kakunaj la", "kojkunaj la", "kekunaj la"]

def test(items):
    for item in items:
        print(item)
        anal = KI.morphology['v'].anal(item)
        for a in anal:
            for f in a[1]:
                print([('e', f.get('er')), ('a', f.get('ab')), ('t', f.get('tam'))])

def load_verbs():
    KI.morphology['v'].load_fst(True, recreate=True, verbose=True)
