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
    along with Morpho.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------
Author: Michael Gasser <gasser@cs.indiana.edu>

Create Language, Morphology, and POSMorphology objects for Spanish.

All functions specific to Spanish morphology are here.
"""

from . import language

### Various functions that will be values of attributes of Spanish Morphology
### and POSMorphology objects.

def vb_get_citation(root, fs, simplified=False, guess=False):
    '''Return the canonical (infinitive) form for the stem and language.FeatStructs in language.FeatStruct set fss.
    '''
    # Return root if no citation is found
    result = root
    # Unfreeze the feature structure
    fs = fs.unfreeze()
    # Update the feature structure to incorporate default (with or without vc and as)
    fs.update(ES.morphology['v'].defaultFS)
    # Refreeze the feature structure
    fs.freeze()
    # Find the first citation form compatible with the updated feature structure
    citation = ES.morphology['v'].gen(root, fs, from_dict=False,
                                       simplified=simplified, guess=guess)
    if citation:
        result = citation[0][0]
    else:
        # Verb may not occur in simplex form; try passive
        fs = fs.unfreeze()
        fs.update({'vc': 'ps'})
        fs.freeze()
        citation = ES.morphology['v'].gen(root, fs, from_dict=False,
                                           simplified=simplified, guess=guess)
        if citation:
            result = citation[0][0]
    return result

def vb_anal2string(anal):
    '''Convert a verb analysis to a string.

    anal is ((*)pos, stem, citation, gramFS)
    '''
    fs = anal[3]
    pos = fs.get('pos')
    if pos == 'n':
        pos_str = 'sustantivo'
    elif pos == 'v':
        pos_str = 'verbo'
    elif pos == 'adj':
        pos_str = 'adjetivo'
    elif pos == 'adv':
        pos_str = 'adverbio'
    stem = anal[1]
    citation = anal[2]
    POS = '?CG: ' if '?' in anal[0] else 'CG: '
    s = POS + pos_str
    if stem:
        s += ', raíz: <' + stem + '>'
    if citation:
        s += ', citación: ' + citation
    s += '\n'
    if fs:
        dob = fs.get('dob')
        iob = fs.get('iob')
        if pos == 'n' or pos == 'adv':
            if pos == 'n':
                s += ' infinitivo'
            else:
                s += ' gerundio'
            if dob and dob.get('xpl'):
                s += '; comp dir:'
                s += arg2string(dob, True)
            if iob and iob.get('xpl'):
                if dob and dob.get('xpl'):
                    s += ';'
                s += ' comp indir:'
                s += arg2string(iob, True)
            if fs.get('refl'):
                s += '; reflexivo'
        elif pos == 'adj':
            s += ' participio'
            ref = fs.get('ref')
            if ref and ref.get('xpl'):
                s += '; referente:'
                if ref.get('fem'):
                    s += ' femenino'
                else:
                    s += ' masculino'
                if ref.get('pl'):
                    s += ', plural'
                else:
                    s += ', singular'
        else:
            # Verb
            tm = fs['tam']
            asp = fs.get('as')
            if tm.get('cnd'):
                s += ' condicional'
            elif tm.get('fut'):
                s += ' futuro'
            elif tm.get('imv'):
                s += ' imperativo'
            elif tm.get('sub'):
                if tm.get('prt'):
                    s += ' subjuntivo imperfecto'
                else:
                    s += ' subjuntivo presente'
            elif tm.get('prt'):
                s += ' pretérito'
            elif tm.get('ipf'):
                s += ' imperfecto'
            elif tm.get('tns') and (not asp or (not asp.get('cnt') and not asp.get('prf'))):
                s += ' presente'
            asp_assigned = False
            if asp:
                if asp.get('cnt'):
                    s += ' gerundio: progresivo'
                    asp_assigned = True
                if asp.get('prf'):
                    s += ' participio: perfectivo'
                    asp_assigned = True
            sb = fs.get('sb')
            if sb and not asp_assigned:
                s += '; subjeto:'
                s += arg2string(sb)
            dob = fs.get('dob')
            if dob and dob.get('xpl'):
                s += '; comp dir:'
                s += arg2string(dob, True)
            iob = fs.get('iob')
            if iob and iob.get('xpl'):
                s += '; comp indir:'
                s += arg2string(iob, True)
            if fs.get('refl'):
                s += '; reflexivo'
        s += '\n'
    return s

def arg2string(fs, ob=False):
    '''Convert an argument Feature Structure to a string.'''
    s = ''
    if fs.get('p2'):
        s += ' 2'
        if fs.get('fam'):
            s += ', fam'
        else:
            s += ', frml'
    elif fs.get('p1'):
        s += ' 1'
    # Can be both 1st and 3rd person
    elif fs.get('p1', 'missing'):
        s += ' 1/3'
    else:
        s += ' 3'
    if fs.get('pl'):
        s += ', plur'
    else:
        s += ', sing'
    if ob and fs.get('fem'):
        if fs.get('fem'):
            s += ', fem'
        else:
            s += ', masc'
    return s

def vb_anal_to_dict(stem, fs):
    '''Convert a verb analysis Feature Structure to a dict.'''
    args = []
    # List of features that are true
    bools = []
    strings = {}

    gram = {}

    gram['stem'] = stem

    sb = fs['sb']
    ob = fs.get('ob', None)
    vc = fs['vc']
    asp = fs['as']
    tm = fs['tm']
    cj1 = fs.get('cj1', None)
    cj2 = fs.get('cj2', None)
    prp = fs.get('pp', None)

    # Subject and object
    prep = False
    formal = False
    labels = ['person', 'number', 'gender']
    if ob.get('xpl'):
        if ob.get('p2'):
            formal = True
            labels.append('formality')
        prep = True
        labels.append('prepositional')
    args.append(labels)
    args1 = []
    args1.append(agr_to_list(sb, 'subject', formal))
    if ob.get('xpl'):
        args1.append(agr_to_list(ob, 'object', formal))
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
    elif vc == 'cs':
        strings['voice'] = 'causative'

    if asp == 'it':
        strings['aspect'] = 'iterative'
    elif asp == 'rc':
        strings['aspect'] = 'reciprocal'

    # NEGATION
    if fs.get('neg'):
        bools.append('negative')
    # RELATIVIZATION
    if fs.get('rel'):
        bools.append('relative')
    # CASE
    if fs.get('acc'):
        bools.append('accusative')
    # CONJUNCTIONS AND PREPOSITIONS
    if cj1:
        strings['prefix conjunction'] = cj1
    if cj2:
        strings['suffix conjunction'] = cj2
    if prp:
        strings['preposition'] = prp

    gram['args'] = args
    gram['strings'] = strings
    gram['bools'] = bools

    return gram

def vb_dict_to_anal(stem, dct, freeze=True):
    '''Convert a verb analysis dict to a Feature Structure.'''
    fs = language.FeatStruct()
    stem = stem or dct['stem']

    # Arguments
    sb = list_to_arg(dct, 'sb')
    if dct.get('ob'):
        ob = list_to_arg(dct, 'ob')
    else:
        ob = language.FeatStruct()
        ob['xpl'] = False
    fs['sb'] = sb
    fs['ob'] = ob
    
    # TAM: labels are the same as FS values
    fs['tm'] = dct.get('tam', 'prf')

    # DERIVATIONAL STUFF
    fs['as'] = dct.get('asp', 'smp')
    fs['vc'] = dct.get('voice_am', 'smp')

    # OTHER GRAMMAR
    fs['neg'] = dct.get('neg', False)
    fs['rel'] = dct.get('rel', False)
    fs['acc'] = dct.get('acc', False)
    if dct.get('aux'):
        fs['aux'] = 'al'
    else:
        fs['aux'] = None

    # PREPOSITIONS and CONJUNCTIONS
    fs['pp'] = dct.get('prep_am')
    if fs['pp']:
        fs['sub'] = True

    fs['cj1'] = dct.get('preconj_am')
    if fs['cj1']:
        fs['sub'] = True

    fs['cj2'] = dct.get('sufconj_am')

    return [stem, FSSet(fs)]

def agr_to_list(agr, cat, formal=False):
    '''Convert an agreement Feature Structure to a list.

    Category, then person, number, gender, formality (2nd prs), prepositional.
    '''
    gram = [cat]

    if agr.get('p1'):
        gram.append('1')
    elif agr.get('p2'):
        gram.append('2')
    else:
        gram.append('3')

    if agr.get('pl'):
        gram.append('plural')
    else:
        gram.append('singular')

    if not agr.get('p1') and not agr.get('pl'):
        # Gender only for 2nd and 3rd person singular
        if agr.get('fem'):
            gram.append('feminine')
        else:
            gram.append('masculine')
    else:
        gram.append('')

    if formal:
        if cat == 'object' and agr.get('p2'):
            if agr.get('frm'):
                gram.append('formal')
            else:
                gram.append('informal')

    if agr.get('prp'):
        if agr.get('b'):
            gram.append('b-')
        else:
            gram.append('l-')
    elif cat == 'object':
        gram.append('no')

    return gram

def list_to_arg(dct, prefix):
    '''Convert a dict to an argument Feature Structure.'''
    arg = language.FeatStruct()
    person = dct.get(prefix + '_pers')
    number = dct.get(prefix + '_num')
    gender = dct.get(prefix + '_gen')
    arg['xpl'] = True

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
        arg['pl'] = True
    else:
        # Singular the default
        arg['pl'] = False
    # Gender
    if person != '1':
        if gender == 'fem':
            arg['fem'] = True
        else:
            arg['fem'] = False

    # 2nd person: formality
    if person == '2':
        formality = dct.get(prefix + '_form')
        if formality == 'form':
            arg['frm'] = True
        else:
            # Informal the default
            arg['frm'] = False

    # Prepositional (object only)
    if prefix == 'ob':
        prep = dct.get(prefix + '_prep_am')
        if prep == 'l':
            arg['prp'] = 'l'
        elif prep == 'b':
            arg['prp'] = 'b'
        else:
            arg['prp'] = None

    return arg

## Create Language object for Spanish, including segmentation units (graphemes).
ES = language.Language("español", 'Es',
                       citation_separate=False,
                       seg_units=[['a', 'b', 'd', 'e', 'f', 'g', 'h', 'i', 'j',
                                   'm', 'n', 'ñ', 'o', 'p', 's', 't', 'u', 'v',
                                   'x', 'y', 'z', 'á', 'é', 'í', 'ó', 'ú', 'ü',
                                   # foreign words
                                   'k', 'w',
                                   # morphophonemic characters
                                   'E', 'O', 'I', 'U', '!',
                                   'C', 'K', 'J', 'Z', 'G', "'", "`", '_'
                                   ],
                                  {'c': ['c', 'ch'],
                                   'l': ['l', 'll'],
                                   'q': ['qu'],
                                   'r': ['r', 'rr']}],
                       msgs={'loading': 'Cargando datos morfológicos para',
                             'Word': 'Palabra',
                             'analyzing': 'Analizando palabras en',
                             'writing': 'Escribiendo análisis en'})

## Create Morphology object and noun, verb, and copula POSMorphology objects for Spanish,
## including punctuation and ASCII characters that are part of the romanization.
ES.set_morphology(language.Morphology((),
                                      pos_morphs=[('v', [], [], [])],
                                      # Exclude - (because it can be used in compounds)
                                      punctuation=r'[“‘”’–—:;/,<>?.!%$()[\]{}|#@&*\_+=\"^]',
                                      # Include digits?
                                      characters=r'[a-zA-Zñáéíóúü]'))

### Assign various attributes to Morphology and POSMorphology objects

# Functions that simplifies Spanish orthography
ES.morphology.simplify = lambda word: simplify(word)
ES.morphology.orthographize = lambda word: orthographize(word)

# No analysis at all because there's something wrong (expand later)
ES.morphology.triv_anal = lambda form: None

## Set pre-analyzed words for each POS
# ES.morphology['v'].set_analyzed()
# ES.morphology['n'].set_analyzed()

## Otherwise only words with pos=v will be included in FST
ES.morphology['v'].wc = None

## Functions converting between feature structures and simple dicts
ES.morphology['v'].anal_to_dict = lambda stem, anal: vb_anal_to_dict(stem, anal)
ES.morphology['v'].dict_to_anal = lambda stem, anal: vb_dict_to_anal(stem, anal)

## Default feature structure for POSMorphology objects
## Used in generation and production of citation form
# 3ps present
ES.morphology['v'].defaultFS = \
    language.FeatStruct("[pos=v,tam=[-fut,-prt,-sub,-ipf,-cnd,-imv,+tns],as=[-cnt,-prf]," \
                        + "sb=[-p1,-p2,-pl],-refl,dob=[-xpl,-p1,-p2,-pl,-fem,-fam]," \
                        + "iob=[-xpl,-p1,-p2,-pl,-fem,-fam]," \
                        + "ref=[-xpl,-p1,-p2,-pl,-fem,-fam]]")
ES.morphology['v'].FS_implic = {'dob': [['xpl']], 'iob': [['xpl']],
                                'cnd': ['fut'],
                                ('pos', 'adv'): [['tam', ('tns',)]],
                                ('pos', 'adj'): [['ref', ['xpl']], ['tam', ('tns',)]],
                                ('pos', 'n'): [['tam', ('tns',)]]}

# defaultFS: infinitive
ES.morphology['v'].citationFS = \
    language.FeatStruct("[pos=n,tam=[-fut,-prt,-sub,-ipf,-cnd,-imv,-tns],as=[-cnt,-prf]," \
                        + "sb=[-p1,-p2,-pl],-refl,dob=[-xpl,-p1,-p2,-pl,-fem,+fam]," \
                        + "iob=[-xpl,-p1,-p2,-pl,-fem,+fam]]")

## Functions that return the citation forms for words
ES.morphology['v'].citation = lambda stem, fss, simplified, guess, ignore: vb_get_citation(stem, fss, simplified, guess)

## Functions that convert analyses to strings
ES.morphology['v'].anal2string = lambda fss: vb_anal2string(fss)
