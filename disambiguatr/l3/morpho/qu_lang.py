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

------------------------------------------------------
Author: Michael Gasser <gasser@cs.indiana.edu>

Create Language, Morphology, and POSMorphology objects for Quechua.
"""

from . import language

def v_get_citation(root, fs, guess=False):
    '''Return the canonical (prf, 3sm) form for the root and FeatStructs in FeatStruct set fss.
    '''
    # Return root if no citation is found
    result = root
    # Unfreeze the feature structure
    fs = fs.unfreeze()
    # Update the feature structure to incorporate default (with or without vc and as)
    fs.update(QU.morphology['v'].citationFS)
    # Refreeze the feature structure
    fs.freeze()
    # Find the first citation form compatible with the updated feature structure
    citation = QU.morphology['v'].gen(root, fs, from_dict=False,
                                      simplified=False, guess=guess)
    if citation:
        return citation[0][0]

def anal2string(anal):
    '''Convert a word analysis to a string.

    anal is ("all", root, citation (currently None), gramFS) except for pre-analyzed cases,
    where it's (pos, None, None, gramFS)
    '''
    root = anal[1]
    fs = anal[3]
    citation = anal[2]
    if root == None:
        # Word is pre-analyzed
        pos = anal[0]
    else:
        pos1 = fs.get('pos')
        pos2 = fs.get('pos2')
        if pos2 == 'inf':
            pos = 'infinitivo'
        elif pos2 == 'ger':
            pos = 'gerundio'
        elif pos2 == 'agt':
            pos = 'agentivo'
        elif pos2 == 'nft':
            pos = 'futuro nominal'
        elif pos2 == 'prt':
            pos = 'participio'
        elif pos2 == 'sub':
            pos = 'subordinativo'
        elif pos1 == 'n':
            pos = 'substantivo'
        elif pos1 == 'v':
            pos = 'verbo'
        elif pos1 == 'adj':
            pos = 'adjetivo'
    trans = fs.get('t')
    esp = trans.get('es') if trans else None
    POS = '?CG: ' if '?' in anal[0] else 'CG: '
    s = POS + pos
    if root:
        s += ', raíz: <' + root + '>'
    if citation:
        s += ', citación: ' + citation
    if esp:
        s += '\n Español: ' + esp
    s += '\n'
    if fs and root != None:
        # Complex features relevant to all POS
        sb = fs.get('sb')
        conj = fs.get('conj')
        prag = fs.get('prag')
        der = fs.get('der')
        # Verbs
        if pos1 == 'v':

            # Verb-specific complex features
            ob = fs.get('ob')
            asp = fs.get('asp')
            tam = fs.get('tam')

            # Subject, object agreement
            s += ' Subjeto:'
            s += arg2string(sb)
            if ob and ob.get('xpl'):
                s += ' Complemento directo:'
                s += arg2string(ob, True)

            ## Other grammatical features
            # TAM
            s += ' TAM:' + tam_string(tam, asp) + '\n'
            
            # Derivation
            derstring = der_string(der, True)
            if derstring:
                s += ' Derivación:' + derstring
                
            # Pragmatic (independent suffixes)
            pragstring = prag_string(prag)
            if pragstring:
                s += ' Pragmática:' + pragstring
                
            # Conjunctions
            conjstring = conj_string(conj)
            if conjstring:
                s += ' Conjunción:' + conjstring
                
            if conjstring or pragstring or derstring:
                s += '\n'
        else:
            # Nouns
            case = fs.get('cs')

            # Possessor (subject)
            if sb and sb.get('xpl') != False:
                s += ' Posesor:' + arg2string(sb)

            # Number
            if fs.get('pl'):
                s += ' Plural\n'

            # Case
            casestring = case_string(case)
            if casestring:
                s += ' Caso:' + casestring + '\n'

            # Derivation
            derstring = der_string(der, False)
            if derstring:
                s += ' Derivación:' + derstring

            # Pragmatic (independent suffixes)
            pragstring = prag_string(prag)
            if pragstring:
                s += ' Pragmática:' + pragstring
                
            # Conjunctions
            conjstring = conj_string(conj)
            if conjstring:
                s += ' Conjunción:' + conjstring
                
            if conjstring or pragstring or derstring:
                s += '\n'

    return s

def case_string(case):
    s = ''
    # Case 1
    if case.get('gen'):
        s += ' genitivo'
    elif case.get('intrc'):
        s += ' interactivo'
    elif case.get('pos'):
        s += ' posicional'
    elif case.get('prol'):
        s += ' prolativo'
    elif case.get('dstr'):
        s += ' distributivo'
    # Case 2
    if case.get('loc'):
        s += ' locativo'
    elif case.get('ben'):
        s += ' benefactivo'
    elif case.get('acc'):
        s += ' acusativo'
    elif case.get('ill'):
        s += ' ilativo'
    elif case.get('abl'):
        s += ' ablativo'
    elif case.get('caus'):
        s += ' causal'
    # Case 3
    if case.get('trm'):
        s += ' terminativo'
    elif case.get('ins'):
        s += ' instrumental'

    return s

def tam_string(tam, asp):
    s = ''
    if tam.get('ps'):
        s += ' pretérito'
    elif tam.get('cd'):
        s += ' condicional'
    elif tam.get('pp'):
        s += ' pluscuamperfecto'
    elif tam.get('im'):
        s += ' imperativo'
    # Both future and present are possible
    elif tam.get('ft'):
        s += ' futuro'
    # No explicit future feature
    elif tam.get('ft', 'missing'):
        s += ' presente/futuro'
    else:
        s += ' presente'

    if asp.get('prg'):
        s += ', progresivo'
    else:
        contin = asp.get('contin')
        if contin == 'y':
            s += ', continuativo'
        elif contin == 'n':
            s += ', discontinuativo'
    return s

def conj_string(conj):
    conjstring = ''
    if conj.get('add'):
        conjstring += ' aditivo'
    if conj.get('cop'):
        conjstring += ' copulativo'
    if conj.get('seq'):
        conjstring += ' secuencial'
    return conjstring

def der_string(der, verb=True):
    derstring = ''
    if der.get('lim'):
        derstring += ' limitativo'
    elif der.get('incl'):
        derstring += ' inclusivo'
    if verb:
        if der.get('caus'):
            derstring += ' causativo'
        elif der.get('cisloc'):
            derstring += ' cislocativo'
        elif der.get('cnsc'):
            derstring += ' consecutivo'
        elif der.get('des'):
            derstring += ' desiderativo'
        elif der.get('inch'):
            derstring += ' incoativo'
        elif der.get('rcp'):
            derstring += ' recíproco'
        elif der.get('rfl'):
            derstring += ' reflexivo'
        elif der.get('fct'):
            derstring += ' factitivo'
    else:
        if der.get('dim'):
            derstring += ' diminutivo'
        elif der.get('aug'):
            derstring += ' augmentativo'
    return derstring

def prag_string(prag):
    pragstring = ''
    if prag.get('dbt'):
        pragstring += ' dubitativo'
    if prag.get('emot'):
        pragstring += ' emotivo'
    if prag.get('emph'):
        pragstring += ' enfático'
    if prag.get('intj'):
        pragstring += ' interjectivo'
    if prag.get('nonassr'):
        pragstring += ' no asertivo'
    if prag.get('progn'):
        pragstring += ' pronosticativo'
    if prag.get('top'):
        pragstring += ' tópico'
    if prag.get('xplc'):
        pragstring += ' explicitativo'
    if prag.get('resp'):
        pragstring += ' responsivo'
    evid = prag.get('ev')
    if evid == 'vald':
        pragstring += ' validador'
    elif evid == 'rprt':
        pragstring += ' reportativo'
    return pragstring

def arg2string(fs, obj=False):
    '''Convert an argument Feature Structure to a string.'''
    s = ''
    plr = fs.get('pl')
    p1 = fs.get('p1')
    p2 = fs.get('p2')
    if p1:
        if p2:
            s += ' 1 plur incl'
        elif plr:
            s += ' 1 plur excl'
        else:
            s += ' 1 sing'
    elif p2:
        s += ' 2'
        if plr:
            s += ' plur'
        else:
            s += ' sing'
    elif not obj:
        s += ' 3'
        if plr:
            s += ' plur'
        else:
            s += ' sing'
    s += '\n'
    return s

## Create Language object for Quechua, including preprocessing, postprocessing,
## and segmentation units (phones).
QU = language.Language("quechua", 'Qu',
                       seg_units=[['a', 'e', 'f', 'h', 'i', 'j', 'm', 'n',
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
                                   }],
                       # Should be Quechua
                       msgs={'loading': 'Cargando datos morfológicos para',
                             'Word': 'Palabra',
                             'analyzing': 'Analizando palabras en',
                             'writing': 'Escribiendo análisis en'})

## Create Morphology object for verb POSMorphology object for Quechua,
## including punctuation and ASCII characters that are part of the romanization.
QU.set_morphology(language.Morphology((),
                                      pos_morphs=[('all', [], [], [])
#                                                  ('v', [], [], []),
#                                                  ('n', [], [], [])],
                                                    ],
                                      # Exclude - (because it can be used in compounds)
                                      punctuation=r'[“‘”’–—:;/,<>?.!%$()[\]{}|#@&*\_+=\"^]',
                                      # Include digits?
                                      characters=r'[a-zA-Zñáéíóú]'))

### Assign various attributes to Morphology and POSMorphology objects

# No analysis at all because there's something wrong (expand later)
QU.morphology.triv_anal = lambda form: None

# Function that converts (POS, root, citation, FS) to string
QU.morphology.anal2string = lambda anal: anal2string(anal)

## Set pre-analyzed words for each POS
# QU.morphology['v'].set_analyzed()
# QU.morphology['n'].set_analyzed()

## Morpheme labels
#QU.morphology['v'].morphs = ['DER', 'NOM', 'ASP', 'AGR1', 'TAM1','AGR2', 'AGR_tam', 'AGR3', 'TAM2', 'PERSP', 'CASE']

## Default feature structure for POSMorphology objects
## Used in generation and production of citation form
# 3ps present
QU.morphology['all'].defaultFS = \
    language.FeatStruct(
    "[pos=n,rpos=n,pos2=cn,-tr,-pl,tam=[-im,-cd,-pp,-ps,-ft]," \
    + "der=[-rfl,-rcp,-des,-cisloc,-caus,-cnsc,-inch,-fct,-lim,-pos,-dim,-aug,-incl]," \
    + "cs=[-gen,-intrc,-pos,-prol,-dstr,-loc,-ben,-acc,-ill,-abl,-caus,-trm,-ins]," \
    + "prag=[-top,-emph,-emot,-intj,-progn,-dbt,-nonassr,-xplc,-resp,ev=None]," \
    + "conj=[-add,-cop,-seq],asp=[contin=None,-prg]," \
    + "sb=[-p1,-p2,-pl,-xpl],ob=[-xpl,-p1,-p2,-pl]]")
QU.morphology['all'].FS_implic = {'ob': ['tr', ['xpl']],
                                  'sb': [['xpl']],
                                  ('pos', 'adj'): [['pos2', 'adj'], ['rpos', 'adj']],
                                  ('pos2', 'ger'): [['rpos', 'v']],
                                  ('pos2', 'nft'): [['rpos', 'v']],
                                  ('pos2', 'agt'): [['rpos', 'v']],
                                  ('pos2', 'prt'): [['rpos', 'v']],
                                  ('pos2', 'sub'): [['rpos', 'v']],
                                  ('pos2', 'inf'): [['rpos', 'v']],
                                  ('pos', 'v'): [['sb', ['xpl']], ['pos2', 'v'], ['rpos', 'v'], ['cs', None]]}
# defaultFS: infinitive
QU.morphology['all'].citationFS = \
    language.FeatStruct("[pos2=inf]")

## Functions that return the citation forms for words
# QU.morphology['v'].citation = lambda stem, fss, simplified, guess, ignore: v_get_citation(stem, fss, guess)

## Functions that convert analyses to strings
QU.morphology['all'].anal2string = lambda fss: anal2string(fss)

## All TAM forms of the root hayu- 'contradict'

PRES_INTRANS = ['hayuni', 'hayunki', 'hayun', 'hayuyku', 'hayunkichis', 'hayunku']
PRES_TRANS = ['hayuyki', 'hayuwanki', 'hayuwan', 'hayusunki', 'hayuykiku', 'hayuwankiku',
              'hayuwanku', 'hayusunkiku', 'hayuykichis', 'hayuwankichis', 'hayuwanchis', 'hayusunkichis']

PAST_INTRANS = ['hayurqani', 'hayurqanki', 'hayurqa', 'hayurqan', 'hayurqayku', 'hayurqanchis',
                'hayurqankichis', 'hayurqanku']
PAST_TRANS = ['hayurqayki', 'hayuwarqanki', 'hayuwarqan', 'hayuwarqa', 'hayurqasunki',
              'hayurqaykiku', 'hayuwarqankiku', 'hayuwarqanku', 'hayurqasunkiku',
              'hayurqaykichis', 'hayuwarqankichis', 'hayuwarqanchis', 'hayurqasunkichis']

FUT_INTRANS = ['hayusaq', 'hayunki', 'hayunqa', 'hayusaqku', 'hayusunchis', 'hayunkichis', 'hayunqaku']
FUT_TRANS = ['hayusayki', 'hayuwanki', 'hayuwanqa', 'hayusunki',
             'hayusaykiku', 'hayuwankiku', 'hayuwanqaku', 'hayusunkiku',
             'hayusaykichis', 'hayuwankichis', 'hayuwasunchis', 'hayusunkichis']

PP_INTRANS = ['hayusqani', 'hayusqanki', 'hayusqa', 'hayusqayku', 'hayusqanchis', 'hayusqankichis',
              'hayusqaku']
PP_TRANS = ['hayusqayki', 'hayuwasqanki', 'hayuwasqa', 'hayusqasunki',
            'hayusqaykiku', 'hayuwasqankiku', 'hayuwasqaku', 'hayusqasunkiku',
            'hayusqaykichis', 'hayuwasqankichis', 'hayuwasqanchis', 'hayusqasunkichis']

COND_INTRANS = ['hayuyman', 'hayuwaq', 'hayunman', 'hayuykuman', 'hayusunchisman', 'hayuswan',
                'hayuwaqchis', 'hayunkuman']
COND_TRANS = ['hayuykiman', 'hayuwankiman', 'hayuwanman', 'hayusunkiman',
              'hayuykikuman', 'hayuwankikuman', 'hayuwankuman', 'hayusunkikuman',
              'hayuykichisman', 'hayuwankichisman', 'hayuwaswan', 'hayuwasunchisman', 'hayusunkichisman']

IMP_INTRANS = ['hayuy', 'hayuychis', 'hayuchun', 'hayuchunku']
IMP_TRANS = ['hayuway', 'hayuwaychis', 'hayuwachun', 'hayuwachunku', 'hayuwayku']

def test(items):
    for item in items:
        print(item)
        anal = QU.morphology['all'].anal(item)
        for a in anal:
            for f in a[1]:
                print([('s', f.get('sb')), ('o', f.get('ob')), ('t', f.get('tam'))])

def load_all():
    QU.morphology['all'].load_fst(True, recreate=True, verbose=True)
