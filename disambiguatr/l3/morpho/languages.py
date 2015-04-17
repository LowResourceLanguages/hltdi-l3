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
"""

from .language import *
# import anal_gui
try:
    import psyco
    psyco.full()
except:
    pass

###
### Loading languages
###

LANGUAGES = {}

def get_lang_id(string):
    '''Get a language identifier from a string which may be the name
    of the language.'''
    lang = string if len(string) <= 3 else string.replace("'", "")[:2]
    return lang.lower()

def load_lang(lang, phon=False, segment=False, load_morph=True, verbose=True):
    """Load Morphology objects and FSTs for language with lang_id."""
    lang_id = get_lang_id(lang)
##    try:
    language = None
    if lang_id == 'am':
        from . import am_lang
        language = am_lang.AM
    elif lang_id == 'ki':
        from . import ki_lang
        language = ki_lang.KI
    elif lang_id == 'ti':
        from . import ti_lang
        language = ti_lang.TI
    elif lang_id == 'es':
        from . import es_lang
        language = es_lang.ES
    elif lang_id == 'ms':
        from . import ms_lang
        language = ms_lang.MS
    elif lang_id == 'qu':
        from . import qu_lang
        language = qu_lang.QU
    elif lang_id == 'om':
        from . import om_lang
        language = om_lang.OM
    elif lang_id == 'sil':
        from . import sil_lang
        language = sil_lang.SIL
    LANGUAGES[lang_id] = language
    if load_morph:
        return language.load_morpho(segment=segment, ortho=True, phon=phon,
                                    verbose=verbose)
##    except:
##        print 'Unable to load language', lang
    return True

def get_language(language, load=True, phon=False, segment=False, verbose=False):
    """Get the language with lang_id, attempting to load it if it's not found
    and load is True."""
    lang_id = get_lang_id(language)
    lang = LANGUAGES.get(lang_id, None)
    if not lang or (load and not lang.get_fsts(phon=phon, segment=segment)):
#    if not lang_id in LANGUAGES:
        if not load_lang(lang_id, phon=phon, segment=segment, load_morph=load, verbose=verbose):
            return False
    return LANGUAGES.get(lang_id, None)

def load_pos(language, pos, scratch=False):
    """Load FSTs for a single POS, overriding compiled FST if scratch is True."""
    language.morphology[pos].load_fst(scratch, recreate=True, verbose=True)
    
