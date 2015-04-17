# Cross-lingual links: join instances of Lex in different "languages"
# (Semantics is a language)
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010, 2011, 2012, 2013, 2014
#   The HLTDI L^3 Team, <gasser@cs.indiana.edu>
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
# 2010.10.30 (MG)
# -- Created.
# 2011.03.02
# -- Completely changed. Now simply pointers between Lexs, unidirectional
#    or bidirectional.
# 2011.05.15
# -- Empty crosslexes for crosslexes that create empty nodes (empty in source,
#    explicit in target).
# 2011.12.06
# -- RevEmptyCrosslexes
# 2012.02.25
# -- RevEmptyCrosslexes extended to allow relation attribute ('mother', 
#    'daughter')
# 2013.08.05
# -- EmptyCrosslexes have empty_cond attribute to condition creation of
#    empty nodes on the value of a particular agreement feature.
#
#########################################################################

# import os

class Crosslex:

    ID = 0
    
    def __init__(self, source_lex,
                 targ_lang_abbrev=None,
                 targ_lex_key='',
                 targ_lex_index=0,
                 targ_lex=None,
                 lexdim=None,
                 targdim=None,
                 bidir=False,
                 id=0,
                 count=1,
                 add=True,
                 empty=False, reverse=False):
        self.source_lex = source_lex
        self.source_lang = source_lex.language
        self.targ_lang_abbrev = targ_lang_abbrev
        self.targ_lex_key = targ_lex_key
        self.targ_lex_index = targ_lex_index
        # Interface lex dimension between the languages
        self.lexdim = lexdim
        # An arc lex dimension within the target language
        self.targdim = targdim
        self.bidir = bidir
        # Number of times this crosslex has occurred; used to 
        # estimate probabilities for disambiguation
        self.count = count
        # Normally set at finalization
        self.targ_lex = targ_lex
        # Set later too
        self.targ_lang = None
        if id:
            self.id = id
        else:
            self.id = Crosslex.ID
            Crosslex.ID += 1
        # Whether this an empty crosslex
        self.empty = empty
        # Whether this is a reverse crosslex
        self.reverse = reverse
        if add:
            self.add()

    def clone(self, source=None, copy_targ=True):
        """Make a copy of the crosslex. If copy_targ is False, the target lex is
        replaced with None so that it can be filled in during finalization.
        Used in lexicon flattening and during lexicalization in parsing and translation."""
#        cloneID = Crosslex.cloneID
#        Crosslex.cloneID += 1
        source = source or self.source_lex
        copied = Crosslex(source,
                          targ_lang_abbrev=self.targ_lang_abbrev,
                          targ_lex_key=self.targ_lex_key,
                          targ_lex_index=self.targ_lex_index,
                          targ_lex=self.targ_lex if copy_targ else None,
                          # Copy the lexdim??
                          lexdim=self.lexdim,
                          targdim=self.targdim,
                          bidir=self.bidir,
                          # Copy this??
                          count=self.count,
                          id=self.id, add=False)
        copied.targ_lang = self.targ_lang
#        print('Cloning', self, 'targ_lang', copied.targ_lang)
        return copied
    
    def add(self):
        crosslexes = self.source_lex.get_crosslexes(self.targ_lang_abbrev)
        crosslexes.append(self)

    def get_targ_lang(self):
        if self.targ_lex:
            self.targ_lang = self.targ_lex.language
        return self.targ_lang

    def either_lang_is(self, language):
        return language in [self.source_lang, self.get_targ_lang()]

    def is_semantic(self):
        """Is either end of the crosslex Semantics?"""
        return self.targ_lang_abbrev == 'sem' or self.source_lang.abbrev == 'sem'

    def __repr__(self):
        string = '{}:{}_{}{}{}:{}'
        src = self.source_lex
        trg = self.targ_lex
        return string.format(self.source_lang.abbrev,
                             self.id,
                             src.label or src.get_name(),
                             '<->' if self.bidir else '->',
                             self.targ_lang_abbrev,
                             (trg.label or trg.get_name()) if trg \
                                 else self.targ_lex_key)

    def merge(self, class_xlex, source):
        """Merge attributes from class_xlex into this crosslex, with source lex source."""
#        print('Merging {} into {} xlex {}'.format(class_xlex, source, self))
        dim = class_xlex.lexdim
        if dim:
            selflexdim = self.lexdim
            if selflexdim:
#                print('  Merging class lexdim {} with original lexdim {}'.format(dim, selflexdim))
                selflexdim.merge_attribs(dim)
            else:
#                print('  Cloning and adding class lexdim {}'.format(dim))
                cloned_lexdim = dim.clone(lex=source)
                self.lexdim = cloned_lexdim
        else:
            print('{} has no lexdim'.format(class_xlex))
    
    def same(self, xlex):
        """Is one or the other crosslex a clone of the other?"""
        return self.id == xlex.id

    def equiv(self, xlex):
        """Only really needed for RevEmptyCrosslex"""
        return self.same(xlex)

    @staticmethod
    def unique(xlexes):
        xlex_copy = xlexes[:]
        for i1, x1 in enumerate(xlex_copy[:-1]):
            for x2 in xlex_copy[i1+1:]:
                if x2 in xlexes:
                    if x1.same(x2):
                        xlexes.remove(x2)
        return xlexes

class EmptyCrosslex(Crosslex):
    '''Crosslex for an empty node in the source language with an explicit
    lex in the target language, for example,
    GN->ES/SEM prepositions/peripheral roles corresponding to Gn suffix postpositions.
    Created via a "trigger" lexical entry, which is separate from the
    source lex ("empty lex"), which is always something like ZERO.
    Specifies the relationship between target lex (inserted lex in the target language)
    and the trigger node in the target language.
    '''

    def __init__(self,
                 trigger_lex,
                 empty_lex_key='', empty_lex_index=0,
                 targ_lang_abbrev=None, targ_lex_key='', targ_lex_index=0, targ_lex=None,
                 lexdim=None, targdim=None, if_dim='',
                 # Added 2013.08.05; condition for creating empty node
                 empty_cond=None,
                 agrs=None, rel=None,
                 id=0, count=1, add=True):
        Crosslex.__init__(self,
                          trigger_lex,
                          targ_lang_abbrev=targ_lang_abbrev,
                          targ_lex_key=targ_lex_key,
                          targ_lex_index=targ_lex_index,
                          targ_lex=targ_lex,
                          lexdim=lexdim, targdim=targdim,
                          bidir=False,
                          id=id,
                          count=count, add=add, empty=True, reverse=False)
        self.empty_lex_key = empty_lex_key
        self.empty_lex_index = empty_lex_index
        self.empty_lex = None
#        print('Creating empty cross lex with empty key {}'.format(empty_lex_key))
        # If there's an agrs attribute, the value needs to be converted to a set of tuples
        if agrs:
            # First element is the dimension name
            # Second element: a dictionary of feature-value pairs
            for feat, val in agrs[1].items():
                # val is a list; convert to set of tuples
                agrs[1][feat] = {tuple(val)}
        self.agrs = agrs or []
        self.rel = rel or ['mother', None, None]
        self.if_dim = if_dim or rel[1]
        if empty_cond:
            feat, value = empty_cond
            if isinstance(value, int):
                value = (value,)
            else:
                value = tuple(value)
            self.empty_cond = (feat, value)
        else:
            self.empty_cond = None
#        print("Empty crosslex {}, ifdim {}".format(self, self.if_dim))

    def clone(self):
        """Make a copy of the crosslex that replaces the target lex with None
        so that it can be filled in during finalization. Used in lexicon
        flattening."""
#        cloneID = Crosslex.ID
#        Crosslex.ID += 1
#        print('Cloning {}'.format(self))
        copied = EmptyCrosslex(self.source_lex,
                               targ_lang_abbrev=self.targ_lang_abbrev,
                               targ_lex_key=self.targ_lex_key,
                               targ_lex_index=self.targ_lex_index,
                               targ_lex=self.targ_lex,
                               # Copy the lexdim??
                               lexdim=self.lexdim,
                               # Copy this??
                               targdim=None,
                               empty_lex_key=self.empty_lex_key,
                               empty_lex_index=self.empty_lex_index,
                               agrs=self.agrs,
                               rel=self.rel,
                               id=self.id,
                               # a tuple
                               empty_cond=self.empty_cond,
                               # Copy this??
                               count=self.count, add=False)
        copied.targ_lang = self.targ_lang
        copied.empty_lex = self.empty_lex
        return copied
    
    def __repr__(self):
        string = '{}:{}[{}:{}]->{}:{}[{}]'
        emp = self.empty_lex
        src = self.source_lex
        #        trg = self.targ_lex
        return string.format(self.source_lang.abbrev,
                             (emp.label or emp.get_name()) if emp else '??',
                             self.source_lang.abbrev,
                             src.label or src.get_name(),
                             self.targ_lang_abbrev,
                             self.targ_lex_key,
                             #                             (trg.label or trg.get_name()) if trg \
                             #                                 else self.targ_lex_key,
                             self.id)

    def equiv(self, xlex):
        """Are the two crosslexes effectively the same; that is, do they have the same
        insert_lex and the same empty_lex (targ_lex), but possibly different trigger lexes?"""
        if xlex.id != self.id:
            return False
        return self.targ_lex == xlex.targ_lex and self.empty_lex == xlex.empty_lex
#        emp, ins = self.targ_lex, self.insert_lex
#        emp2, ins2 = xlex.targ_lex, xlex.insert_lex
#        return emp and ins and emp2 and ins2 and (emp == emp2) and (ins == ins2)
#        return self == xlex

class RevEmptyCrosslex(Crosslex):
    '''Crosslex for an empty node on dim1 which is a daughter or a mother of the
    "trigger node" on dim2. Lexical (or grammatical entries) for both
    dimensions (empty_lex, insert_lex) are specified, as well as the
    label for the trigger->insert arc on dim2.
    THESE CAN PROBABLY GO AWAY SINCE THERE WILL BE NO MORE AUTOMATICALLY GENERATED
    REVERSE CROSSLEXES.
    '''

    def __init__(self,
                 trigger_lex, empty_lang_abbrev=None,
                 empty_lex_key='', empty_lex_index=0, empty_lex=None,
                 insert_lex_key='', insert_lex_index=0, insert_lex=None,
                 if_dim='', targdim=None, arc_label='',
                 rel=None, id=0, count=1, add=True):
        Crosslex.__init__(self, trigger_lex,
                          targ_lang_abbrev=empty_lang_abbrev,
                          targ_lex_key=empty_lex_key,
                          targ_lex_index=empty_lex_index,
                          targ_lex=empty_lex, lexdim=None,
                          targdim=targdim, bidir=False,
                          id=id,
                          count=count, add=add, empty=True, reverse=True)
        self.insert_lex_key = insert_lex_key
        self.insert_lex_index = insert_lex_index
        self.insert_lex = insert_lex
        self.if_dim = if_dim
        self.arc_label = arc_label
        self.rel = rel or ['daughter']
        self.empty_cond = None

    def clone(self):
        """Make a copy of the crosslex that replaces the target lex with None
        so that it can be filled in during finalization. Used in lexicon
        flattening."""
#        cloneID = Crosslex.cloneID
#        Crosslex.cloneID += 1
        copied = RevEmptyCrosslex(self.source_lex,
                                  empty_lang_abbrev=self.targ_lang_abbrev,
                                  empty_lex_key=self.targ_lex_key,
                                  empty_lex_index=self.targ_lex_index,
                                  empty_lex=self.targ_lex,
                                  insert_lex_key=self.insert_lex_key,
                                  insert_lex_index=self.insert_lex_index,
                                  insert_lex=self.insert_lex,
                                  # Copy or set to None
                                  if_dim=self.if_dim,
                                  arc_label=self.arc_label,
                                  rel=self.rel,
                                  # Copy this??
                                  targdim=None,
                                  id=self.id,
                                  # Copy this??
                                  count=self.count,
                                  add=False)
        copied.targ_lang = self.targ_lang
#        print('Cloning', self, 'targ_lang', copied.targ_lang)
        return copied
    
    def __repr__(self):
        string = '{}:{}({}:{})<-{}:{}[{}]'
        emp = self.targ_lex
        trig = self.source_lex
        ins = self.insert_lex
        ins_name = ins[0].name if ins else ''
        return string.format(self.source_lang.abbrev, ins_name,
                             trig.label or trig.get_name(),
                             self.arc_label, self.targ_lang_abbrev,
                             (emp.label or emp.get_name()) if emp else self.targ_lex_key,
                             self.id)

    def equiv(self, xlex):
        """Are the two crosslexes effectively the same; that is, do they have the insert_lex
        and the same empty_lex (targ_lex), but possibly different trigger lexes?"""
        emp, ins = self.targ_lex, self.insert_lex
        emp2, ins2 = xlex.targ_lex, xlex.insert_lex
        return emp and ins and emp2 and ins2 and (emp == emp2) and (ins == ins2)

