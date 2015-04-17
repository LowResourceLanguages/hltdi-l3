#   Implementation of Extensible Dependency Grammar, as described in
#   Debusmann, R. (2007). Extensible Dependency Grammar: A modular
#   grammar formalism based on multigraph description. PhD Dissertation:
#   Universität des Saarlandes.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010, 2011, 2012, 2013, 2014
#   by the HLTDI L^3 Team <gasser@cs.indiana.edu>
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
# 2010.07.29 (MG)
#
# 2010.08.13 (MG)
# -- Agrs and agree features modified.
# 2010.08.15 (MG)
# -- Language keeps track of agreements features as
#    lexical entries are added: agrs features and values
#    and label/daughter feature combinations
# 2010.08.20 (MG)
# -- Reintroduced YAML representations and pickling.
#    Agreement feature values are not FeatStructs as before,
#    simplifying several things.
# 2010.08.21 (MG)
# -- Lexical attributes changed to 'attribs' dict within
#    LexDim.
# 2010.08.23 (MG)
# -- Language in separate module.
# 2010.08.29 (MG)
# -- Added Group class and Lex method incorporating attributes
#    from groups in participating lexical entries. Groups
#    do not normally create new lexical entries for words
#    they contain.
# 2010.09.05 (MG)
# -- Groups now *do* create new lexical entries for each of their
#    as in Debusmann's groups. (It seemed impossible to implement
#    groups otherwise.)
# 2010.09.11 (MG)
# -- inherit_properties brought over from older XDG (differences
#    include sets instead of lists, list of ints instead of
#    feature structures.
# 2010.09.13 (MG)
# -- Finished inheritance, more or less.
# 2010.10.10 (MG)
# -- I broke pickling of lexicons. It's trying to pickle some function
#    (method?), resulting in
#    _pickle.PicklingError: Can't pickle <class 'function'>: attribute lookup builtins.function failed
# -- Fixed it. But it requires replacing all of the lambda functions that are values
#    of attributes in Language, Morphology, and POS_Morphology including preprocess and postprocess,
#    which are still needed for Amharic
# 2010.10.17 (MG)
# -- Added method (incorp_analyses) for incorporating morphological analyses into clone of lex
# 2010.10.23 (MG)
# -- Fixed inheritance so it works with sets of tuples.
# -- Lexicon.lexicalize() looks up only words (not lexemes) by default.
# -- Lexdim abbreviations changed to lg-dim in lexicon, except for semantic dimensions
# 2010.10.24 (MG)
# -- Unification methods are functions.
# 2010.10.31
# -- Added root and pos to Lex attribs. During inheritance they are copied to the names dict
#    attribute under language (in Lex.inherit_properties()).
# 2010.11.13
# -- Fixed bug in unify_fs (affecting unification of tuples of different lengths)
# 2010.11.16
# -- Fixed valency inheritance so 0, ! have precedence over +, ?, *
# 2010.12.12
# -- In LexDim, record_agrs also records features/values in 'govern' attribute.
# 2011.01.31
# -- Lexes have a crosslexes attrib: a dict association target language abbreviations
#    with [target_entry, LexDim] pairs (LexDim optional).
#    "target_entry" is (target_entry_label, target_entry_index) when lexicon is initialized,
#    converted to entry object in Language.finalize_crosslexes()
# 2011.02.01
# -- New crosslexes work in inheritance by creating a clone of the target entry
#    with the cross-lingual LexDim added to it (when there is a LexDim; when there
#    isn't, no clone is necessary).
# 2011.02.06
# -- Fixed inherit so it doesn't get stuck in loops. Target languages can't inherit
#    back to semantics.
# 2011.02.10
# -- Empty nodes incorporated in inheritance and Lex.from_dict().
# 2011.02.13
# -- New pattern functions check whether one feature tuple is a generalization of
#    another and remove specializations from sets of feature tuples. This is used
#    in language.py to simplify the list of possible agr features (and prevent
#    spurious analyses with features that have values of (0,0) vs. (0,0,0), say).
# 2011.02.22
# -- Fix crosslexes so that an entry can have more than one. In an entry, the YAML
#    now looks like this:
#    cross:
#      sem:
#        - lex: ...
#          dim: ...
#        - lex: ...
#      om:
#        lex: ...
# 2011.02.26
# -- Empty lexical entries (like @SB) now record this (based on the '@' in the name).
# 2011.03.09
# -- Cloned lexes were inheriting multiple times from the same class; fixed this (checking
#    ids and languages of inherited classes).
# -- Lex names attribute (including word, lexeme, gram labels) is now copied (a deepcopy)
#    when Lex is cloned. This fixes the output form of some words in the target language.
# 2011.03.11
# -- New way to represent subclass partitions of classes in YAML files, read in with
#    Lex.partition_from_dict().
# 2011.03.15
# -- Fix to incorp_analyses(), which failed to get the language for the LexDims right.
# 2011.03.18
# -- Possible to nest exhaustive class partitions, using 'subpartition' keyword under
#    'partition' in YAML lexicon (see examples in es/tiny.yaml).
# 2011.04.08
# -- Lexical class entries belonging to disjoint partitions of classes now record the other
#    elements of the partition in their disjoint attribute, and disjoint classes are
#    also accumulated during inheritance. The disjoint list is used in class_compatible.
# 2011.04.13
# -- Changes in how disjoint classes are read in from YAML files and recorded in entries.
# 2011.04.15
# -- Fixed a strange bug in inherit1 (how did this last so long?) that left the list of
#    entries empty if a possible ancestor on some branch was incompatible with the
#    original lex.
# 2011.04.17
# -- Fixed a bug in how disjoint classes get their parent classes.
# 2011.05.15
# -- In getting crosslexes, check for compatibility in the empty crosslex case.
# 2011.10.07
# -- Within partitions, crosslexes need to be associated with all parts (children)
#    rather than with the shared superclass. This now happens (see Lex.from_dict()).
# -- Lexicon.add_lex() changed to make words work as partition parts.
# 2011.12.06
# -- Lots of changes incorporating RevEmptyCrosslexes (mostly to inheritance)
# 2011.12.08
# -- Possible now to have more than one government constraint for a given word
#    and dimension (needed for Spanish transitive verbs).
# 2011.12.16
# -- Higher-level inheritance functions rewritten. Within-language and cross-language
#    inheritance is not kept separate, and inheritance for reverse empty nodes
#    is handled specially.
# 2011.12.18
# -- A few more fixes to inheritance, especially for empty nodes. Pretty stable now,
#    I think.
# 2011.12.22
# -- Patterns and unification eliminated (functions still around though).
# 2012.02.17
# -- Multiple indices possible in crosslex attribute.
# 2012.02.22
# -- Groups modified in several ways. Lexemes accessed in YAML can be copied
#    from others (see "break the ice" in en/tiny.yaml). (Note that this requires
#    that groups appear *after* other lexical entries.)  Groups now have a head
#    Lex (or set of Lexes in the case of disjoint lexeme children) which must
#    appear first in the YAML.
# 2012.02.25
# -- Various changes to reading functions for empty nodes, allowing more flexibility
#    for complex empty nodes (like copula in English as target).
# 2012.03.*
# -- Counts and probabilities in lexical entries and crosslexes.
#    Fixed bug in filter_classes.
# 2012.03.25
# -- Lexicon.flatten() produces a lexicon of only word and lexeme entries with
#    all attributes in grammatical entries inherited.
# -- In partition, keywords can now include 'wordpart', 'lexemepart', and 'grampart'.
# 2012.08.14
# -- Lexicon can have the same entry participating in multiple partitions (e.g.,
#    Gn @none in both @SJ and @OJ)
# 2012.09.16
# -- Fixes to make crosslexes work right in generation.
# 2012.11.19
# -- For each Lex, dictionaries for group IDs and group head IDs, with languages
#    as keys.
# 2012.12.01
# -- New attrib type specifying maximum (and potentially also minimum) number of arcs
#    into and out of nodes.
# 2013.05.22
# -- Added entries for unknown words.
# -- Fixed inheritance so it only checks the lexicon for grammatical classes when
#    it is flattening or working with (now completely obsolete!) hierarchical lexicons.
# 2013.07.10
# -- Split lex.py and lexicon.py
# 2013.07.31
# -- Lexicons can read in LexClass instances from .cls files
# 2013.08.09
# -- Lexicons can read in instantiations of LexClasses from .inst files
# 2013.09.13
# -- inherit() changed so that original lex is checked along with "add_entries"
#    in inheriting through crosslexes
# 2013.10.16
# -- Lexical class instantiations can refer to lexical entries by part-of-speech:
#      gnv=mbarete:vc
# 2013.10.26
# -- Lexical class instantiations can also refer to lexical entries by agr feature:
#      gn=mbota:@rfl  or gn=mbota:@rfl>1  (reflexive entry for mbota)
#      gn=mbota:@~rfl or gn=mbota:@rfl>0  (non-reflexive entry for mbota)
# 2014.02.04
# -- New method for creating and incorporating 'inherited crossling' lexical entries,
#    replacing corresponding ones with crosslexes that have not been filled in,
#    incorp_cross_inh().

# Needed to check on dimension names in crosslex attributes (at least)
from .utils import DIMENSIONS, PARSE, GENERATE, TRANSLATE
from .lex import *
import os, re, yaml

# String key for entries for unknown words.
UNKNOWN = '*'

## Regular expressions for reading in lexicon template files.
TEMPLATE_RE = re.compile(r'\s*\*\*(\S+)\s*$')
ENTRY_RE = re.compile(r'\s*\&\&\s*\*\*(\S+)\s*$')
VAR_RE = re.compile(r'\s*\%(\S+)\%[: ]+(\S+)\s*$')
VAR_SUB_RE = re.compile(r'\%(\S+)\%')

# There can be many del arcs out of a node; that's why this is high.
MAX_CARD = 8

### Debugging pickling
##class Pickler(pickle._Pickler):
##
##    def dump(self, obj):
##        """Write a pickled representation of obj to the open file."""
##        # Check whether Pickler was initialized correctly. This is
##        # only needed to mimic the behavior of _pickle.Pickler.dump().
##        print("DUMPING {}".format(obj))
##        if not hasattr(self, "write"):
##            raise pickle.PicklingError("Pickler.__init__() was not called by "
##                                "%s.__init__()" % (self.__class__.__name__,))
##        if self.proto >= 2:
##            self.write(pickle.PROTO + bytes([self.proto]))
##        self.save(obj)
##        pickle._Pickler.write(self, pickle.STOP)
##
##    def save(self, obj, save_persistent_id=True):
##        print("SAVING {}".format(obj))
##        # Check for persistent id (defined by a subclass)
##        return pickle._Pickler.save(self, obj, save_persistent_id=save_persistent_id)
##
##def dump(obj, path, protocol=None, *, fix_imports=True):
##    file = open(path, 'wb')
##    Pickler(file, protocol, fix_imports=fix_imports).dump(obj)

class Lexicon(dict):
    """Repository for the whole grammar/lexicon. Dict keys are words or lexemes. (In unflattened
    lexicons, they may also be grammatical class labels such as V_T.)
    """

    GID = 0   # Finite; can have neg out

    # Character indicating a feature in a lexical entry specification
    FEAT = '@'
    # Character relating feature name to value.
    VALUE = '>'
    # Character indicated false
    NEG = '~'

    # Name of a LexClass: ^xxx
    LEXCLASS = re.compile(r'\s*(\^\S+)\s*$')
    # A new instantiation
    # & NAME possible variable bindings
    INST = re.compile(r'\s*\&\s*(\S+)\s*(.*)$')
    # LexClass variable and value: var = val
    VAR_VAL = re.compile('(\w+\s*=\s*(?:\S+)|(?:\[.+\]))')
    # ?xxx?: yyy   [: optional]
#    VAR_VAL_LINE = re.compile(r'\s*\?(\S+)\?[: ]+(\S+)\s*$')
    VAR_VAL_LINE = re.compile(r'\s*(\S+)\s*=\s*(\S+)\s*$')
    VAR_VALLIST_LINE = re.compile(r'\s*(\S+)\s*=\s*\[(.+)\]\s*$')

    def __init__(self, language=None, hierarchical=True):
        dict.__init__(self)
        self.language = language
        self.groups = []
        # a name, LexClass dict
        self.classes = {}
        # hierarchical lexicons are those that are not flattened
        self.hierarchical = hierarchical
        # temporary place for crosslexes that are waiting to be instantiated
        # after other languages are created
        self.crosslexes_waiting = []

    def __repr__(self):
        return '%%{}'.format(self.language.name)

    def incorp_cross_inh(self, word, lexes):
        """Incorporate 'cross-inherited' entries, replacing those already in the lexicon
        without inheritance."""
        new_lex = {}
        for l in lexes:
            lex = l.lexify_cross_inh(word)
            source_id = l.id
            if source_id not in new_lex:
                new_lex[source_id] = []
            new_lex[source_id].append(lex)
        for id, l in new_lex.items():
            print("Incorporating cross-inherited entries {}, old id {}".format(l, id))
        old_entries = self.get(word)
        print("Old entries: {}".format(old_entries))
        new_entries = []
        for l in old_entries:
            new_ee = new_lex.get(l.id)
            if new_ee:
                new_entries.extend(new_ee)
            else:
                new_entries.append(l)
        print("New entries: {}".format(new_entries))
        self[word] = new_entries

    def read(self, lexicon_list):
        """Fill in the lexicon from a lexicon list read in from a file."""
        language = self.language
        lang_prefix = language.abbrev
        for lex in lexicon_list:
            if 'group' in lex:
                group = Group.from_dict(lex, language=language, lexicon=self)
                for l in group.lexes.values():
                    self.add_lex(l)
                # Not sure if lexicon needs to keep track of groups; maybe just for
                # debugging...
                self.groups.append(group)
            elif 'lexclasses' in lex:
                classes = lex['lexclasses']
                filename = classes + '.cls'
                if os.path.exists(os.path.join(language.get_dir(), filename)):
                    class_stream = open(os.path.join(language.get_dir(), filename),
                                       encoding='utf8')
                    print('Reading lex classes from {}: '.format(filename), end='')
                    LexClass.read(class_stream, self)
                    print()
            elif 'classinst' in lex:
                classinst = lex['classinst']
                filename = classinst + '.inst'
                if os.path.exists(os.path.join(language.get_dir(), filename)):
                    inst_stream = open(os.path.join(language.get_dir(), filename),
                                       encoding='utf8')
                    print('Reading lex class instantiations from {}'.format(filename))
                    self.read_classinst_file(inst_stream)
            elif 'sublexicon' in lex:
                sublex = lex['sublexicon']
                # This is a file for a sublexicon, which should also be loaded.
                # It could be a .yaml file...
                filename = sublex + '.yaml'
                if os.path.exists(os.path.join(language.get_dir(), filename)):
                    substream = open(os.path.join(language.get_dir(), filename),
                                     encoding='utf8')
                    try: 
                        sublex_list = yaml.load(substream)
                    except yaml.YAMLError:
                        raise
                # or a .lex file
                else:
                    filename = sublex + '.lex'
                    if os.path.exists(os.path.join(language.get_dir(), filename)):
                        sublex_path = os.path.join(language.get_dir(), filename)
#                        print(sublex_path, 'exists')
                        sublex_string = Lexicon.read_lexicon_file(sublex_path)
                        try:
                            sublex_list = yaml.load(sublex_string)
                        except yaml.YAMLError:
                            raise
                for lex1 in sublex_list:
                    if 'group' in lex1:
                        group = Group.from_dict(lex1, language=language, lexicon=self)
                        for l in group.lexes.values():
                            self.add_lex(l)
                        self.groups.append(group)
                    else:
                        subentries = Lex.from_dict(lex1, lang_prefix=lang_prefix, language=language,
                                                   lexicon=self)
                        for subentry in subentries:
                            # Add lex to the lexicon, with one or two keys (Lex names)
                            self.add_lex(subentry)
            else:
                # Convert lex (a dict) to an instance of Lex (multiple entries if
                # for a partition)
                entries = Lex.from_dict(lex, lang_prefix=lang_prefix, language=language,
                                        lexicon=self)
                for entry in entries:
                    # Add lex to the lexicon, with one or two keys (Lex names)
                    self.add_lex(entry)

    def extend(self, name, lexeme=False,
               pos='', root='', dim_attribs=None, cross=None,
               # Group properties
               gid=0, ghead=0, group_thead=None, groupouts=None,
               finalized=True, verbosity=0,
               check=False):
        """Make a new classless lexical entry, and add it to the lexicon.
        The lexicon and language may or not have been finalized and linked
        to other languages. In any case, the entry's daughter sets still needs
        to be set.

        If lexeme is True, make this a lexeme entry.
        dim_attribs: list of dim label, attributes pairs.
        cross: list of language abbrev, translation pairs, where translation is
           a dict of properties:
           lex: (name, index)        # an existing Lex in the other language
           name, dim_attribs, pos    # parameters of extend() to create Lex
                                       in other language
        """
        language = self.language
        lang_abbrev = language.abbrev
#        print('Extending {} with {}, dim attribs {}'.format(self, name, dim_attribs))
        lex = Lex(name=name, word=name if not lexeme else '',
                  lexeme=name if lexeme else '',
                  root=root, pos=pos,
                  language=language, lexicon=self,
                  flat=True)
        if gid:
            # gid is not 0, so this is part of a group
            lex.gid = gid
            lex.gids[lang_abbrev] = gid
            if ghead:
                lex.ghead = ghead
                lex.gheads[lang_abbrev] = ghead
            if group_thead:
                lex.group_thead = group_thead
            
        if dim_attribs:
            # Create the LexDims to store attributes
            for dim_label, attribs in dim_attribs:
                # If check is True, check here whether dim_label and
                # and attribs are valid.
                if '-' not in dim_label:
                    # It's just the dimension abbreviation, not the full
                    # language-dimension label, so add the language
                    dim_label = lang_abbrev + '-' + dim_label
                lexdim = LexDim(language=language, lex=lex, dim=dim_label,
                                attribs=attribs)
                lex.set_lexdim(dim_label, lexdim)
                #                if gid:
        # This follows finalization, so daughter sets have to be created.
        lex.make_daughter_sets()
        self.add_lex1(name, lex, name in self)
        if cross:
            languages = self.language.LANGUAGES
            # Make crosslex to entry in other language
            for t_abbrev, trans in cross:
                if finalized:
                    tlang = languages.get(t_abbrev)
                    if not tlang:
                        finalized = False
                    else:
                        tlexicon = tlang.lexicon
                tlex = None
                t_lexdim = None
                tlex_index = 0
                t_name = trans.get('name', '')
                t_index = trans.get('index', 0)
#                print('trans {}'.format(trans))
#                tlex_props = trans.get('lex')
                t_cross_attribs = trans.get('cross_attribs')
                empty = trans.get('empty')

                if t_cross_attribs:
                    # (dim_label, dim_attribs)
                    dim_label, dim_attribs = t_cross_attribs
                    if '-' not in dim_label:
                        # It's just the dimension abbreviation, not the full
                        # language-dimension label, so add the language
                        dim_label = lang_abbrev + '-' + dim_label
                    t_lexdim = LexDim(language=language, lex=lex, dim=dim_label,
                                      attribs=dim_attribs)
                    
                # Make the crosslexes
                xlex = Crosslex(lex,
                                targ_lang_abbrev=t_abbrev,
                                targ_lex_key=t_name, targ_lex_index=t_index,
                                targ_lex=tlex,
                                lexdim=t_lexdim,
                                #  targdim=None,
                                bidir=False)

                if empty:
                    for e in empty:
                        props, cond = e
                        tlex_key = props[0]
                        rel = [props[1], props[2], [props[2]]]
                        tindex = props[3] if len(props) > 3 else -1
#                        print('Empty cond {}'.format(cond))
                        empty_xlex = EmptyCrosslex(lex,
                                                   empty_lex_key='zero', empty_lex_index=0,
                                                   targ_lang_abbrev=t_abbrev,
                                                   targ_lex_key=tlex_key,
                                                   targ_lex_index=tindex,
                                                   empty_cond=cond,
                                                   agrs=None, rel=rel,
                                                   if_dim=None, count=1)
#                print('Created xlex {} to {}'.format(xlex, t_name))
#                print('Lex crosslexes {}'.format(lex.crosslexes))

#                if finalized:
#                    revxlex = Crosslex(tlex, targ_lang_abbrev=lang_abbrev,
#                                       targ_lex_key=t_name, targ_lex_index=lex.entry_index, targ_lex=lex,
#                                       lexdim=t_lexdim,
#                                       bidir=True)
        if verbosity:
            print("Creating lexical entry {}".format(lex))
        return lex
  
    @staticmethod
    def get_gid():
        '''Return a new group id, incrementing the counter.'''
        Lexicon.GID += 1
        return 'g{}'.format(Lexicon.GID)

    @staticmethod
    def load(language, verbosity=0):
        """Load the lexicon for the specified language from YAML files."""
        return Lexicon.deyaml(language, verbosity=verbosity)

    @staticmethod
    def deyaml(language, verbosity=0):
        """Create a lexicon from a YAML file."""
        #        print("Trying to deyaml", language, "directory", language.get_dir(), "file", language.lexicon_name + '.yaml')
        try:
            lexicon_name = language.lexicon_name or language.abbrev
            # Look for the YAML file for this language
            filename = lexicon_name + '.yaml'
            stream = open(os.path.join(language.get_dir(), filename), encoding='utf8')
            try:
#                # Import yaml; we should only have to do this once or twice for a given
#                # problem
#                import yaml
                try:
                    print('Creating lexicon for', language, 'grammar', lexicon_name)
# 'from', filename)
                    # Create an empty lexicon
                    lexicon = Lexicon(language)
#                    print('Created lexicon', lexicon)
                    # Read in the lexicon as a list of dicts
                    lexicon_list = yaml.load(stream)
                    # For each Lex name, create a dict entry consisting of a list of Lexs
                    lexicon.read(lexicon_list)
                    return lexicon
                except yaml.YAMLError as exc:
                    # Allow YAML errors to get past??
#                    print 'Error in YAML file',
#                    if hasattr(exc, 'problem_mark'):
#                        mark = exc.problem_mark
#                        print "location: (%s:%s)" % (mark.line+1, mark.column+1),
#                    print
                    raise
            except ImportError:
                print('yaml not found; download it from <http://pyyaml.org/wiki/PyYAML>')
            stream.close()
        except IOError:
            print("No yaml file for", language)

    @staticmethod
    def read_lexicon_file(filename):
        """Read in lexical entries from a .lex file. Returns a string that is to be
        loaded into YAML."""
        variables = {}
        templates = {}
        entries = []
        t_name = None
        template = ''
        with open(filename, encoding='utf8') as stream:
            for line in stream:
                # strip comments
                line = line.split('#')[0]
                # ignore empty lines
                if not line.strip():
                    continue
                m = TEMPLATE_RE.match(line)
                if m:
#                    print('{} matches template with name {}'.format(line, m.group(1)))
                    if template and t_name:
                        # Finished another template
                        templates[t_name] = template
                    # Start a new template
                    t_name = m.group(1)
                    template = ''
                    continue
                m = ENTRY_RE.match(line)
                if m:
#                    print('{} matches entry with template {}'.format(line, m.group(1)))
                    if variables:
                        # This is not the first entry; finish the last entry
                        entries.append(variables)
                        variables = {}
                    elif template and t_name:
                        # This is the first entry; finish the last template
                        templates[t_name] = template
                        # Done with templates
                        t_name = None
                        template = ''
                    variables['tmp'] = m.group(1)
                    continue
                m = VAR_RE.match(line)
                if m:
#                    print('{} matches variable with name {} and value {}'.format(line, m.group(1), m.group(2)))
                    name = m.group(1)
                    value = m.group(2)
                    variables[name] = value
                    continue
                # Read in a line that's either part of a template or an entry
                if t_name:
                    # We're reading in a template
                    template += line # + '\n'
                else:
                    print("Something wrong; what's this: {}".format(line))
            if variables:
                entries.append(variables)
        res = ''

        # Fill in each entry's template
        for entry_vars in entries:
            template = entry_vars['tmp']
            template = templates[template]
            entry = Lexicon.replace_vars(template, entry_vars)
            res += entry

        return res

    def read_classinst_file(self, stream):
        """Read in instantiations of LexClasses from a file."""
        lexclass = None
        variables = {}
        for line in stream:
            # strip comments
            line = line.split('#')[0]
            # ignore empty lines
            if not line.strip():
                continue

            m = Lexicon.LEXCLASS.match(line)
            if m:
                # First make the current instantiation if there is one
                if variables and lexclass:
                    lexclass.instantiate(variables)
                    variables = {}
                # Get the new class name
                lexclass_label = m.group(1)
                lexclass = self.classes.get(lexclass_label)
#                if lexclass:
#                    print("Lex class for instantiation: {}".format(lexclass))
                if not lexclass:
                    print("Warning: lexicon has no lex class called {}".format(lexclass_label))
                continue

            m = Lexicon.INST.match(line)
            if m:
                inst_name = m.group(1)
                other_vars = m.group(2)
                if variables and lexclass:
                    # First make the current instantiation
                    lexclass.instantiate(variables)
                    variables = {}
                variables['name'] = inst_name
                if other_vars:
                    varvals = Lexicon.VAR_VAL.split(other_vars)
                    for varval in varvals:
                        if '=' in varval:
                            var, val = varval.strip().split('=')
                            if '[' in val:
                                val = val.replace('[', '').replace(']', '')
                                val = [v.strip() for v in val.split(',')]
                            else:
                                val = val.strip()
                            var = var.strip()
                            variables[var] = val
#                            print('var {}, val {}'.format(var, val))
#                print('Instantiating with name {}'.format(inst_name))
                continue

            m = Lexicon.VAR_VALLIST_LINE.match(line)
            if m:
                # Value of variable is a list of values
                var, vallist = m.group(1), m.group(2)
                vallist = [v.strip() for v in vallist.split(',')]
#                print('Variable {}, value list {}'.format(var, vallist))
                variables[var] = vallist
                continue

            m = Lexicon.VAR_VAL_LINE.match(line)
            if m:
                var, val = m.group(1), m.group(2)
#                print('Variable {}, value {}'.format(var, val))
                variables[var] = val
                continue

            else:
                print("Something wrong; what's this: {}?".format(line))

        if variables and lexclass:
            # Make the last instantiation
            lexclass.instantiate(variables)

    @staticmethod
    def subs_var(var_dict):
        """Returns a function that takes a match object to
        pass to re.sub() in replace_vars()."""
        return lambda matchobj: var_dict.get(matchobj.group(1), '')
    
    @staticmethod
    def replace_vars(string, var_dict):
        """Substitutes variable values in var_dict into string."""
        return VAR_SUB_RE.sub(Lexicon.subs_var(var_dict), string)

    @staticmethod
    def filter_classes(classes, ifdim=''):
        """Remove (mutating) classes that are ancestors of others in list, copying
        IF dimensions from ancestors to dimensions."""
        if len(classes) <= 1:
            return
#        print('Filtering {}'.format(classes))
        to_remove = set()
        for cls1 in classes:
#            print('Cls1', cls1)
            for cls2 in classes:
#                print(' Cls2', cls2)
                if cls1 == cls2:
                    continue
                if cls2.isa(cls1):
#                    print('  {} isa {}'.format(cls2, cls1))
                    dims1 = [(k, v) for k, v in cls1.dims.items() if k.split('-')[-1] in DIMENSIONS['if']]
                    for k, v in dims1:
                        dim2 = cls2.dims.get(k)
                        if not dim2:
                            cls2.dims[k] = v
                        else:
                            # cls2 already has dimension k; add features to it (assume no conflict)
                            for attrib, value in v.attribs.items():
                                dim2.attribs[attrib] = value
                    to_remove.add(cls1)
        for c in to_remove:
#            print('Removing {}'.format(c))
            classes.remove(c)

    def flatten(self, between=True, other_languages=[]):
        """Return a new non-hierarchical lexicon by inheriting attribs to non-grammatical entries
        from all classes, creating new entries when there are partitions in the hierarchy."""
#        print('Flattening {}'.format(self))
        lexicon = Lexicon(language=self.language, hierarchical=False)
        languages = [self.language] + other_languages
        for name, entries in self.items():
            # name is the key in the lexicon dict
            if name[-1] == '!' and len(name) > 1:
                # Ignore entries that are special partition roots
                continue
            new_entries = []
            for entry in [e for e in entries if e.is_lexical()]:
                if entry in list(lexicon.values()):
                    print('{} already in lexicon'.format(entry))
                    continue
                elif entry.name != name and name[0] not in [UNKNOWN, '!', '%', '#', '@'] and not entry.root:
                    # Ignore entries that do not have the same name as the key,
                    # that is, roots of lexical partitions,
                    # unless they begin with '!' or '%' or '#' or '@' or contain '*'
                    continue
                elif entry.flat:
                    # The entry is already flattened, so just copy it changing its lexicon only
#                    print('Flat entry {}, crosslexes {}'.format(entry, entry.crosslexes))
                    lexicon[name] = [entry]
                    entry.lexicon = lexicon
                # This apparently creates some crosslexes again
                new_entries1 = entry.inherit(lexicon, inh_lexicon=self,
                                             languages=languages,
                                             between=between)
                new_entries.extend(new_entries1)
            if new_entries:
#                print('Adding new entries {} to lexicon {}'.format(new_entries, lexicon))
                lexicon[name] = new_entries
        # Just point to self's groups? (or copy them?)
        lexicon.groups = self.groups
        lexicon.classes = self.classes
        return lexicon

    def finalize_flat(self):
        """Make final changes to flattened entries."""
        pass

    def copy_disjoint_lexeme(self, label, gid=0):
        """Return a copy of each of the disjoint daughters associated with
        label."""
        daughters = self.get(label, [])
        # Copy the daughters, without copying their disjoint lexes
#        print('Cloning disjoing lexes {}'.format(daughters))
        d_lexes = [d.clone(disjoint=False, temp=False, suf='*', gid=gid) for d in daughters]
        for d in d_lexes:
            disj = d_lexes[:]
            disj.remove(d)
            d.disjoint = disj
        return d_lexes
        
    def add_lex(self, lex):
        """Add a new lexical entry to the lexicon."""
        names = [lex.get_name()]
        if lex.root and lex.root not in names:
            # For words with a root that is not a name, add the root as another name
            # (so that they can be looked up during morphological analysis)
            names.append(lex.root)
#            print('Adding {}, names {}, part {}'.format(lex, names, lex.part))
        if lex.part:
            # lex is part of a partition; add the partition name to its lexicon keys
            if lex.partitions:
                names.extend(lex.partitions)
            else:
                names.append(lex.gram or lex.lexeme)
        for name in names:
            # subclasses in partitions get stored twice, once by their 'gram', once
            # by their 'label'
            if name:
                # Make the lex empty if its name has '@' or in it.
                if '@' in name:
                    lex.empty = True
                if name in self:
                    if lex in self[name]:
                        continue
                    # Already at least one Lex with the name; append the new one
                    self.add_lex1(name, lex, True)
                    #                    # This is wrong because there could be multiple names with
                    #                    # the same lex.
                    #                    lex.entry_index = len(self[name])
                    #                    self[name].append(lex)
                elif UNKNOWN in name:
                    # An entry for an unknown word: *, *V, *N, etc.
                    self.add_lex1(UNKNOWN, lex, existing=UNKNOWN in self)
                    #                    current_unk = self.get(UNKNOWN, [])
                    #                    lex.entry_index = len(current_unk)
                    #                    self[UNKNOWN] = current_unk + [lex]
                else:
                    self.add_lex1(name, lex)
                    #                    lex.entry_index = 0
                    #                    # First Lex with this name; start a new dict entry
                    #                    self[name] = [lex]

    def add_lex1(self, key, lex, existing=False):
        """Add the lex to the lexicon and set its entry index."""
        if existing:
            # There are already entries
            lex.entry_index = len(self[key])
            self[key].append(lex)
        else:
            # First entry for this key
            lex.entry_index = 0
#            print('{} adding lex for key {}'.format(self, key))
            self[key] = [lex]

    def get_unknown(self, name='', clone=True):
        """
        Find lexical entries for unknown words, including those for
        particular syntactic classes.
        """
        print("Creating unknown entry for {}".format(name))
        lexs = self.get(UNKNOWN, [])
        if clone:
#            print('Cloning unknown {}'.format(lexs))
            lexs = [lex.clone() for lex in lexs]
        if name:
            for l in lexs:
                l.name = name
        return lexs

    def get_by_spec(self, name, spec=None):
        """Return all entries for name compatible with spec, which could be
        a POS or an agrs list or dict."""
        if not spec:
            return self.get(name)
        elif Lexicon.FEAT in spec:
            # spec specifies feature values
            # different features are separate by commas
            agrs = Lexicon.expand_fv(spec)
            return self.get_by_agrs(name, agrs)
        else:
            # spec specifies POS
            return self.get_by_pos(name, spec)

    @staticmethod
    def expand_fv(fv):
        """fv is a string specifying one or more feature-value constraints. This is expanded
        either to a list or a dict."""
        fv = fv.replace(Lexicon.FEAT, '')
        # comma-separated list
        fv = fv.split(',')
        lres = []
        dres = {}
        for fv1 in fv:
            if '>' in fv1:
                f, v = fv1.split('>')
                # Make v into a tuple of ints
                v = eval(v)
                if isinstance(v, int):
                    v = (v,)
                dres[f] = v
            elif Lexicon.NEG in fv1:
                fv1 = fv1.replace(Lexicon.NEG, '')
                dres[fv1] = (0,)
            else:
                dres[fv1] = (1,)
        if dres:
            return dres
        else:
            return lres

    def get_by_pos(self, name, pos=None):
        """Return all entries for name with the given POS."""
        lexs = self.get(name)
        if pos:
#            print("Looking for lexes in {} with POS {} ({})".format(lexs, pos, [l.pos for l in lexs]))
            return [l for l in lexs if l.get_pos() == pos]
        else:
            return lexs

    def get_by_agrs(self, name, agrs=None):
        """agrs is a feature-value dict."""
        lexs = self.get(name)
        if agrs:
            res = []
            for l in lexs:
                agr_dim = l.dims.get(self.language.surface_dim)
                if not agr_dim:
                    continue
                l_agrs = agr_dim.attribs.get('agrs')
                if not l_agrs:
                    continue
                ok = True
                for f, v in agrs.items():
                    l_v = l_agrs.get(f)
#                        print('f {}, v {}, l_v {}'.format(f, v, l_v))
                    if (not l_v) or (v not in l_v):
                        ok = False
                        break
                if ok:
                    res.append(l)
            return res
        else:
            return lexs

    ## Lexicalization

    def lexicalize(self, name, word=True, clone=False, indices=None, any_other=False,
                   classes=False, analyze=False, orig_form=None, verbosity=1):
        """
        Find lexical entries matching name.
        
        @param word: whether to find only words (as opposed to lexemes and grams).
        @type  word: boolean
        @param clone: whether to clone the lexical entries
        @type  clone: boolean
        @param indices: entry indices use
        @type  indices: set
        @param any_other: whether there are lexs from morphological analysis
        @type  any_other: boolean
        @param classes: whether this is a search for classes of a lex
        @type  classes: boolean
        """
        if word and verbosity:
            print('Lexicalizing {}'.format(name))
        # Lexicalize a class
        if classes:
            lexs = [lex for lex in self.get(name, [])]
        # Lexicalize the output of morphological analysis: has to be a lexeme
        elif not word:
            lexs = [lex for lex in self.get(name, []) if lex.lexeme]
        # Lexicalize a wordform
        else:
            lexs = [lex for lex in self.get(name, []) if lex.word]
#        lexs = [lex for lex in self.get(name, []) if not word or lex.word] # or lex.label]
        if not lexs and word and not any_other and not classes and not analyze:
            l = self.get_unknown(name=name, clone=True)
            if verbosity:
                print('No entry found for {}; using unknown entries {}'.format(name, l))
            return l
        if indices:
            lexs = [lex for lex in lexs if lex.entry_index in indices]
            #        if clone:
            #            print('Cloning in lexicalize: {}'.format(lexs))
            #            lexs = [lex.clone() for lex in lexs]
#        print('Lexs {}'.format(lexs))
        if analyze:
            anal_lex = self.analyze(orig_form, name, incorp=True)
            if anal_lex:
                lexs.extend(anal_lex[0])
        return lexs

    def analyze(self, word, form, position=0, incorp=True):
        """Analyze the word with pre-processed form form morphologically.
        position is needed for segmentations that happen during analysis."""
        anals = []
        segmentations = []
        analyses = self.language.anal(word, form)
        if analyses:
            for root, grams in analyses[1]:
                # Look for lexical entries for each analysis
                anal_lexs = self.lexicalize(root, word=False)
                if anal_lexs:
                    anals.extend([(l, grams) for l in anal_lexs])
                segs = analyses[2]
                new_word = analyses[3]
                if segs:
                    root = analyses[1][0][0]
                    if len(segs) > 1:
                        segs.sort(key=lambda x: x[0][0] == '_')
                    for seg in segs:
                        segmentations.append([position, (root, anals), seg, new_word])
            if incorp:
                # Assume the agreement dimension is the "surface dimension"
                agree_dim = self.language.surface_dim
                a = self.incorp_analyses(anals, [agree_dim])
                return a, segmentations
        return anals, segmentations

    def incorp_analyses(self, analyses, dimensions, word='', problem=None, clone=True, cache=True):
        """Incorporate morphological analyses into root lexical entry, returning None if the
        entry is incompatible with any analyses.
        analyses is a list of [lex, feats] pairs.
        dimensions are agreement dimensions."""
        result = []
        for analysis in analyses:
#            print('{}: analysis {}'.format(node, analysis))
            lex = analysis[0]
            agr = analysis[1]
            if clone:
#                print('Cloning in incorp: {}'.format(lex))
                lex = lex.clone()
            # Incorporate morphological analysis in agrs
            for dimension in dimensions:
                # Only add information to dimensions in source language
                # dimension could be the actual dimension or a dimension abbreviation
                abbrev = ''
                if isinstance(dimension, str):
                    # It's the dimension name; does it belong to self.language
                    abbrev = dimension
                    if dimension.partition('-')[0] != self.language.abbrev:
                        continue
                else:
                    abbrev = dimension.abbrev
                    if self.language != dimension.language:
                        continue
                lex_dim = lex.dims.get(abbrev)
                if lex_dim:
                    lex_agrs = lex_dim.attribs.get('agrs')
                    # If the lex already has agrs, update with analysis
                    if lex_agrs:
                        # Add features from analysis that are *not* in lex,
                        # rejecting the lex if it's not compatible with the analysis
                        for feat, value in agr.items():
                            if not feat:
                                # could be None
                                continue
                            if feat in lex_agrs:
                                lex_value = lex_agrs[feat]
                                pre_arcs = problem.pre_arcs.get(abbrev) if problem else None
                                pre_arc_compat = True
                                if pre_arcs:
                                    for arc_label in pre_arcs:
                                        lex_arc_label = lex_dim.attribs.get('outs', {}).get(arc_label, None)
                                        if lex_arc_label == 0:
                                            # If pre arcs specify an arc with arc_label and this lexical entry forbids one,
                                            # then the entry is incompatible and must be rejected
                                            pre_arc_compat = False
                                            break
                                if not pre_arc_compat:
                                    lex = None
                                    break
                                inters = value.intersection(lex_value)
                                if not inters:
                                    # lex_value and value have nothing in common; reject lex
                                    # for this analysis
                                    lex = None
                                    break
                                else:
                                    # Use intersection of lex_value and value
                                    lex_agrs[feat] = inters
                            else:
                                lex_agrs[feat] = value
                    else:
                        lex_dim.attribs['agrs'] = agr
                else:
                    lex.set_lexdim(abbrev,
                                   LexDim(label=abbrev, language=dimension.language,
                                          lex=lex, dim=abbrev,
                                          attribs={'agrs': agr}))
            if lex:
#                print('  Appending lex {}'.format(lex))
                result.append(lex)
        if cache:
            new_lexs = []
#            copies = []
            for l in result:
                new_l = l.inst_lexeme(word)
                new_lexs.append(new_l)
#                copies.append(new_l.clone(disjoint=False, temp=True))
            print('Created new lexs {}'.format(new_lexs))
            return new_lexs
        return result

    def inherit(self, lex, dimensions, add_entries=[], node=None,
                classes=None, languages=None, target_languages=None,
                transfer_xlex=True, copy_xtarg=True,
                reverse=False, src_language=None, set_prob=True,
                between=True, within=True, process=PARSE,
                flatten=False,
                verbosity=0):
        '''
        within: whether to inherit from entries in this language
        between: whether to inherit across crosslexes
        '''
        src_language = src_language or lex.language
        lang_abbrevs = [l.abbrev for l in languages]
        lexicons = [l.lexicon for l in languages]
        target_lang_abbrevs = [l.abbrev for l in target_languages]
        target_lexicons = [l.lexicon for l in target_languages]
        non_target_langs = [l for l in languages if l not in target_languages] + [src_language]
        non_target_abbrevs = [l.abbrev for l in non_target_langs]
        non_target_lexicons = [l.lexicon for l in non_target_langs]
        if verbosity > 0:
            print('>>STARTING INHERITANCE FOR {}; language {} current language {} src language {}'.format(lex, lex.language, self.language,
                                                                                                          src_language))
#        print('inherit: lex: {}, classes: {}'.format(lex, classes))
        if within:
            if verbosity > 0:
                print('>>Inheriting within language {} for {}'.format(lex.language, lex))
            n_add = len(add_entries)
            if lex.language != self.language:
                if verbosity > 1:
                    print("{}'s language is {}, not source".format(lex, lex.language.abbrev))
                lex_lexicon =  lex.language.lexicon
                if flatten or lex_lexicon.hierarchical:
                    classes = classes or lex_lexicon.get_classes(lex, languages=languages, clone=True)
                if classes:
                    lex_lexicon.inherit1language(lex, lex, dimensions,
                                                 classes, checked=[], add_entries=add_entries,
                                                 languages='all' if flatten else languages,
                                                 process=process, copy_xtarg=copy_xtarg,
                                                 reverse=reverse, is_source=False,
                                                 flatten=flatten, between=not flatten,
                                                 set_prob=set_prob,
                                                 src_language=src_language, verbosity=verbosity)
                # Don't do any more inheritance
                return
            else:
                if flatten or self.hierarchical:
                    classes = classes or self.get_classes(lex, languages=languages, clone=True)
                if classes:
                    self.inherit1language(lex, lex, dimensions,
                                          classes, checked=[], add_entries=add_entries,
                                          flatten=flatten, process=process,
                                          copy_xtarg=copy_xtarg,
                                          languages='all' if flatten else languages,
                                          reverse=reverse, is_source=True, between=not flatten,
                                          set_prob=set_prob,
                                          src_language=src_language, verbosity=verbosity)
            if len(add_entries) > n_add:
                if verbosity > 0:
                    print('New entries added to {}: {}'.format(lex, add_entries))
        if not between:
            return

        if verbosity > 0:
            print('>>Inheriting between languages for {}, targets {}'.format(lex, target_languages))
        # if this is a reverse empty node, exclude target languages because we already
        # covered them, and we'll otherwise get spurious empty classes
        l_abbrevs = lang_abbrevs[:]
        lexs = lexicons[:]
        # For each of the original lex and the add_entries list, try to inherit across languages
        entries = [lex] + add_entries
        if reverse:
            for a in target_lang_abbrevs:
                l_abbrevs.remove(a)
            for l in lexs:
                lexs.remove(l)
        for lang_abbrev, lexicon in zip(l_abbrevs, lexs):
            if lang_abbrev == self.language.abbrev and not lexicon:
                lexicon = self
            if verbosity > 0:
                print(lex, 'inheriting in', lang_abbrev)
                if verbosity > 1:
                    print('Add entries', add_entries)
            for entry in entries:
                xlex_targets = lexicon.get_xlexes(lex, entry, languages=[lang_abbrev],
                                                  actual_languages=languages,
                                                  target_languages=target_languages,
                                                  transfer=transfer_xlex, process=process,
                                                  src_language=src_language,
                                                  consider_other_langs=True,
                                                  verbosity=verbosity)
                if verbosity > 2:
                    print(' Inheriting between languages for entry', entry)
                    print(' Found xlex targets', xlex_targets)
                Lexicon.filter_classes(xlex_targets)
                if verbosity > 0:
                    print('Filtered xlex targets', xlex_targets)
                if not xlex_targets:
                    # If no crosslingual links are found, use the unknown lexical
                    # entry for each target language, but if lex is in the target
                    # language, don't bother
#                    if src_language != lex.language:
#                        print('No crosslingual links found, but lex {} is in target language'.format(lex))
                    if src_language == lex.language:
                        print('No crosslingual links found for {}'.format(lex))
                        xl = []
                        for l in target_languages:
                            xl.extend(l.lexicon.get_unknown(name=lex.name, clone=True))
                        xlex_targets = xl
                if xlex_targets:
                    xlexicon = xlex_targets[0].language.lexicon
#                    print('xlex_targets {}'.format(xlex_targets))
                    xlexicon.inherit1language(lex, entry, dimensions,
                                              [xlex_targets], checked=[], add_entries=add_entries,
                                              languages=languages, reverse=reverse, process=process,
                                              flatten=flatten, between=True,
                                              copy_xtarg=copy_xtarg,
                                              is_source=False, src_language=src_language,
                                              verbosity=verbosity)

        # ELIMINATE ALL OF THIS REVERSE STUFF LATER.
        # Look for reverse crosslexes, but only in the first reversed languages (semantics or the source language)
        if not reverse:
            abbrev = non_target_abbrevs[0]
            lexicon = non_target_lexicons[0]
            if abbrev == self.language.abbrev and not lexicon:
                lexicon = self
            if verbosity > 0:
                print('>>Inheriting backwards for {} from {}'.format(lex, target_lang_abbrevs))
            if verbosity > 1:
                print(lex, 'inheriting backwards in', abbrev)
                print('Add entries', add_entries)
            for entry in entries:
                lexicon.get_xlexes(lex, entry, languages=[abbrev],
                                   actual_languages=languages,
                                   transfer=transfer_xlex, process=process,
                                   consider_other_langs=False,
                                   src_language=src_language,
                                   target_languages=target_languages,
                                   reverse=True, verbosity=verbosity)

        # Continue inheriting backwards to source if this is a complex empty node
        if reverse:
            src_abbrev = src_language.abbrev
            src_lexicon = non_target_lexicons[-1]
            if verbosity > 0:
                print('>>Proceeding to source language', src_abbrev)
            for entry in entries:
                xlex_targets = self.get_xlexes(lex, entry, languages=[src_abbrev],
                                               actual_languages=languages, process=process,
                                               target_languages=target_languages,
                                               src_language=src_language,
                                               transfer=transfer_xlex,
                                               consider_other_langs=True,
                                               verbosity=verbosity)
                Lexicon.filter_classes(xlex_targets)
                if xlex_targets:
                    if verbosity > 1:
                        print('Found xlexes back to source language', xlex_targets)
                    src_lexicon.inherit1language(lex, entry, dimensions,
                                                 [xlex_targets], checked=[], add_entries=add_entries,
                                                 languages=languages, reverse=reverse,
                                                 process=process, copy_xtarg=copy_xtarg,
                                                 flatten=flatten, between=True,
                                                 is_source=False, src_language=src_language,
                                                 verbosity=verbosity)

    def get_classes(self, lex, languages='', clone=False):
        '''Get classes of lex within this lexicon and crosslexes in crosslexicon if there is one.'''
        # Get names of classes
        classes = lex.classes[:]
        # Get lexes for classes
        classes = [self.lexicalize(cls, word=False, clone=clone, classes=True) for cls in classes]
        return classes

    def get_xlexes(self, base_lex, lex, languages='',
                   actual_languages=None,
                   transfer=False, src_language=None,
                   consider_other_langs=False,
                   reverse=False, target_languages=None, process=PARSE,
                   other_languages=None, verbosity=0):
        '''Get crosslexed entries and LexDims, returning a cloned target entry.
        If transfer, consider L2L xlexes as well as those
        to or from semantics. But give priority to L2L over semantics.
        If consider_other_langs is True, check crosslexes indexed by a language other
        than Semantics.
        '''
#        if verbosity:
#            print('Get xlexes; lexicon {} base lex {} lex {} languages {}'.format(self, base_lex, lex, languages))
#            print(' transfer {} src language {} consider other {}'.format(transfer, src_language, consider_other_langs))
#            print(' reverse {} target langs {} other langs {}'.format(reverse, target_languages, other_languages))
        # List of languages
        actual_languages = actual_languages or []
        if process == GENERATE:
            # Add Semantics to languages
            actual_languages = actual_languages + [src_language]
        # List of target language abbreviations
        target_languages = target_languages or []
        other_languages = other_languages or set()
        target_lexes = []
        xlexes = lex.crosslexes
        if xlexes:
            if verbosity > 2:
                print('Found XLEXES for {}: {}'.format(lex, xlexes))
            if reverse:
                if verbosity > 2:
                    print('REVERSE XLEXES', xlexes, 'target languages', target_languages, 'languages', languages, 'process', process)
                if process==GENERATE:
                    # Use target language as languages to look for reverse xlexes
                    languages = [l.abbrev for l in target_languages]
                for lg in languages:
                    target_xlexes = xlexes.get(lg)
                    if target_xlexes:
                        for xlex in target_xlexes:
                            if not transfer and not xlex.is_semantic():
                                if verbosity > 2:
                                    print('  Ignoring', xlex)
                                continue
                            if isinstance(xlex, RevEmptyCrosslex):
                                # Need to accept only xlexes from *target* language
                                # (insert language in xlex)
                                insert_lang = xlex.source_lex.language
                                if not xlex.insert_lex:
                                    #                                    print('Adding insert lex {} to lexicon {}'.format(insert_lex_key,
                                    #                                                                                      insert_lang.lexicon))
                                    xlex.insert_lex = insert_lang.lexicon[xlex.insert_lex_key]
                                if insert_lang.abbrev in [l.abbrev for l in target_languages]:
#                                    print('Adding complex empty node {}'.format(xlex))
                                    base_lex.complex_empty_nodes.append(xlex)
            else:
                if verbosity > 2:
                    print('  XLEXES', xlexes)
                for lg in languages:
                    if lg == 'sem' or self.language.abbrev == 'sem' or consider_other_langs:
                        target_xlexes = xlexes.get(lg)
                        if verbosity > 1:
                            print(' target xlexes {}'.format(target_xlexes))
                        if target_xlexes:
                            if verbosity > 2:
                                print('    target xlexes', target_xlexes)
                            for xlex in target_xlexes:
                                targ_key = xlex.targ_lex_key
                                targ_index = xlex.targ_lex_index
                                targ_lexicon = xlex.targ_lang.lexicon
                                xlex_entry = xlex.targ_lex
                                if not xlex_entry:
                                    print('base lex {}, lex {}, xlex target key {}'.format(base_lex, lex, targ_key))
                                    if targ_key not in targ_lexicon:
                                        print("No entry in target language for {}".format(targ_key))
                                        continue
                                    else:
                                        # A target entry has been created since the source crosslex was created
                                        xlex_entry = targ_lexicon[targ_key][targ_index]
                                        xlex.targ_lex = xlex_entry
                                if not transfer and not xlex.is_semantic():
                                    if verbosity > 2:
                                        print('  Ignoring', xlex)
                                    continue
                                if isinstance(xlex, EmptyCrosslex):
                                    # Empty crosslexes need to be treated differently
                                    if self.empty_xlex_compatible(base_lex, xlex):
                                        if verbosity > 2:
                                            print('      xlex is compatible')
                                        # Associate the xlex with base_lex so an
                                        # empty node can be created later.
#                                        print('Adding complex empty node {} (2)'.format(xlex))
                                        base_lex.complex_empty_nodes.append(xlex)
                                elif not isinstance(xlex, RevEmptyCrosslex):
                                    xlex_lexdim = xlex.lexdim
#                                    if not xlex.targ_lang:
#                                        xlex.targ_lang = [l for l in actual_languages if l.abbrev == xlex.targ_lang_abbrev][0]
#                                    if not xlex_entry:
#                                        #                                        print('Adding xlex entry {} to lexicon {}'.format(targ_key, targ_lexicon))
#                                        xlex_entry = targ_lexicon[targ_key][targ_index]
#                                    print('xlex entry: {}'.format(xlex_entry))
                                    # Only add new target lexes if they're not already among the
                                    # the inherit classes for base_lex
                                    if verbosity > 2 and any([xlex_entry.equals(ic) for ic in lex.inh_classes]):
                                        print('      xlex entry', xlex_entry, 'already in', lex.inh_classes)
                                    if not any([xlex_entry.equals(ic) for ic in lex.inh_classes]):
                                        # Clone both the entry and the lex dim
#                                        print('Cloning in xlex: {}'.format(xlex_entry))
                                        # Clone the target entry, recording the count for the xlex in its xcount
                                        xlex_entry_clone = xlex_entry.clone(disjoint=False, xcount=xlex.count)
                                        if xlex_lexdim:
                                            xlex_lexdim = xlex_lexdim.clone(lex=xlex_entry_clone)
                                        # Copy the count from the xlex to the target lex
                                        xlex_entry_clone.count = xlex.count
                                        xlex_entry_clone.update_crosslex_entry(xlex_lexdim)
                                        target_lexes.append(xlex_entry_clone)
#        print('inh classes {}, xlexes: {}'.format(lex.inh_classes, target_lexes))
        return target_lexes

    def empty_xlex_compatible(self, lex, empty_xlex):
        '''Are the constraints in the empty xlex satisfied for this lex (the trigger
        for the empty xlex)?'''
        agrs = empty_xlex.agrs
        rel = empty_xlex.rel
        if agrs:
            # Do the feature-value agrs in the empty_lex agree with this in the ID
            # dimension of the lex?
            agr_dim = agrs[0]
            lex_agrs = lex.dims[agr_dim].attribs.get('agrs', {})
            for feat, value in agrs[1].items():
                if not unify_fssets(value, lex_agrs.get(feat, set())):
                    print('Lex agrs', lex_agrs, 'doesnt agree with', value)
                    return False
        return True

    def inherit1language(self, orig_lex, lex, dimensions, classes=None,
                         checked=None, add_entries=None, languages=None,
                         reverse=False, src_language=None, is_source=True,
                         set_prob=True, flatten=False, between=True,
                         copy_xtarg=True, process=PARSE,
                         verbosity=0):
        checked = checked or []
        classes = classes or []
#        add_entries = add_entries or []
        if classes:
            class1_lex = classes[0]
            if len(class1_lex) == 0:
                return
#            print('inherit1language: class1_lex {}'.format(class1_lex))
            # Name for the first list of classes
            class1_name = class1_lex[0].name
            # Remaining lists of classes
            remaining = classes[1:]
            # Names for each list of remaining classes
            remaining_names = [cls[0].name for cls in remaining]
            if not class1_lex: raise ValueError("No class {}".format(class1_name))
            if verbosity > 1:
                print('Getting classes labeled {} for {}: '.format(class1_name, lex), end='')
                for cls in class1_lex:  print(cls, end=' ')
                print()
            # First eliminate classes that are not compatible with lex.
            # This is where exhaustive subclass partitions of superclasses are checked.
            compat_cls1_lex = [cls for cls in class1_lex if lex.class_compatible(cls, dimensions, verbosity=verbosity)]
            if not compat_cls1_lex:
                # Nothing compatible with entry (only possible if the word has morphological features
                # that are incompatible with syntactic features)
                # Don't use this entry or any of its accumulated classes
                if verbosity > 1:
                    print('  No class compatible with {}'.format(lex))
                add_entries.remove(lex)
                return True
            if verbosity > 1:
                if len(compat_cls1_lex) < len(class1_lex):
                    print('  Classes compatible with {}'.format(lex), end='')
                    for cls in compat_cls1_lex:  print(cls, end=' ')
                    print()
                else:
                    print('  All classes compatible with {}'.format(lex))
            # Create new cloned lexes if there's more than one compatible class lex left
#            if len(compat_cls1_lex) > 1:
#                print('Cloning in inherit1: {}'.format(lex))
#            print('Inherit 1 {}, cloned? {}'.format(lex, lex.cloned))
            lexes = [lex] if not between else [lex.clone(temp=False if flatten else True)]
            lexes = lexes + [lex.clone(temp=False if flatten else True) for i in range(len(compat_cls1_lex)-1)]
            # If there are multiple classes and each is lexical, set probabilities for each lex
            count_total = 0
            if len(lexes) > 1 and set_prob:
                if all([c.is_lexical() for c in compat_cls1_lex]):
                    count_total = sum([c.count for c in compat_cls1_lex])
                if verbosity > 1:
                    print("Cloning", lex, 'as', lexes, 'classes:', compat_cls1_lex)
            # For each combination of lex and class entry...
            for l, cls in zip(lexes, compat_cls1_lex):
                if len(lexes) > 1 and set_prob:
                    if verbosity > 1:
                        print('One of multiple classes', cls)
                        print('{} prob: {}'.format(l, l.prob))
                    if count_total:
                        l.prob *= cls.count / count_total
                # If the class entry has not already been checked
                if cls not in checked:
                    # Add entry to the new entries unless this is the original, uncloned lex
                    if l != lex:
                        if verbosity > 1: 
                            print('Adding entry', l)
                        add_entries.append(l)
                    ## The actual inheritance
                    # Inherit the properties from this class entry to the lex
                    # Languages to inherit crosslexes from
                    if languages == 'all':
                        x_langs = 'all'
                    else:
                        x_langs = [l.abbrev for l in languages]
                    # In the reverse direction, also look for crosslexes back to the source language
                    if reverse:
                        x_langs += [src_language.abbrev]
                    l.inherit_properties(cls, dimensions, cls.language, is_source=is_source,
                                         languages=x_langs, flatten=flatten, between=between,
                                         process=process, copy_xtarg=copy_xtarg,
                                         verbosity=verbosity)
                    # Append this class entry to the list of checked entries
                    checked.append(cls)
                    # Add the name of the class to the class list for this lex if it's not there
                    # Recurse using this class's classes and the remaining classes...
                    # List of lists of superclasses for cls
                    if flatten or self.hierarchical:
                        # Don't bother to inherit from classes if there aren't any
                        clss = self.get_classes(cls, languages=languages, clone=True)
                        # Names for each superclass list
                        clss_names = [cl[0].name for cl in clss if cl]
                        # Add any of the remaining class lists that don't share a name with cls's classes
                        # (but allow repeat inheritance from crosslex entries??)
                        for rem_name, rem in zip(remaining_names, remaining):
                            if rem_name not in clss_names:
                                clss.append(rem)
                        self.inherit1language(orig_lex, l, dimensions, classes=clss,
                                              checked=checked[:], add_entries=add_entries,
                                              languages=languages,
                                              reverse=reverse, is_source=is_source,
                                              process=process, copy_xtarg=copy_xtarg,
                                              flatten=flatten, between=between,
                                              src_language=src_language,
                                              verbosity=verbosity)
