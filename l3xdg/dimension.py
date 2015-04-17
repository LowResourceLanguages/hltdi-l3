#   Implementation of dimensions and principles.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010, 2011, 2012, 2013, 2014
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
# 2010.08.18
# -- Created.
# 2010.08.21
# -- Principle classes for creating variables (problem and node) and
#    constraints (only TreePrinciple implemented so far).
# 2010.08.22
# -- ValencyPrinciple, AgreementPrinciple, OrderPrinciple added.
# 2010.08.27
# -- Interface dimensions added.
# -- LinkingEndPrinciple added.
# 2010.09.05
# -- GroupPrinciple finished (it seems).
# 2010.09.24
# -- Fixed bug in GroupPrinciple.
#    Nodes that are possibly in groups (because at least one
#    entry's group id is not 0) but that have no groupout attribs
#    still need to be constrained: their group id must be in
#    the union of their mothers' group ids.
# 2010.10.17
# -- Syntax dimension: combines ID and LP.
# 2010.10.19
# -- Minor fixes in interface dimensions.
# 2010.10.23
# -- Dimension names, other than for semantic dimensions, changed to
#    lg-dim, e.g., "am-syn"
# 2010.10.24
# -- LinkingDaughterEndP implemented.
# 2010.10.29
# -- Semantics dimensions and principles have no language. Arc
#    labels are associated directly with the dimension.
# 2010.10.31
# -- Solved the problem of irrelevant seq variables in lexical
#    selection constraints with the new det_seqs option on IntSelection
#    (in constraint.py).
# -- OrderP augmented so that it works for generation/translation as well
#    (seemingly).
# 2010.11.13
# -- Government Principle, requiring numerous changes in constraint and
#    variable. Seems to work for Amharic case.
# 2010.12.26
# -- Agr Principle, formerly (and still) part of Agreement Principle,
#    required for Semantic dimension, which needs the agreement variables
#    for IFAgreement
# 2010.12.29
# -- IFAgreement Principle: for agreement between features on multiple
#    dimensions
# 2011.01.01
# -- Various changes to Agr and Agreement Principles
#    1 Agr vars are created for a node, feature pair only if some entry for the
#      node has a value for the feature.
#    2 For each node, feature pair a selection contrainst determined
#      the *options* for the agr values (an SVar whose name ends in 'opt').
#    3 A IVMemberSV constraint relates the agr var (an IVar) to the option
#      SVar.
#    2 and 3 eliminate the need for "irrelevant" agreement features and the
#    det_seq option for UnionSelection in constraint.py.
# 2011.01.16
# -- Fixed bug in AgreementP and AgrP concerning lexical ambiguity when one
#    entry had no value for a given feature
# 2011.02.06
# -- Removed () from sets of agreement features (in AgrP, AgreementP; also
#    affecting GovernmentP)
# 2011.02.10-14
# -- Incorporated empty nodes into ValencyP, TreeP, AgrP, AgreementP, OrderP,
#    LinkingDaughterEndP
#    Still to do: LinkingEndP, GroupP, IFAgreementP
# 2011.02.27
# -- Changes to OrderP to accommodate deleted nodes (*after* EOS punctuation
#    node).
# 2011.03.04
# -- Still the problem of empty and zero nodes ending up in the same slot
#    so that there are multiple spurious outputs:
#    I cleaned the house -> ቤቱን ጠረግኩት . zero I
#                        -> ቤቱን ጠረግኩት . I zero
# 2011.03.08
# -- Problem of deleted node order fixed by constraining order to be the
#    order of the corresponding node indices.
# 2011.03.28
# -- Created DAG Disjoint Daughter Principle, a subclass of Graph Principle (Debusmann diss: 149).
# 2011.04.10
# -- Created EmptyNode Principle, forcing empty nodes to have as their mother either the EOS node
#    (if they're "unused" (deleted)) or their "source" (mother) node.
# 2011.04.11
# -- Created ClimbingPrinciple (Debusmann 77, 139).
# 2011.04.10...
# -- Made final constraint for linking principles "reified" so that its truth can depend on
#    whether the attribute for the principle is empty or not (when more than one lexical
#    entry is possible).
# 2011.04.18
# -- LinkingAboveBelow1or2StartPrinciple. Fixed reified constraints for other linking principles
#    in various ways.
# 2011.04.24
# -- Dimensions and principles have weights governing propagator and variable weights.
#    Principle instantiation happens outside of dimension constructor.
# 2011.05.17
# -- ComplexEmptyNodeP for empty nodes such as the ones created for prepositions in
#    Qu->Es.
# 2011.05.20
# -- CrossGovernP for government where the arc label and daughter agreement are on different
#    dimensions (as for semantic peripheral roles -> case marking in languages such as Qu).
# 2011.06.01
# -- Added GovernP to Semantics to handle selectional constraints (like SUFFER's arg2 must
#    be a CONDITION; 'cat' feature).
# 2011.11.29
# -- By checking lexical valency constraints before assigning GraphPrinciple variables and
#    propagators, lots can be avoided (variables are determined; propagators are not created).
# -- ForestPrinciple created to test possible of chunking (not requiring nodes to have
#    mothers).
# 2011.12.03
# -- LinkingMotherEndP added (used for IDSem prepositional modifiers of nouns: 'mod' in lexicon).
# 2011.12.06
# -- Fixed ComplexEmptyNodeP to work with reverse ComplexEmptyNodes.
# 2011.12.08
# -- LinkingBelowStartP added (needed for semantics of Spanish personal 'a').
# 2011.12.09
# -- More changes to ComplexEmptyNodeP to relax the constraints for reverse ComplexEmptyNodes.
#    Now the empty node is constrained to have as its mother either its "trigger node" or
#    the EOS node.
# 2011.12.17
# -- Fixed problem with GovernmentP; it needed to apply to empty nodes as well as real nodes.
# 2011.12.22
# -- Patterns and unification eliminated.
# 2012.02.22
# -- Various fixes in groups, especially for constraints related to gids.
# 2012.02.25
# -- EmptyNodePrinciple restricted to source language dimensions.
#    (Before failed on subject empty node in ደከማት -> she is tired.)
# 2012.09.13
# -- In GraphPrinciple, when variables are created, pre_arcs in problem
#    can constrain the out and/or in variables.
# 2012.09.16
# -- Fixes to pre_arcs.
# -- Fixes in GraphPrinciple that allow generation to work with pre_arcs
#    (with propagators, already worked with projectors).
# 2012.09.23
# -- Fixed GovernmentP so that spurious constraints are not created for
#    features that a node has no government attribute for.
# 2012.09.27
# -- ID dimension is no longer Tree, but DAGDisjDaugh, so that relative
#    pronouns can have incoming antecedent and argument arcs.
# -- New IDLP interface principle, LinkingBelowEnd, similar to LinkingBelowStart,
#    to constrain the antecedent arc from a relative clause head noun to
#    be within the relative clause
# 2012.09.28
# -- New IDSem interface principle, LinkingAboveBelowStart, similar to
#    LinkingAboveBelow1Or2Start, except that intermediate node on dimension
#    must be the daughter (not the granddaughter) of the end node. This
#    correctly gets the relation between subject and arg1 (at least for Es).
# 2012.10.04
# -- EmptyNode principle changed so that it can include multiple mothers,
#    including antec arcs (node's mothers are either a del arc or the
#    node's source and possibly an antec arc).
# 2012.11.19
# -- GroupPrinciple changed to have separate group variables, etc. for each
#    language.
# 2012.12.10
# -- AgreementPrinciple changed to include () in possible value for daughter
#    agreement variables when some or all of entries have no value for
#    for the agr feature.
# 2013.04.05
# -- IFAgreementPrinciple takes into consideration agr_maps dict for
#    source language.
# 2013.04.18-21
# -- New principle implemented: ArcAgreementP.
#    This permits an agreement feature to have a value that depends on
#    whether or not there is an outgoing arc with a particular label,
#    for example, Spanish and English negative verbs.
# 2013.05.20
# -- IFAgreementPrinciples changed to include agr_maps dicts in both
#    directions.
# 2013.05.27
# -- Fixed the way cardinality range is figured for nodes with different
#    entries in ValencyP.
# 2013.06.03
# -- New principle, CrossOrderEqP, to constrain order of nodes in
#    one dimension to be the same as another, in practice (so far),
#    to preserve SL chunk order in TL.
# -- Principles have an applies field. Only if is is True is
#    make_constraints() called in XDG. True by default for single dimension
#    principles, False by default for IFPrinciples.
# 2013.06.05
# -- Default feature value (DFLT_FV = (0,)) included in lists of possible
#    values in AgreementP and GovernmentP. Currently () is also added;
#    is this necessary anymore??
# 2013.06.08
# -- Simplification of possible values for label pair orders in OrderP and
#    CrossOrderEqP: based on possible daughters for each node.

# Principles create variables and constraints, so we need those
# modules.

from .constraint import *
from .utils import *
import itertools

# Maximum number of edges out of a node with a given label.
MAX_LABELS = 4
MAX_CARD = 8

# Default feature value when an entry has no value
DFLT_FV = (0,)
DFLT_FV_SET = {(0,)}

class Dimension:
    """Abstract class for XDG dimensions."""

    def __init__(self, language, problem, abbrev='',
                 weight=1, princ_classes=None, project=False):
        """
        @param language:  the language for the dimension, needed for
                          implementation of constraints
        @type  language:  Language
        @param problem:   the constraint satisfaction problem
        @type  problem:   XDGProblem
        @param weight:    weight governing whether the dimension is "weakened".
        """
        self.language = language
        prefix = ''
        if language:
            langabb = language.abbrev
            if langabb != 'sem':
                prefix = langabb + '-'
        self.abbrev = prefix + (abbrev or self.__class__.abbrev)
        self.problem = problem
        self.dstore = problem.dstore
        self.weight = weight
        # Principle classes
        self.princ_classes = princ_classes or []
        self.principles = []
        self.project = project

    def __repr__(self):
        return '{}:{}'.format(self.abbrev, self.problem)
        
    def get_principles(self):
        """Return all principles."""
        return self.principles

    def inst_principles(self, princ_classes):
        self.principles = [pc(self.problem, self, project=self.project) for pc in princ_classes if pc in self.princ_classes]

    def instantiate_princs(self):
        self.principles = [pc(self.problem, self, project=self.project) for pc in self.princ_classes]

    def has_principle(self, princ_class):
        """Does this dimension have a principle of a particular class?
        @param  princ_class: a principle class
        @type   princ_class: class
        @return: whether this principle is among the dimension's principles
        @rtype:  boolean
        """
        return princ_class in [princ.__class__ for princ in self.principles]

class ArcDimension(Dimension):
    """
    Abstract class for dimensions with arcs, such as syntax and semantics.

    These have the valency and group arc principles, but not necessarily tree, order, or agreement.
    """

    def __init__(self, language, problem, abbrev='',
                 weight=1, princ_classes=None, project=False):
        Dimension.__init__(self, language, problem, abbrev=abbrev or self.__class__.abbrev,
                           weight=weight, princ_classes=princ_classes, project=project)
        self.arc = True

    def set_labels(self):
        """Assign arc labels for the language."""
        # Strip off the language prefix if there is one
        self.labels = self.language.labels.get(self.abbrev)

class IFDimension(Dimension):
    """Abstract class for interface dimensions, such as IDLP. These have two 'sub'-dimensions."""

    def __init__(self, language=None, problem=None, dim1='', dim2='', abbrev='', weight=1,
                 dimclass1=None, dimclass2=None, princ_classes=None,
                 # whether the two dimensions are in different languages
                 cross=True,
                 project=False):
        """
        dimclass1, dimclass2: classes of subdimensions.
        """
        Dimension.__init__(self, language, problem, abbrev=abbrev or self.__class__.abbrev,
                           weight=weight, princ_classes=princ_classes, project=project)
        self.arc = False
        self.dim1 = dim1
        self.dim2 = dim2
        self.dimclass1 = dimclass1
        self.dimclass2 = dimclass2
        self.cross = cross
        
class Syntax(ArcDimension):
    """Class for the syntax dimension; combines ID and LP. Used in chunking."""

    abbrev = 'syn'

    def __init__(self, language=None, problem=None, abbrev='', weight=1,
                 project=False):
        """Create arc label list and principle groups."""
        ArcDimension.__init__(self, language, problem, abbrev=abbrev, weight=weight,
                              project=project,
                              princ_classes=[TreeP, ValencyP, OrderP,
                                             ProjectivityP,
                                             AgreementP,
                                             GovernmentP,
#                                             DaughAgreementP,
                                             ArcAgreementP,
                                             EmptyNodeP,
                                             GroupP])
        self.set_labels()
        if not self.labels:
            # Default arc labels
            self.labels = ['sb', 'ob', 'adv', 'det', 'adj', 'prp', 'pob', None]
                             
class ID(ArcDimension):
    """Class for the immediate dominance dimension."""

    abbrev = 'id'

    def __init__(self, language=None, problem=None, abbrev='', weight=1,
                 project=False):
        """Create arc label list and principle groups."""
        ArcDimension.__init__(self, language, problem, abbrev=abbrev, weight=weight,
                              project=project,
                              princ_classes=[DAGDisjDaughP,
#                                          TreeP,
                                             ValencyP, AgreementP, GovernmentP,
                                             ArcAgreementP,
                                             EmptyNodeP, GroupP])
        self.set_labels()
        if not self.labels:
            # Default arc labels
            self.labels = ['sb', 'ob', 'adv', 'det', 'adj', 'prp', 'pob', None]
        # GovernmentP has to follow AgreementP
#                            CrossAgreementP

class LP(ArcDimension):
    """Class for the linear precedence dimension."""

    abbrev = 'lp'

    def __init__(self, language=None, problem=None, abbrev='', weight=1,
                 project=False):
        """Create arc label list and principle groups."""
        ArcDimension.__init__(self, language, problem, abbrev=abbrev, weight=weight,
                              project=project,
                              princ_classes=[TreeP, ValencyP, ProjectivityP, OrderP])
        self.set_labels()
        if not self.labels:
            # Default arc labels
            self.labels = ['adjf', 'compf', 'detf', 'fadvf', 'lbf', 'mf1', 'mf2', 'nf', 'padjf',
                           'padvf', 'prepcf', 'rbf', 'relf', 'root', 'rprof', 'tadvf', 'vf', 'vvf', None]

class SemDimension(Dimension):
    """Dimension that belongs to all languages (self.language=SEMANTICS)."""
    
    def __init__(self, language=None, problem=None, abbrev='', weight=1,
                 princ_classes=None,
                 project=False):
        ArcDimension.__init__(self, language, problem=problem, abbrev=abbrev, weight=weight,
                              princ_classes=princ_classes,
                              project=project)
                             
class Semantics(ArcDimension, SemDimension):
    """Class for the semantics dimension, belongs to all
    languages, so language=None."""

    abbrev = 'sem'

    def __init__(self, language=None, problem=None, abbrev='', weight=1, project=False):
        """Create arc label list and principle groups."""
        SemDimension.__init__(self, language, problem=problem, abbrev=abbrev, weight=weight,
                              princ_classes=[DAGDisjDaughP, ValencyP, AgreementP, GovernmentP],
                              project=project)
        self.set_labels()
        if not self.labels:
            # No language to get labels from.
            self.labels = ['arg1', 'arg2', 'arg3', 'del', 'vmod', 'nmod', 'loc', 'coref', 'root']

class SynSem(IFDimension):
    """Class for the syntax-semantics interface."""

    abbrev = 'synsem'

    def __init__(self, language=None, problem=None, sem=None, syn=None, abbrev='', weight=1):
        IFDimension.__init__(self, language, problem, sem, syn, abbrev=abbrev, weight=weight,
                             dimclass1=Syntax, dimclass2=Semantics,
                             princ_classes=[LinkingEndP, IFAgreementP],
                             cross=True)

class SynSyn(IFDimension):
    """Class for cross-language Syn-Syn interface."""

    abbrev = 'synsyn'

    def __init__(self, language=None, problem=None, id1=None, id2=None, abbrev='', weight=1):
        IFDimension.__init__(self, language, problem, id2, id1, abbrev=abbrev, weight=weight,
                             dimclass1=Syntax, dimclass2=Syntax,
                             cross=True,
                             # some linking principles may not be needed
                             princ_classes=[LinkingEndP, LinkingDaughterEndP, LinkingMotherEndP,
                                            LinkingAboveBelowStartP, LinkingBelowStartP,
#                                            LinkingAboveEndP, LinkingAboveBelow1or2StartP,
                                            IFAgreementP,
                                            CrossOrderEqP,
#                                            CrossGovernmentP,
                                            ComplexEmptyNodeP
                                            ])

class IDID(IFDimension):
    """Class for cross-language ID-ID interface."""

    abbrev = 'idid'

    def __init__(self, language=None, problem=None, id1=None, id2=None, abbrev='', weight=1):
        IFDimension.__init__(self, language, problem, id2, id1, abbrev=abbrev, weight=weight,
                             dimclass1=ID, dimclass2=ID,
                             cross=True,
                             # some of these may not be needed
                             princ_classes=[LinkingEndP, RevLinkingEndP, LinkingDaughterEndP,
                                            LinkingAboveEndP, LinkingAboveBelow1or2StartP,
                                            LinkingBelowStartP,
                                            LinkingAboveBelowStartP,
                                            LinkingMotherEndP,
                                            IFAgreementP,
                                            ComplexEmptyNodeP,
                                            CrossGovernmentP
                                            ])

class IDSem(IFDimension):
    """Class for the ID-semantics interface."""

    abbrev = 'idsem'

    def __init__(self, language=None, problem=None, sem=None, syn=None, abbrev='', weight=1):
        IFDimension.__init__(self, language, problem, sem, syn, abbrev=abbrev, weight=weight,
                             dimclass1=ID, dimclass2=Semantics,
                             cross=True,
                             princ_classes=[LinkingEndP, RevLinkingEndP, LinkingDaughterEndP,
                                            LinkingAboveEndP, LinkingAboveBelow1or2StartP,
                                            LinkingBelowStartP,
                                            LinkingAboveBelowStartP,
                                            LinkingMotherEndP,
                                            IFAgreementP,
                                            ComplexEmptyNodeP,
                                            CrossGovernmentP
                                            ])

class IDLP(IFDimension):
    """Class for interface between ID and LP dimensions.
    """

    abbrev = 'idlp'

    def __init__(self, language=None, problem=None, lp_dim=None, id_dim=None,
                 abbrev='', weight=1):
        IFDimension.__init__(self, language, problem, lp_dim, id_dim, abbrev=abbrev, weight=weight,
                             dimclass1=ID, dimclass2=LP,
                             cross=False,
                             princ_classes=[LinkingEndP,
                                            LinkingDaughterEndP,
                                            LinkingBelowEndP,
                                            ClimbingP, BarriersP])

class Principle:
    """Abstract class for all principles."""

    def __init__(self, problem, dimension, short_name="P", project=False,
                 applies=True):
        """applies: boolean specifying whether the principle applies to the problem.
        May be changed in make_variables.
        """
        self.problem = problem
        self.dimension = dimension
        self.language = dimension.language
        # Is the language for this principle the input language of the problem or semantics?
        self.is_input = not self.language or (self.language == self.problem.language)
        self.dstore = problem.dstore
        self.short_name = short_name
        self.weight = self.dimension.weight
        # We need a list of associated propagators, at least for debugging
        self.propagators = []
        # OK, and a list of associated variables, for debugging too
        self.variables = []
        # Prefix for variable names
        self.var_pre = '{0}|{1}:'.format(self.dimension.abbrev, self.short_name)
        self.project = project
        self.applies = applies
#        print('Created', self, 'with weight', self.weight)

    def __repr__(self):
        # Same as variable prefix string
        return '{}|{}'.format(self.dimension.abbrev, self.short_name)

    def get_label_daughs(self, node, nodedimD=None):
        if not nodedimD:
            nodedimD = self.get_nodedimD(node)
        return [nodedimD['outvars'][label][0] for label in self.get_arc_labels()]
        
    def get_nodedimD(self, node):
#        print('Getting nodedimD, dim {}, node.dims {}'.format(self.dimension, node.dims.keys()))
        return node.dims[self.dimension]
        
    def get_entrydim(self, node, index):
        return node.entries[index].dims.get(self.dimension.abbrev, None)

    def get_problemdimD(self):
        return self.problem.dims[self.dimension]

    def get_arc_labels(self):
        return self.dimension.labels

    def get_n_arc_labels(self):
        return len(self.get_arc_labels())
        
    def add_propagator(self, propagator):
        propagator.set_weight(self.weight)
        self.problem.add_propagator(propagator)
        self.propagators.append(propagator)
        
    def add_derived_propagator(self, propagator):
        propagator.set_weight(self.weight)
        self.problem.add_derived_propagator(propagator)
        self.propagators.extend(propagator.constraints)

    def make_variables(self, proc_direction=0):
        pass

    def make_constraints(self, weight=1, proc_direction=0):
        pass

    def ivar(self, name, domain):
        """Make an IVar for this principle. It gets the principle's weight.
        If the domain contains only one element, make it a DetIVar.
        """
        name = self.var_pre + name
        if len(domain) == 1:
            return DetIVar('{}'.format(name), list(domain)[0])
        else:
            var = IVar(name, init_domain=domain,
                       problem=self.problem, rootDS=self.dstore,
                       weight=self.weight, principle=self)
            self.variables.append(var)
            return var

    def svar(self, name, lower, upper, lower_card=0, upper_card=MAX,
             soft_lower_card=None, soft_upper_card=None):
        """Make an SVar for this principle. It gets the principle's weight."""
        name = self.var_pre + name
        # if the variable can already be determined, make a DetSVar instead
        if lower == upper:
            return DetSVar(name, lower)
        var = SVar(name, lower_domain=lower, upper_domain=upper,
                   lower_card=lower_card, upper_card=upper_card,
                   soft_lower_card=soft_lower_card,
                   soft_upper_card=soft_upper_card,
                   problem=self.problem, rootDS=self.dstore,
                   weight=self.weight, principle=self)
        self.variables.append(var)
        return var

class IFPrinciple(Principle):
    """Abstract class for interface principles."""

    def __init__(self, problem, dimension, short_name='IF', reverse=False, project=False,
                 applies=True):
        Principle.__init__(self, problem, dimension, short_name=short_name, project=project,
                           applies=applies)
        self.reverse=reverse

    def get_arc_labels(self, dim):
        """Get the arc labels for one or the other dimension."""
        return dim.labels

    def get_label_daughs(self, node, dim=None, nodedimD=None):
        if not nodedimD:
            nodedimD = node.dims[dim]
        return [nodedimD['outvars'][label][0] for label in self.get_arc_labels(dim)]
        
    def get_label_moths(self, node, dim=None, nodedimD=None):
        if not nodedimD:
            nodedimD = node.dims[dim]
        return [nodedimD['invars'][label][0] for label in self.get_arc_labels(dim)]

    def get_language2(self):
        return self.dimension.dim2.language
        
    def get_language1(self):
        return self.dimension.dim1.language

    def init_constraints(self, attrib):
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1 if not self.reverse else self.dimension.dim2
        dim2 = self.dimension.dim2 if not self.reverse else self.dimension.dim1
        # Values for attrib ('arg', etc.) recorded from lexical entries
        # $$ Do this instead in Language.finalize()??
        attrib_values = self.language.lex_attribs.get(attrib, [])
        label_language = dim1.language
        # Possible attrib values converted to set of ints for dim1
        attrib_values = [set([label_language.get_label_int(l, dim1.abbrev) for l in v]) for v in attrib_values]
        self.attrib_values = set().union(*attrib_values)

### Principles

## Still to do: merge2

class GraphP(Principle):
    """All graphs use the same mother, daughter, nodes, and roots variables
    and have most of the same constraints."""

    def __init__(self, problem, dimension, short_name='GP', project=False):
        Principle.__init__(self, problem, dimension, short_name=short_name, project=project)

    def make_variables(self, proc_direction=0):
        """Since GraphP always applies to the dimensions it's associated with, applies is
        not affected by this method."""
        problem = self.problem
        probdimD = self.get_problemdimD()
        abbrev = self.dimension.abbrev
        pre_arcs = problem.pre_arcs.get(abbrev)
#        if pre_arcs:
#            print('{} making variables, pre arcs {}'.format(self, pre_arcs))
        # Make roots variable for this dimension
        probdimD['rootsvar'] = self.svar('roots',
                                         set(), problem.max_set, lower_card=1, upper_card=1)
        # Make nodes set variable; works for all dimensions;
        # include all empty nodes as "real" nodes
        problem.nodesvar = DetSVar('nodes', problem.all_indices)
#        innone = 0, outnone = 0
        for node in problem.get_nodes():
            node_index = node.index
            abbrev = self.dimension.abbrev
            nodedimD = self.get_nodedimD(node)

            # out and in vars are needed for graph principles as well as valency
            nodedimD['outvars'] = {}
            nodedimD['invars'] = {}                    
            ## Edge label (label-specific daughter, mother) variables
            for label in self.get_arc_labels():
                # For each of out and in there are two set variables, one (index 0)
                # for the indices of the nodes on the other end of links with the labels
                # and one (index 1) for the possible cardinalities of the first.
                # But check to see whether these can be determined variables by looking
                # at the cardinality constraints for all entries.
                pre_arc = None
                do_pre_arc = False
                if pre_arcs:
                    pre_arcs1 = pre_arcs.get(label)
                    if pre_arcs1:
                        for pre_arc in pre_arcs1:
                            if node_index in pre_arc:
                                do_pre_arc = True
                                # If this node's index is the first in pre_arc, it's the mother
                                pre_arc_mother = pre_arc.index(node_index) == 0
                                arc_other = pre_arc[1] if pre_arc_mother else pre_arc[0]
#                        print('node {}, label {}, mother {} other {}'.format(node, label, pre_arc_mother, arc_other))
                # Out variable to daughters on arcs with this label
                low, high = self._label_card(node, abbrev, label, 'out')
                cvar = None
                if (low, high) == (0, 0):
                    lvar = EMPTY
                    if not self.project:
                        cvar = ZERO_SET
                else:
                    if do_pre_arc and pre_arc_mother:
                        # A pre arc is specified and this node is the mother of that arc.
                        # This constrains the lower bound of the variable.
                        if high == 1:
                            # The value can be determined
                            lvar = DetSVar('{}{}D'.format(node_index, label), {arc_other})
                        else:
                            lvar = self.svar('{}{}D'.format(node_index, label),
                                             {arc_other}, problem.all_indices - {node_index}, low, high)
                    else:
                        lvar = self.svar('{}{}D'.format(node_index, label),
                                         set(), problem.all_indices - {node_index}, low, high)
                    if not self.project:
                        cvar = self.svar('|{}{}D|'.format(node_index, label),
                                         set(), set(range(low, high+1)), lower_card=1)
                nodedimD['outvars'][label] = (lvar, cvar)
                # In variable to mothers on arcs with this label
                low, high = self._label_card(node, abbrev, label, 'in')
                if (low, high) == (0, 0):
                    lvar = EMPTY
                    if not self.project:
                        cvar = ZERO_SET
                else:
                    if do_pre_arc and not pre_arc_mother:
                        # A pre arc is specified and this node is the daughter of that arc.
                        # This constrains the lower bound of the variable.
                        if high == 1:
                            # The value can be determined
                            lvar = DetSVar('{}{}M'.format(node_index, label), {arc_other})
                        else:
                            lvar = self.svar('{}{}M'.format(node_index, label),
                                             {arc_other}, problem.all_indices - {node_index}, low, high)
                    else:
                        lvar = self.svar('{}{}M'.format(node_index, label),
                                         set(), problem.all_indices - {node_index}, low, high)
                    if not self.project:
                        cvar = self.svar('|{}{}M|'.format(node_index, label),
                                         set(), set(range(low, high+1)), lower_card=1)
                nodedimD['invars'][label] = (lvar, cvar)
            ## Graph vars not specific to particular arc labels
            # Descendants
            # Immediate daughters
            nodedimD['daughvar'] = self.svar('{}D'.format(node_index),
                                             set(), problem.all_indices - {node_index})
            # All descendants
            nodedimD['downvar'] = self.svar('{}d'.format(node_index),
                                            set(), problem.all_indices - {node_index})  # no cycles
            # All descendants + this node
            nodedimD['eqdownvar'] = self.svar('{}=d'.format(node_index),
                                              {node_index}, problem.all_indices)
            # Ancestors
            # mothvar is defined differently for DAGDisjDaughP and Tree P
            # All ancestors
            nodedimD['upvar'] = self.svar('{}m'.format(node_index),
                                          set(), problem.all_indices - {node_index})  # no cycles
            # All ancestors + this node
            nodedimD['equpvar'] = self.svar('{}=m'.format(node_index),
                                            {node_index}, problem.all_indices)

    def _label_card(self, node, dim_abbrev, label, direction):
        """Lowest low and highest high cardinality for label in direction ('in' or 'out')
        from/to node; all entries are examined.
        """
        minim = 1
        maxim = 0
        for entry in node.entries:
#            minim = 1
#            maxim = 0
            entry_dims = entry.dims
            if dim_abbrev in entry_dims:
#                print('label {}, direction {}, dim {}'.format(label, direction, dim_abbrev))
                low, high, soft_low, soft_high = entry_dims[dim_abbrev].get_label_card_bounds(label, direction)
                minim = min(low, minim)
                maxim = max(high, maxim)
#            if direction == 'in':
#                print('Node {}, entry {}, label {}, minim {}, maxim {}'.format(node, entry, label, minim, maxim))
        # min cannot be greater than max
        if minim > maxim:
            minim = maxim
#            print('minim {} maxim {}'.format(minim, maxim))
        return minim, maxim

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        probdimD = self.get_problemdimD()
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        eqdownvars = [n['eqdownvar'] for n in nodedimDs]
        equpvars = [n['equpvar'] for n in nodedimDs]
        # Constrain rootsvar to be the union of the 'root' mother vars for all nodes
        rootmothers = [self.get_nodedimD(n)['invars']['root'][0] for n in problem.get_nodes()]
        self.add_derived_propagator(Union([probdimD['rootsvar']] + rootmothers, problem=problem))
        for node, nodedimD in zip(problem.get_nodes(), nodedimDs):
            ## Down variables
            daughvar, downvar, eqdownvar = nodedimD['daughvar'], nodedimD['downvar'], nodedimD['eqdownvar']
            # Value of daughvar is the partition of the sets of daughters on each link type;
            # enforces the prohibition of multiple arcs from a node to the same daughter
            labelvars = [lvar for lvar, cardvar in list(nodedimD['outvars'].values())]
            prop = Partition([daughvar] + labelvars, problem=problem)
            self.add_derived_propagator(prop)
            # Determined set variable for the node itself
            nodesetvar = node.dsvar
            # Value of eqdown is the partition of the node and the down of the node;
            # enforces the prohibition of cycles (the node cannot be one of its own descendants)
            self.add_derived_propagator(Partition([eqdownvar, nodesetvar, downvar], problem=problem))
            # Value of down is the UnionSelection of the eqdowns of all nodes
            # with the daughter variable as the selection variable
            prop = UnionSelection(downvar, daughvar, eqdownvars, problem=problem)
            self.add_propagator(prop)
            ## Up variables
            mothvar, upvar, equpvar = nodedimD['mothvar'], nodedimD['upvar'], nodedimD['equpvar']
            # Value of mothvar is the partition of the sets of mothers on each link type;
            # enforces the prohibition of multiple arcs to a node from the same mother
            labelvars = [lvar for lvar, cardvar in list(nodedimD['invars'].values())]
#            print('labelvars {} for {}'.format(labelvars, node))
            self.add_derived_propagator(Partition([mothvar] + labelvars, problem=problem))
            # Value of equp is the partition of the node and the up of the node;
            # enforces the prohition of cycles (the node cannot be one of its own ancestors)
            self.add_derived_propagator(Partition([equpvar, nodesetvar, upvar], problem=problem))
            # Value of up is the UnionSelection of the equps of the mothers
            # with the mother variables as the selection variable
            self.add_propagator(UnionSelection(upvar, mothvar, equpvars, problem=problem))
        # For each pair of nodes, constrain mother and daughter vars
        for node1, node2 in itertools.combinations(problem.get_nodes(), 2):
            index1, index2 = node1.index, node2.index
            dsvar1, dsvar2 = node1.dsvar, node2.dsvar
            dim1D, dim2D = self.get_nodedimD(node1), self.get_nodedimD(node2)
            for label in self.get_arc_labels():
                out1, out2 = dim1D['outvars'][label][0], dim2D['outvars'][label][0]
                in1, in2 = dim1D['invars'][label][0], dim2D['invars'][label][0]
                # Determined SVar representing {index1, index2}
                index_svar = DetSVar('{}{{{},{}}}'.format(self.var_pre, index1, index2), {index1, index2})
                # SVars for intersections of mother and daughters with indices
                # The in and out variables can be determined if there are pre arcs in the problem (XDG)
                if isinstance(out1, Determined):
                    out1value = out1.value or set()
                    out1inters_svar = DetSVar('{}I_{}{}D_{}'.format(self.var_pre, index1, label, index2),
                                              out1value & {index2})
                else:
                    out1inters_svar = self.svar('I_{}{}D_{}'.format(index1, label, index2),
                                                set(), problem.all_indices - {index1})
                if isinstance(in2, Determined):
                    in2value = in2.value or set()
                    in2inters_svar = DetSVar('{}I_{}{}D_{}'.format(self.var_pre, index1, label, index2),
                                             in2value & {index1})
                else:
                    in2inters_svar = self.svar('I_{}M{}_{}'.format(index2, label, index1),
                                               set(), problem.all_indices - {index2})
                if isinstance(in1, Determined):
                    in1value = in1.value or set()
                    in1inters_svar = DetSVar('{}I_{}M{}_{}'.format(self.var_pre, index2, label, index1),
                                             in1value & {index2})
                else:
                    in1inters_svar = self.svar('I_{}{}M_{}'.format(index2, label, index1),
                                               set(), problem.all_indices - {index1})
                if isinstance(out2, Determined):
                    out2value = out2.value or set()
                    out2inters_svar = DetSVar('{}I_{}{}M_{}'.format(self.var_pre, index2, label, index1),
                                              out2value & {index1})
                else:
                    out2inters_svar = self.svar('I_{}D{}_{}'.format(index1, label, index2),
                                                set(), problem.all_indices - {index2})
                # Intersection of node1's daughters by label and node2's index
                if not isinstance(out1, Determined):
                    self.add_derived_propagator(Intersection([out1inters_svar, out1, dsvar2], problem=problem))
                # Intersection of node2's mothers by label and node1's index
                if not isinstance(in2, Determined):
                    self.add_derived_propagator(Intersection([in2inters_svar, in2, dsvar1], problem=problem))
                # Union of intersections
                if not isinstance(in2, Determined) or not isinstance(out1, Determined):
                    inters_union1 = self.svar('U(D{}M{}/{})'.format(index1, index2, label),
                                              set(), problem.all_indices)
                    self.add_derived_propagator(Union([inters_union1, out1inters_svar, in2inters_svar],
                                                      problem=problem))
                    # Selection constraint: the union of the intersections
                    # is either empty or the set consisting of both indices
                    self.add_propagator(OneSelection(inters_union1, [EMPTY, index_svar], problem=problem))
                ## The other direction
                # Intersection of node1's mothers by label and node2's index
                if not isinstance(in1, Determined):
                    self.add_derived_propagator(Intersection([in1inters_svar, in1, dsvar2], problem=problem))
                # Intersection of node2's daughters by label and node1's index
                if not isinstance(out2, Determined):
                    self.add_derived_propagator(Intersection([out2inters_svar, out2, dsvar1], problem=problem))
                # Union of intersections
                if not isinstance(in1, Determined) or not isinstance(out2, Determined):
                    inters_union2 = self.svar(':U(D{}M{}/{})'.format(index2, index1, label),
                                              set(), problem.all_indices)
                    self.add_derived_propagator(Union([inters_union2, in1inters_svar, out2inters_svar],
                                                      problem=problem))
                    # Selection constraint: the union of the intersections
                    # is either empty or the set consisting of both indices
                    self.add_propagator(OneSelection(inters_union2, [EMPTY, index_svar], problem=problem))

class TreeP(GraphP):

    def __init__(self, problem, dimension, project=False):
        GraphP.__init__(self, problem, dimension, short_name='TP', project=project)

    def make_variables(self, proc_direction=0):
        GraphP.make_variables(self, proc_direction=proc_direction)
        problem = self.problem
        # Mother variable differs for tree and DAG
        for node in problem.get_nodes():
            node_index = node.index
            abbrev = self.dimension.abbrev
            nodedimD = self.get_nodedimD(node)
            lower_card = 0 if node_index == problem.eos_index else 1
            nodedimD['mothvar'] = self.svar('{}M'.format(node_index),
                                            set(), problem.all_indices - {node_index},
                                            # Tree constraint: at most one mother
                                            lower_card=lower_card, upper_card=1)

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        probdimD = self.get_problemdimD()
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        # Value of nodesvar is the partition of roots and all daughters;
        # enforces the prohibition on multiple arcs into nodes (TreePrinciple but not
        # DAGPrinciple) and the requirement that all nodes have incoming arcs
        self.add_derived_propagator(Partition([problem.nodesvar, probdimD['rootsvar']] + \
                                              [n['daughvar'] for n in nodedimDs],
                                              problem=problem))
        GraphP.make_constraints(self, weight=weight, proc_direction=proc_direction)

class DAGDisjDaughP(GraphP):
    """Constrains graph to be a DAG with no more than one arc joining any pair of nodes (Debusmann diss: 149)."""

    def __init__(self, problem, dimension, project=False):
        GraphP.__init__(self, problem, dimension, short_name='DDDP', project=project) 

    def make_variables(self, proc_direction=0):
        GraphP.make_variables(self, proc_direction=proc_direction)
        problem = self.problem
        # Mother variable differs for tree and DAG
        for node in problem.get_nodes():
            node_index = node.index
            abbrev = self.dimension.abbrev
            nodedimD = self.get_nodedimD(node)
            lower_card = 0 if node_index == problem.eos_index else 1
            # Upper cardinality not constrained for DAG
            nodedimD['mothvar'] = self.svar('{}M'.format(node_index),
                                            set(), problem.all_indices - {node_index},
                                            lower_card=lower_card)

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        probdimD = self.get_problemdimD()
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        # Value of nodesvar is the union of roots and all daughters;
        # enforces the requirement that all nodes have incoming arcs
        # (but not the requirement that each node have only one mother; the only difference
        # from TreeP; for TreeP, it is the partition rather than the union).
        self.add_derived_propagator(Union([problem.nodesvar, probdimD['rootsvar']] + \
                                              [n['daughvar'] for n in nodedimDs],
                                          problem=problem))
        GraphP.make_constraints(self, weight=weight, proc_direction=proc_direction)

class ForestP(GraphP):
    """Like a tree except that the nodes var is not the partition of root and all daughters,
    but rather the union of root and all downeqs.
    """

    def __init__(self, problem, dimension, project=False):
        GraphP.__init__(self, problem, dimension, short_name='FP', project=project)

    def make_variables(self, proc_direction=0):
        GraphP.make_variables(self, proc_direction=proc_direction)
        problem = self.problem
        # Mother variable differs for tree and DAG
        for node in problem.get_nodes():
            node_index = node.index
            abbrev = self.dimension.abbrev
            nodedimD = self.get_nodedimD(node)
#            lower_card = 0 if node_index == problem.eos_index else 1
            nodedimD['mothvar'] = self.svar('{}M'.format(node_index),
                                            set(), problem.all_indices - {node_index},
                                            # Forest constraint only; motherless node possible
                                            lower_card=0,
                                            # Tree and Forest constraint
                                            upper_card=1)

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        probdimD = self.get_problemdimD()
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        # Value of nodesvar is the union of roots and all eqdowns;
        # unlike TreePrinciple there is no requirement that all nodes have
        # incoming arcs
        self.add_derived_propagator(Union([problem.nodesvar,
                                           probdimD['rootsvar']] + [n['eqdownvar'] for n in nodedimDs],
                                          problem=problem))
        GraphP.make_constraints(self, weight=weight, proc_direction=proc_direction)

class ProjectivityP(Principle):

    def __init__(self, problem, dimension, project=False):
        Principle.__init__(self, problem, dimension, short_name='PP', project=project) 

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        nodes = problem.get_nodes()
        abbrev = self.dimension.abbrev
        if not self.is_input:
            posvars = [self.get_nodedimD(node)['posvar'] for node in nodes]
        # Projectivity doesn't apply to empty nodes??
        for node in nodes:
            nodedimD = self.get_nodedimD(node)
            eqdownvar = nodedimD['eqdownvar']
            # Convexity must hold for each eqdown variable
            if not self.is_input:
                # For output language, we have to use the values of the position variables in
                # place of node indices; use eqdownvar as a selection variable, posvars
                # as sequence variables to get the position eqdownvar
                pos_eqdownvar = self.svar('{}=dP'.format(node.index),
                                          set(), problem.positions, lower_card=1)
                nodedimD['poseqdownvar'] = pos_eqdownvar
                # Selection constraint for pos_eqdownvar
                sel_constraint = UnionSelection(pos_eqdownvar, eqdownvar, posvars, problem=problem)
                self.add_propagator(sel_constraint)
                proj_constraint = SetConvexity(pos_eqdownvar, problem=problem)
            else:
                proj_constraint = SetConvexity(eqdownvar, problem=problem)
            self.add_propagator(proj_constraint)

class ValencyP(Principle):

    def __init__(self, problem, dimension, project=False):
        Principle.__init__(self, problem, dimension, short_name='VP', project=project) 

    def make_variables(self, proc_direction=0):
        '''No variables created for valency alone.
        Since ValencyP always applies to the dimensions it's associated with, applies is
        not affected by this method.'''
        pass

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        for node in problem.get_nodes():
            lexvar = node.lexvar
            nodedim = self.get_nodedimD(node)
            # List of main vars and seq vars for IntSelection
            main_seqs = []
            for direction in ['out', 'in']:
                cat = 'D' if direction == 'out' else 'M'
                varD = nodedim['outvars'] if direction == 'out' else nodedim['invars']
                # For each arc label, variable pairs are indices of daughters and cardinality
                for label, (labelvar, cardvar) in varD.items():
                    # For each entry, a set representing partial cardinalities
                    cards = [self._entry_label_card(entry, abbrev, label, direction) for entry in node.entries]
#                    if any([x == None for x in cards]):
#                        print('cards {}, abbrev {}, node {}, label {}, direction {}'.format(cards, abbrev, node, label, direction))
                    # Create determined set variables for each cardinality set if we're doing propagator CS
#                    if not self.project:
                    var_name = '{}{}{}/{}'
                    card_det_vars = [DetSVar(var_name.format(label, cat, node.index, i), c) for i, c in enumerate(cards)]
                    main_seqs.append([cardvar, card_det_vars])
                    # Constrain cardinality of the label variable
                    if not isinstance(labelvar, Determined):
                        # Propagator CS
                        if cardvar and not isinstance(cardvar, Determined):
                            self.add_propagator(CardinalitySubset((labelvar, cardvar), problem=problem))
                        # Projector CS
##                        if self.project:
##                            ivar_name = '{}{}{}/{}{}'
##                            lower_ivars = [DetIVar(ivar_name.format(label, cat, node.index, i, '-'), min(card)) \
##                                               for i, card in enumerate(cards)]
##                            upper_ivars = [DetIVar(ivar_name.format(label, cat, node.index, i, '+'), max(card)) \
##                                               for i, card in enumerate(cards)]
##                            lower_cardprop = CardSelection(labelvar, lexvar, lower_ivars, lower=True, problem=problem)
##                            upper_cardprop = CardSelection(labelvar, lexvar, upper_ivars, lower=False, problem=problem)
##                            self.add_propagator(lower_cardprop)
##                            self.add_propagator(upper_cardprop)
            # Constrain cardinality with lexical entry selection constraint
            # With projectors, CardSelection constraints went here, replacing the IntSelection and CardinalitySubset constraints
##            if not self.project: # and not isinstance(lexvar, Determined):
            for cardvar, card_det_vars in main_seqs:
                prop = IntSelection(cardvar, lexvar, card_det_vars, problem=problem)
#                    print('Adding intsel {}'.format(prop))
                self.add_propagator(prop)

    def _entry_label_card(self, entry, dim_abbrev, label, direction):
        """The possible cardinalities for daughters on arcs with label in direction for a dimension in an entry.
        If there is no LexDim for this dimension assume {0} by default.
        """
        entry_dims = entry.dims
        if dim_abbrev in entry_dims:
            label_card = entry_dims[dim_abbrev].get_label_card(label, direction)
#                print('label card {}'.format(label_card))
            return label_card
        else:
            return {0}

class OrderP(Principle):
    """Behavior depends on whether the language is an input language (as for parsing),
    or an output language (as for generation or target language for translation)."""

    def __init__(self, problem, dimension, project=False):
        Principle.__init__(self, problem, dimension, short_name='OP', project=project)
        # Pairs of ints representing labels
        self.max_order_set = set()

    def _make_max_order_set(self, labels=None):
        """Same as in CrossOrderEqP.
        Maximum set of possible order pair tuples; this could be constrained
        a lot more, for example, to exclude pairs that are not possible outgoing
        arcs from the same nodes, like (detf, compf).
        """
        n_labels = len(self.dimension.language.labels[self.dimension.abbrev])
        if not labels:
            labels = range(n_labels+1)
        else:
            labels.add(n_labels)
        return set(itertools.permutations(labels, 2))

    #    def _make_max_order_set(self):
    #        """Maximum set of possible order pair tuples; this could be constrained
    #        a lot more, for example, to exclude pairs that are not possible outgoing
    #        arcs from the same nodes, like (detf, compf).
    #        """
    #        n_order_labels = len(self.language.labels[self.dimension.abbrev])
    #        return set(itertools.permutations(range(n_order_labels+1), 2))

    def make_variables(self, proc_direction=0):
        '''Since OrderP always applies to the dimensions it's associated with, applies is
        not affected by this method.'''
        problem = self.problem
        abbrev = self.dimension.abbrev
        self.arc_labels = self.get_arc_labels()
        # This could be constrained a lot more, for example, to include only
        # pairs that are possible outgoing arcs of the same nodes (for example,
        # not (detf, compf))
#        self.max_order_set = self._make_max_order_set()
#        print('O; dim {}, max order set {}'.format(abbrev, self.max_order_set))
        real_nodes = self.problem.nodes
        empty_nodes = self.problem.empty_nodes
        all_nodes = real_nodes + empty_nodes
        # Create attribute for process (parse, generate, or translate)
        for node in all_nodes:
            node_index = node.index
            nodedimD = self.get_nodedimD(node)
            # Get the maximum order set for this node
            d_labels = [e.dims.get(abbrev).attribs.get('daughs', set()) if abbrev in e.dims else set() for e in node.entries]
            d_labels = set().union(*d_labels)
            nodedimD['dlabels'] = d_labels
            max_order_set = EMPTY
            if d_labels:
#                print('O; dim, {} node {}, d labels {}'.format(abbrev, node, d_labels))
                max_order_set = self._make_max_order_set(labels=d_labels)
#                print('  O; max order set for {}: {}'.format(node, max_order_set))
            if d_labels:
                nodedimD['ordervar'] = self.svar('{}'.format(node_index), set(), max_order_set)
            else:
                nodedimD['ordervar'] = EMPTY
            nodedimD['max_order_set'] = max_order_set
            if not self.is_input:
                # For an output language,
                # create an output position variable for this node
                nodedimD['posvar'] = self.svar('{}pos'.format(node_index),
                                               set(), problem.positions, 1, 1)
                # Create daughter variables by positions instead of indices
                nodedimD['posDvars'] = {}
                d_label_strings = {}
                if d_labels:
                    d_label_strings = {self.language.get_int_label(l, abbrev) for l in d_labels}
                for label in self.arc_labels:
                    if d_labels and label in d_label_strings:
                        nodedimD['posDvars'][label] = self.svar('{}{}PosD'.format(node_index, label),
                                                                set(), problem.positions)
                    else:
                        nodedimD['posDvars'][label] = EMPTY
        if not self.is_input:
            # For an output language, 
            # we need a variable for the indices of the deleted nodes
            eos_node = problem.nodes[problem.eos_index]
            eos_dimD = self.get_nodedimD(eos_node)
#            print('e {}, e.dims {}'.format(eos_node.entries, [e.dims for e in eos_node.entries]))
            d_labels = [e.dims.get(abbrev).attribs.get('daughs') for e in eos_node.entries]
            d_labels = set().union(*d_labels)
            eos_max_order_set = self._make_max_order_set(labels=d_labels)
            self.eos_max_set = eos_max_order_set
            self.delnode_var = eos_dimD['outvars']['del'][0]

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        real_nodes = problem.nodes
        empty_nodes = problem.empty_nodes
        all_nodes = real_nodes + empty_nodes
        posvars = []
        if not self.is_input:
            posvars = [self.get_nodedimD(node)['posvar'] for node in all_nodes]
            # Constrain posvars to be different
            disjoint_constraint = Disjoint(posvars, problem=problem)
#            print('Created disjoint constraint', disjoint_constraint.constraints)
            self.add_derived_propagator(disjoint_constraint)
            # Constrain deleted nodes to appear in the order of their indices
            del_order_constraint = SimplePrecedenceSelection(self.delnode_var, posvars,
                                                             problem=problem,
                                                             maxset=self.eos_max_set)
            self.add_propagator(del_order_constraint)
        for node in all_nodes:
            # Get the maximum order set for this node
            # Only proceed with constraints if the node can have daughters
            nodedimD = self.get_nodedimD(node)
            d_labels = nodedimD['dlabels']
            if d_labels:
                max_order_set = nodedimD['max_order_set']
                #                print('d labels {}'.format(d_labels))
                #                print('max order set {}'.format(max_order_set))
                lexvar = node.lexvar
                ordervar = nodedimD['ordervar']
                # List of daughter variables for each label, and one for '^' (the node's dsvar)
                # These variables are based on indices
                daugh_vars = self.get_label_daughs(node, nodedimD)
                # If this is not an input language dimension, we need to convert them
                # to position variables
                if not self.is_input:
                    pos_daugh_vars = [nodedimD['posDvars'][label] for label in self.arc_labels]
                    # Make a selection constraint mapping daughter indices to daughter positions for each label
                    for index_daugh_var, pos_daugh_var in zip(daugh_vars, pos_daugh_vars):
                        constraint = UnionSelection(pos_daugh_var, index_daugh_var, posvars, problem=problem)
                        self.add_propagator(constraint)
                    daugh_vars = pos_daugh_vars
                    daugh_vars.append(nodedimD['posvar'])
                else:
                    daugh_vars.append(node.dsvar)
                tuple_vars = [self.get_order_tuple_var(node, entry.get_lexdim(abbrev), index, abbrev,
                                                       max_order_set) \
                                  for index, entry in enumerate(node.entries)]
                # the lexical selection constraint determining the set of pairs of ordered label indices
                self.add_propagator(IntSelection(ordervar, lexvar, tuple_vars, problem=problem,
                                                 maxset=max_order_set))
                # the selection constraint controlling the sequencing of daughters
                self.add_propagator(PrecedenceSelection(ordervar, daugh_vars, problem=problem,
                                                        maxset=max_order_set))

    def get_order_tuple_var(self, node, lexdim, entry_index, abbrev, max_order_set):
        """Create a set of order pair constraints and a determined SVar with this set as its value."""
        if lexdim:
            order_lists = lexdim.get_attrib('order')
            if order_lists:
                tuples = set()
                node_index = node.index
                for order_list in order_lists:
                    # Create an order tuple for every pair of labels in order_list
                    tuples1 = [(self.language.get_label_int(x, abbrev), self.language.get_label_int(y, abbrev)) \
                                   for x, y in itertools.combinations(order_list, 2)]
                    for tup in tuples1:
                        if tup in max_order_set:
                            tuples.add(tup)
                            #                    tuples.update(tuples1)
                return DetSVar('{}{}/{}'.format(self.var_pre, node_index, entry_index), tuples)
        # There may be no order constraint for this entry
        return EMPTY

class AP(Principle):
    """Abstract superclass for agreement principles. AgreementP shares AgrP's
    make_variables and make_constraints methods."""

    def __init__(self, problem, dimension, short_name, project=False, applies=True):
        Principle.__init__(self, problem, dimension, short_name=short_name,
                           project=project, applies=applies)
        self.pre_agrs = self.problem.pre_agrs.get(dimension.abbrev)
        
    def _get_agrs(self, node, entry_index, agr):
        """The agrs values for feature agr in node's entry with entry_index,
        default value if nothing there.
        """
        dim = self.get_entrydim(node, entry_index)
        if dim:
            return dim.attribs.get('agrs', {}).get(agr, set())
        return set()

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        for node in problem.get_nodes():
            node_index = node.index
            nodedimD = self.get_nodedimD(node)
            # Dict of agreement variables by feature
            agrvars = {}
            nodedimD['agrvars'] = agrvars
            agrvalues = {}
            nodedimD['agrvalues'] = agrvalues
            for feat in self.language.agrs.keys():
                # If there's a prespecified value for the feature, use this
                if self.pre_agrs:
                    pre_agr = self.pre_agrs.get(feat)
                    # [(node_index, value), ...]
                    if pre_agr:
                        for pre_index, pre_value in pre_agr:
                            if pre_index == node_index:
                                agrvars[feat] = DetIVar('{}{}{}'.format(self.var_pre, node_index, feat), pre_value)
                entry_agrs = [self._get_agrs(node, index, feat) for index in range(len(node.entries))]
                entry_agrs = set(itertools.chain(*entry_agrs))
                # Somehow rank the possible agreement feature values
                agr_vals = [entry.get_dimattrib(abbrev, 'agrs').get(feat, DFLT_FV_SET) for entry in node.entries]
#                print('Node {}, feat {}, agr_vals {}'.format(node, feat, agr_vals))
                agr_vals = list(itertools.chain.from_iterable(agr_vals))
# set().union(*agr_vals)
                # All possible values
                agrvalues[feat] = agr_vals
                if entry_agrs and feat not in agrvars:
                    # agrvar not created because of pre agrs
                    agrvars[feat] = self.ivar('{}{}'.format(node_index, feat), agr_vals)

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        # list of dimension dicts for each node
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        # dict of node feature variable lists indexed by feature
        featvars = {}
        for feat in self.language.feats:
            featvars[feat] = [nodedimD['agrvars'].get(feat, ZERO_TUPLE) for nodedimD in nodedimDs]

        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            agrvarD = nodedimD['agrvars']
            agrvaluesD = nodedimD['agrvalues']
            lexvar = node.lexvar
            index = node.index
            # For each agr feature (e.g., sbj), make a lexical selection constraint
            for feat in self.language.feats:
                agrvar = agrvarD.get(feat)
                if agrvar:
                    agr_vals = [entry.get_dimattrib(abbrev, 'agrs').get(feat, {()}) for entry in node.entries]
                    agr_vars = []
                    agr_val_set = agrvaluesD[feat]
#                    print('Node {}, feat {}, agr_val_set {}, agr_vals {}'.format(node, feat, agr_val_set, agr_vals))
                    # Figure out what default value to use for entries that don't have the feature
                    if all([len(x) <= 1 for x in agr_val_set]):
                        dflt_var = ZERO_TUPLE_SET
                    else:
                        dflt_var = EMPTY_TUPLE_SET
                    for i, val in enumerate(agr_vals):
                        if val != {()}:
                            # Determined variable with val as value
                            vari = DetSVar('{}{}{}/{}'.format(self.var_pre, index, feat, i), val)
                        else:
                            vari = dflt_var
#EMPTY_TUPLE_SET
                        agr_vars.append(vari)
#                    print('agr vars', agr_vars, 'agrvar', agrvar)
                    # Is any of this necessary if agrvar is determined??
                    agr_option_var = self.svar('{}{}Aopt'.format(index, feat), set(), agr_val_set)
                    # Selection constraint for the agr feature
                    self.add_propagator(IntSelection(agr_option_var, lexvar, agr_vars, problem=problem))
                    # Constrain the agr variable for feature feat to be within the value of agr_option_var
                    # as long as both are not already determined
                    if not agrvar.is_determined() or not agr_option_var.is_determined():
                        self.add_propagator(IVMemberSV([agrvar, agr_option_var], problem=problem))

class AgrP(AP):
    """Only creates agr variables and selection constraint for each one."""

    def __init__(self, problem, dimension, project=False):
        AP.__init__(self, problem, dimension, 'AgrP')

class AgreementP(AP):

    def __init__(self, problem, dimension, project=False):
        AP.__init__(self, problem, dimension, short_name='AgreeP')
        self.maxset = set(self.language.agree)

    def _get_agrees(self, node, entry_index):
        """The agrs values for feature agr in node's entry with entry_index,
        default value if nothing there.
        """
        dim = self.get_entrydim(node, entry_index)
        if dim:
            return dim.attribs.get('agree', set())
        return set()

    def _entry_dim_agree(self, entry, abbrev):
        """Get the agreement constraint for the LexDim of an entry. If none, the default is set()."""
        entry_dims = entry.dims
        if abbrev not in entry_dims:
            return set()
        return entry_dims[abbrev].get_agree()
        
    def make_variables(self, proc_direction=0):
        # Make Agr variables
        AP.make_variables(self, proc_direction=proc_direction)
        # Make Agreement variables
        problem = self.problem
        abbrev = self.dimension.abbrev
        for node in problem.get_nodes():
            node_index = node.index
            nodedimD = self.get_nodedimD(node)
            entry_agrees = [self._get_agrees(node, index) for index in range(len(node.entries))]
            entry_agrees = set(itertools.chain(*entry_agrees))
            # agreevar's values are pairs of ints indexing variables in (1) list of agrvars and (2) list of labeldfeatvars that
            # should be equal.
            nodedimD['agreevar'] = self.svar('{}'.format(node_index), set(), set(self.language.agree))
#            print('Agree var', nodedimD['agreevar'])
            # Arc label / daughter feature variables
            # Length of labeldfeatvars is number of possible label-dfeat combinations
            labeldfeatvars = []
            nodedimD['labeldfeatvars'] = labeldfeatvars
            for label, dfeat in self.language.labeldfeats:
                if any([agree[0] == label and agree[2] == dfeat for agree in entry_agrees]):
#                    print('node {}, dfeat {}, label {}, entry agrees {}'.format(node_index, dfeat, label, entry_agrees))
                    values = self.language.agrs[dfeat]
                    values_copy = values.copy()
                    # Added 2012.12.10, to handle the case where some or all values for feature are non-existent
                    # in different entries (by adding () to the possible values in those cases)
#                    entry_agrs = [self._get_agrs(node, index, dfeat) for index in range(len(node.entries))]
#                    print('Entry agrs for {}: {}/{}/{}'.format(entry_agrs, node, label, dfeat))
#                    if set() in entry_agrs:
                    values_copy.add(())
                    if DFLT_FV not in values_copy:
                        values_copy.add(DFLT_FV)
#                    print('values {}'.format(values_copy))
                    svar = self.svar('{}{}D{}'.format(node_index, label, dfeat),
                                     set(), values_copy, 0, 1)
#                    print(' svar: {}'.format(svar))
                else:
                    svar = EMPTY
#                    print('node {}, dfeat {}, label {}, empty svar {}'.format(node_index, dfeat, label, svar))
#ZERO_TUPLE_SET
                labeldfeatvars.append(svar)

    def make_constraints(self, weight=1, proc_direction=0):
        # Make Agr constraints
        AP.make_constraints(self, weight=weight, proc_direction=proc_direction)
        # Make Agreement constraints
        problem = self.problem
        abbrev = self.dimension.abbrev
        # list of dimension dicts for each node
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        # dict of node feature variable lists indexed by feature
        featvars = {}
        for feat in self.language.feats:
            featvars[feat] = [nodedimD['agrvars'].get(feat, ZERO_TUPLE) for nodedimD in nodedimDs]
#            print('Featvars for {}: {}'.format(feat, featvars[feat]))
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            agrvarD = nodedimD['agrvars']
            lexvar = node.lexvar
            index = node.index
            # Make lexical selection constraint for agreement variable
            agreevar = nodedimD['agreevar']
            agree_vals = [self._entry_dim_agree(entry, abbrev) for entry in node.entries]
#            print("dim {} {}; agree vals {}".format(self.dimension, index, agree_vals))
            agree_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), val) for i, val in enumerate(agree_vals)]
            self.add_propagator(IntSelection(agreevar, lexvar, agree_vars, problem=problem))
#            print('Agreevar {}'.format(agreevar))
            # For each label, constrain the label daughter feature variables to be the union of the features
            # of the daughters on each label.
            labeldfeatvars = nodedimD['labeldfeatvars']
            for ldvar, (label, dfeat) in zip(labeldfeatvars, self.language.labeldfeats):
                # Make a copy of featvars so we can modify it
                seqvars = featvars[dfeat][:]
                # Replace the feat variable for node index with empty tuple; the node can't have itself
                # as a daughter
                seqvars[index] = EMPTY_TUPLE
                # Only make a constraint for variables associated with possible values of agree for this node
                if not isinstance(ldvar, Determined):
                    ldvarU = UnionSelection(ldvar, nodedimD['outvars'][label][0],
                                            seqvars, problem=problem, 
                                            maxset=self.language.agrs[dfeat]
#                                                       pattern=True
                                            )
#                    print(' index', index, 'ldvar', ldvar, 'label', label, 'dfeat', dfeat, 'seqvars', seqvars)
#                    print(' ldvarU {}'.format(ldvarU))
                    self.add_propagator(ldvarU)
            # Make the actual agreement constraints
            agr_list = [agrvarD.get(feat, ZERO_TUPLE) for feat in self.language.feats]
#            print(' agr list {}'.format(agr_list))
#            print(' labeldfeatvars {}'.format(labeldfeatvars))
            self.add_propagator(EqualitySelection(agr_list, agreevar, labeldfeatvars, problem=problem,
                                                  maxset=self.maxset
#                                                  pattern=True
                                                  ))

##class DaughAgreementP(AP):
##    """New principle (started 2013.06.09). Daughters of relevant node on particular arc labels
##    must agree on a given feature. Indicated in lexical entries like this:
##    
##    """
##
##    def __init__(self, problem, dimension, project=False, applies=False):
##        AP.__init__(self, problem, dimension, short_name='DAgreeP', applies=applies)
##        self.maxset = set(self.language.agree)
##
##    def _get_dagrees(self, node, entry_index):
##        """The agreeement values in node's entry with entry_index,
##        default value if nothing there.
##        """
##        dim = self.get_entrydim(node, entry_index)
##        if dim:
##            return dim.attribs.get('dagree', set())
##        return set()
##
##    def _entry_dim_dagree(self, entry, abbrev):
##        """Get the daugh agreement constraint for the LexDim of an entry. If none, the default is set()."""
##        entry_dims = entry.dims
##        if abbrev not in entry_dims:
##            return set()
##        return entry_dims[abbrev].get_dagree()
##        
##    def make_variables(self, proc_direction=0):
##        # Make Agr variables
##        # This should already have happened because of AgreementP.
###        AP.make_variables(self, proc_direction=proc_direction)
##        # Make Agreement variables
##        problem = self.problem
##        abbrev = self.dimension.abbrev
##        for node in problem.get_nodes():
##            node_index = node.index
##            nodedimD = self.get_nodedimD(node)
##            entry_dagrees = [self._get_dagrees(node, index) for index in range(len(node.entries))]
##            entry_dagrees = set(itertools.chain(*entry_dagrees))
###            print("{} DAgree: {}".format(node, entry_dagrees))
##            if entry_dagrees:               
##                # dagreevar's values are tuples of ints indexing variables in list of agrvars that should be equal
##                # Get all possible values from the cdrs of the tuples in self.language.dagree_tuples
##                nodedimD['dagreevar'] = self.svar('{}'.format(node_index), set(), set([d[1:] for d in self.language.dagree]))
###                print("{} DAgree: {}".format(node, nodedimD['dagreevar']))
##                # Have make_constraints happen later
##                self.applies = True
##
##    def make_constraints(self, weight=1, proc_direction=0):
##        # Make Agr constraints
##        # This already happened because of AgreementP?
###        AP.make_constraints(self, weight=weight, proc_direction=proc_direction)
##        # Make Agreement constraints
##        problem = self.problem
##        abbrev = self.dimension.abbrev
##        # list of dimension dicts for each node
##        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
##        # dict of node feature variable lists indexed by feature
##        featvars = {}
##        for feat in self.language.feats:
##            featvars[feat] = [nodedimD['agrvars'].get(feat, ZERO_TUPLE) for nodedimD in nodedimDs]
##        for node in problem.get_nodes():
##            nodedimD = self.get_nodedimD(node)
##            if 'dagreevar' in nodedimD:
##                agrvarD = nodedimD['agrvars']
##                lexvar = node.lexvar
##                index = node.index
##                # Make lexical selection constraint for agreement variable
##                dagreevar = nodedimD['dagreevar']
##                print("Making DAgree constraints for {}, dagreevar {}".format(node, dagreevar))

class GovernmentP(Principle):
    '''Should be instantiated after AgreementP because it uses some of the variables
    created in AgreementP.make_variables()'''

    def __init__(self, problem, dimension, project=False):
        Principle.__init__(self, problem, dimension, short_name='GovP', project=project)
        self.maxset = set(self.language.govern)

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        for node in problem.get_nodes():
            # Get the set of all the possible combinations of arc label, feature, value specified in the
            # entries (do this better later).
#            entry_governs = [self._get_governs(node, index) for index in range(len(node.entries))]
#            entry_governs = set(itertools.chain(*entry_governs))
##            print('Entry governs for {}: {}'.format(node, entry_governs))
            # See if there are any government attributes for the entries of this node
            lexdims = [e.dims.get(abbrev) for e in node.entries]
            lexdimgov = [lexdim.attribs.get('govern') for lexdim in lexdims if lexdim]
            # If any entry has a govern constraint
#            if entry_governs:
            if any(lexdimgov):
                node_index = node.index
                nodedimD = self.get_nodedimD(node)
                # The government variable for this node and dimension
                # Its value is a set of (label-feat, value) pairs, where
                # label-feat is an int corresponding to a label, daughter feature pair.
                nodedimD['govvar'] = self.svar('{}'.format(node_index), set(), set(self.language.govern))
                govlabeldfeatvars = []
                nodedimD['govlabeldfeatvars'] = govlabeldfeatvars
                # Arc label / daughter feature variables
                # Each has the set of possible values for feature of daughters on arcs with label
                for label, dfeat in self.language.govlabeldfeats:
                    if any([label in gov for gov in lexdimgov if gov]):
                        values = self.language.agrs.get(dfeat, set())
                        values_copy = values.copy()
                        values_copy.add(())
                        if DFLT_FV not in values_copy:
                            values_copy.add(DFLT_FV)
#                     print('node', node, 'label', label, 'dfeat', dfeat, 'values', values)
                        var = self.svar('{}{}D{}'.format(node_index, label, dfeat),
                                        set(), values_copy)
                    else:
                        var = DetSVar('{}{}{}D{}'.format(self.var_pre, node_index, label, dfeat), set())
                    govlabeldfeatvars.append([label, dfeat, var])
#                print('govvar', nodedimD['govvar'].pprint())
#                print('govlabeldfeatvars')
#                for v in govlabeldfeatvars:
#                    v.pprint()

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        # dict of feature variable lists by feature (duplicated from AgreementP; should be a Dimension
        # attribute maybe)
        featvars = {}
        for feat in self.language.feats:
            featvars[feat] = [nodedimD['agrvars'].get(feat, ZERO_TUPLE) for nodedimD in nodedimDs]

        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            govvar = nodedimD.get('govvar')
            if govvar:
                agrvarD = nodedimD['agrvars']
                labeldfeatvars = nodedimD['govlabeldfeatvars']
                lexvar = node.lexvar
                index = node.index
     
#                print('Node {}, govvar {}'.format(node, govvar))
                # Make lexical selection constraint for government variable
                gov_vals = [self._entry_dim_govern(entry, abbrev) for entry in node.entries]
                # Later allow the government variable to be undetermined at initialization, to have a set
                # of possible values
                gov_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), val) for i, val in enumerate(gov_vals)]
                lprop = IntSelection(govvar, lexvar, gov_vars, problem=problem)
                self.add_propagator(lprop)
                
                # Constrain the label daughter feature variables to be the union of the agr feature values
                # for the daughters of node on arcs with label
#                print('labeldfeatvars', labeldfeatvars, 'govlabeldfeats', self.language.govlabeldfeats)
#                for ldvar, (label, dfeat) in zip([x[2] for x in labeldfeatvars], self.language.govlabeldfeats):
                for (label, dfeat, ldvar) in labeldfeatvars:
#                    print('label {} dfeat {} ldvar {}'.format(label, dfeat, ldvar))
                    if not isinstance(ldvar, Determined):
                        seqvars = featvars.get(dfeat)
                        if seqvars:
                            ms = self.language.agrs.get(dfeat, set())
#                        print('{} maxset {}'.format(self, ms))
                        # pattern=True so that bound strengthening of seq vars is through unification rather
                        # than intersection
                            prop = UnionSelection(ldvar, nodedimD['outvars'][label][0], seqvars, maxset=ms,
#                                              pattern=True,
                                                  problem=problem)
                            self.add_propagator(prop)
#                print('Using maxset', self.maxset)
                # Make the actual government constraint
                govlabelvars = [ldf[2] for ldf in labeldfeatvars]
                eprop = SimpleEqualitySelection(govvar, govlabelvars, maxset=self.maxset,
#                                                pattern=True,
                                                problem=problem)
#                print('EPROP', eprop)
                self.add_propagator(eprop)

    def _get_governs(self, node, entry_index):
        """The govern values in node's entry with entry_index,
        default value set() if nothing there.
        """
        dim = self.get_entrydim(node, entry_index)
        if dim:
            gov = dim.attribs.get('govern')
            if gov:
                # Return the set of arc label, feat, val possibilities for govern
                s = set()
                for tups in [tuple([(k, f, v) for f, v in l]) for k, l in gov.items()]:
                    s.update(tups)
                return s
#            return dim.attribs.get('govern', set())
        return set()

    def _entry_dim_govern(self, entry, abbrev):
        """Get the government constraint for the LexDim of an entry. If none, the default is set()."""
        entry_dims = entry.dims
        if abbrev not in entry_dims:
            return set()
        dim = entry_dims[abbrev]
        return dim.get_govern()
        
class ArcAgreementP(Principle):
    '''
    New principle, not in Debusmann.
    The value for an agr variable is determined by whether or not there is an outgoing
    arc with a specific label.
    Should be instantiated after AgreementP because it uses some of the variables
    created in AgreementP.make_variables().'''

    def __init__(self, problem, dimension, project=False):
        Principle.__init__(self, problem, dimension, short_name='ArcAgrP', project=project)

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        for node in problem.get_nodes():
            # See if there are any arc agreement attributes for the entries of this node
            lexdims = [e.dims.get(abbrev) for e in node.entries]
            lexdim_arcagr = [lexdim.attribs.get('arcagree') for lexdim in lexdims if lexdim]
            # If any entry has an arc agreement constraint
            if any(lexdim_arcagr):
                node_index = node.index
                nodedimD = self.get_nodedimD(node)
                # Make the arcagree variables for this node and dimension, one for each relevant arc label.
                # Assume there is only one possible constraint for an arc label, for example, for 'neg':
                # ('neg', (0), (1))
                arc_dict = {}
                entry_arcagr = []
                for arcagr_attrib in lexdim_arcagr:
                    if arcagr_attrib:
                        for arc, feat_trip in arcagr_attrib.items():
                            entry_arcagr0 = {}
                            # feat_trip: (feat_label, 0value, 1value)
                            feat_int = self.language.get_feat_int(feat_trip[0])
                            arc_dict[arc] = (feat_trip[0], feat_int, feat_trip[1], feat_trip[2])
                            entry_arcagr0[arc] = {(feat_int, feat_trip[1], feat_trip[2])}
                        entry_arcagr.append(entry_arcagr0)
                    else:
                        entry_arcagr.append(set())
                nodedimD['arcagree'] = entry_arcagr
#                print('Arc dict: {}'.format(arc_dict))
                # For each arc label found, create an arcagree variable
                arcagr_vars = {}
                for arc, values in arc_dict.items():
                    # For each arc label, make
                    # (1) a selection IVar with initial domain {0, 1}
                    # (2) the agr variable for the feature, created here if it doesn't exist
                    # (3,4) determined IVars for each possible value of the feature
                    feat, feat_int, v0, v1 = values
                    featvar = nodedimD['agrvars'].get(feat)
                    if not featvar:
                        featvar = DetIVar('{}|AgrP:{}{}'.format(abbrev, node_index, feat), v0)
                        nodedimD['agrvars'][feat] = featvar
#                        print('Created feat var {}'.format(featvar))
                    arcagr_vars[arc] = (self.ivar('{}:sel'.format(node_index), {0, 1}),
                                        featvar,
                                        DetIVar('{}{}:{}:0'.format(self.var_pre, arc, node_index), v0),
                                        DetIVar('{}{}:{}:1'.format(self.var_pre, arc, node_index), v1))
#                print('Arc agr vars: {}'.format(arcagr_vars))
                nodedimD['arcagrvars'] = arcagr_vars

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        # dict of feature variable lists by feature (duplicated from AgreementP; should be a Dimension
        # attribute maybe)
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            arcagrvars = nodedimD.get('arcagrvars')
            if arcagrvars:
                lexvar = node.lexvar
                index = node.index
                daughvars = self.get_label_daughs(node, nodedimD)
                arcagree = nodedimD['arcagree']
                # Make lexical selection constraints for arcagree vars
                for arc, (selvar, featvar, v0var, v1var) in nodedimD['arcagrvars'].items():
#                    print('  arc {}, selvar {}, featvar {}, v0var {}, v1var {}'.format(arc, selvar, featvar, v0var, v1var))
                    aa_arc_vals = [aa.get(arc) if aa else set() for aa in arcagree]
                    seq_vars = [DetSVar('{}{}:{}_{}'.format(self.var_pre, index, arc, ei), val) for ei, val in enumerate(aa_arc_vals)]
#                    print('  aa arc vals {}'.format(aa_arc_vals))
                    # Make the lexical selection constraint for this arc label
#                    lexsel = IntSelection(aavar, lexvar, seq_vars, problem=problem)
#                    self.add_propagator(lexsel)
#                    print('  lex sel prop {}'.format(lexsel))
                    arcDvar = daughvars[self.language.get_label_int(arc, abbrev)]
#                    print('  arcDvar {}'.format(arcDvar))
                    # Make the cardinality equivalence constraint
                    cardeq = CardinalityEq([arcDvar, selvar], problem=problem)
                    self.add_propagator(cardeq)
#                    print('  card eq prop {}'.format(cardeq))
                    # Make the selection constraint that is the actual content of this principle
                    valsel = IntIntSelection(featvar, selvar, [v0var, v1var], problem=problem)
                    self.add_propagator(valsel)
#                    print('  value sel prop {}'.format(valsel))

###
### Interface principles
###

class ClimbingP(IFPrinciple):
    """
    No attributes specified in lexicon; the principle associates *all* nodes in particular structural
    configurations between the associated dimensions.
    """

    def __init__(self, problem, dimension, project=False, applies=True):
        """applies is True by default."""
        IFPrinciple.__init__(self, problem, dimension, short_name='ClimbP', project=project,
                             applies=applies)

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        # Applies only to full-fledged nodes (not empty nodes)
        for node in problem.nodes:
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            # node's descendants on dim2
            daugh2 = nodedim2D['downvar']
            # node's descendants on dim1
            daugh1 = nodedim1D['downvar']
            # Any node that's a descendant of node on dim2 must be a descendant
            # of node on dim1; in other words, the dim2 descendants of node
            # must be included in the dim1 descendants of node
            subset_constraint = Inclusion([daugh2, daugh1], problem=problem)
            self.add_derived_propagator(subset_constraint)

class BarriersP(IFPrinciple):
    """Certain dim1 arc labels block a path between node0 and node1, joined in dim2,
    if node is between node0 and node1 on dim1 and labels are in node's 'blocks' attribute."""

    def __init__(self, problem, dimension, project=False, applies=False):
        """applies is False by default."""
        IFPrinciple.__init__(self, problem, dimension, short_name='BarriersP', project=project,
                             applies=applies)

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
#        dim1 = self.dimension.dim1
#        dim2 = self.dimension.dim2
#        block_values = self.language.lex_attribs.get('blocks', [])
#        block_values = {self.language.get_label_int(l, dim1.abbrev) for l in block_values}
        for node1 in problem.get_nodes():
#            index1 = node1.index
#            node1dim2D = node1.dims[dim2]
#            node1dim1D = node1.dims[dim1]
#            node1dimD = self.get_nodedimD(node1)
#            lexvar = node1.lexvar
            blocksattribs = [entry.get_dimattrib(abbrev, 'blocks') or [] for entry in node1.entries]
            if any(blocksattribs):
                self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        """Create both variables and constraints."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        # Values for attrib ('arg', etc.) recorded from lexical entries
        # $$ Do this instead in Language.finalize()??
        block_values = self.language.lex_attribs.get('blocks', [])
        # Possible attrib values converted to set of ints for dim1
        block_values = {self.language.get_label_int(l, dim1.abbrev) for l in block_values}
        for node1 in problem.get_nodes():
            index1 = node1.index
            node1dim2D = node1.dims[dim2]
            node1dim1D = node1.dims[dim1]
            node1dimD = self.get_nodedimD(node1)
            lexvar = node1.lexvar
            # list of 'blocks' lists for all entries
            blocksattribs = [entry.get_dimattrib(abbrev, 'blocks') or [] for entry in node1.entries]
            # Only proceed for nodes that have a 'blocks' attribute.
            if any(blocksattribs):
                # variable to represent the value of the 'blocks' attribute for this node
                node1blocksvar = self.svar('{}'.format(index1),
                                           # Domain includes all possible arc labels (as ints)
                                           set(), block_values)
                # Convert arc label strings to ints (one for each entry)
                blocksattribs = [{self.language.get_label_int(l, dim1.abbrev) for l in v} for v in blocksattribs]
                # Create seq vars for lexical selection constraint. Each has as its value a set of integers
                # representing dim1 arc labels.
                blocksattrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index1, i), set(val)) for i, val in enumerate(blocksattribs)]
                # Create the lexical selection constraint for node1blocksvar.
                # This determines the list of dim1 arc labels that participate in the constraint for this node.
                self.add_propagator(IntSelection(node1blocksvar, lexvar, blocksattrib_vars, problem=problem))
                # Now we need to check the ancestors and descendants of node1 and see if any are joined directly on dim2
                # ancestors:
                node1up = node1dim1D['upvar']
                # descendants:
                node1down1 = node1dim1D['downvar']
                # So let's get dim2 children of node1's ancestors.
                # A variable for these:
                node1up_daugh2var = self.svar('{}_up_daugh'.format(index1),
                                              # Domain includes all possible nodes
                                              set(), problem.all_indices)
                # List consisting of dim2 child vars for all nodes
                node1up_daugh2_list = [node.dims[dim2]['daughvar'] for node in problem.get_nodes()]
                # Constraint that finds the dim2 daughters of node1's dim1 ancestors
                up_daugh2_constraint = UnionSelection(node1up_daugh2var, node1up, node1up_daugh2_list, problem=problem)
                self.add_propagator(up_daugh2_constraint)
                # The nodes in node1up_daugh2var that are also dim1 descendants of node1
                # a variable for this:
                node1up_daugh2_downIvar = self.svar('{}_up_daugh_down'.format(index1),
                                                    set(),
                                                    # exclude empty nodes for upper bound
                                                    problem.all_indices - {index1})
                # Constraint for the intersection of the two variables
                up_daugh2_down_constraint = Intersection([node1up_daugh2_downIvar, node1up_daugh2var, node1down1],
                                                         problem=problem)
                self.add_derived_propagator(up_daugh2_down_constraint)
                # Now prevent any dim1 links into the nodes in node1up_daugh2_downIvar with labels that are in
                # node1blocksvar.
                # For each node (other than empty nodes),
                # create a variable representing the union of the dim1 mothers over all of the labels
                # in node1blocksvar
                blocks_mothers = []
                for node in problem.nodes:
                    index = node.index
                    nodedim1D = node.dims[dim1]
                    # variable for the union of these values over all of the labels in node1blocksvar
                    node_motherU_var = self.svar('{}_{}_mother'.format(index1, index),
                                                 set(),
                                                 # exclude empty nodes for upper bound
                                                 problem.max_set - {index})
                    # list of mothers of node by labels
                    mother_list = self.get_label_moths(node, dim=dim1, nodedimD=nodedim1D)
                    # constraint for the union of the mothers over the labels in node1blocksvar
                    node_mother_constraint = UnionSelection(node_motherU_var, node1blocksvar, mother_list,
                                                            problem=problem)
                    problem.add_propagator(node_mother_constraint)
                    blocks_mothers.append(node_motherU_var)
                # Now select from node_motherU_var the union of those nodes that are in node1up_daugh2_downIvar.
                # This value must be zero, so we can use a DetSVar for it.
                node1up_daugh2_down_mothU_var = EMPTY
# DetSVar('{}{}_up_daugh_down_mothU'.format(self.var_pre, index1), set())
# The union selection constraint for this:
                node1up_daugh2_down_mothU_constraint = UnionSelection(node1up_daugh2_down_mothU_var,
                                                                      node1up_daugh2_downIvar, blocks_mothers,
                                                                      problem=problem)
#                print('Block constraint', node1up_daugh2_down_mothU_constraint)
                problem.add_propagator(node1up_daugh2_down_mothU_constraint)

class IFAgreementP(IFPrinciple):
    """
    word
       dim
         agree: {dim2_feature: dim1_feature, ...}
    For each dim_2_feature, its value must agree with the value of dim1_feature on dim1.
    """

    def __init__(self, problem, dimension, project=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='IAgreeP', project=project)
#        self.maxset = self.get_language1().agree

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        self.possible_agree = []
        self.set_agr_maps()
#        print('Agr maps', self.agr_maps, 'rev agr maps', self.rev_agr_maps)
#        self.agr_maps = self.get_language1().agr_maps.get(self.get_language2().abbrev)
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            lexvar = node.lexvar
            index = node.index
            # Get the agreement attributes from the lexical entries (pairs of strings
            # representing dim2, dim1 features, for example, 'pn')
            node_agrees = [entry.get_dimattrib(abbrev, 'agree') or {} for entry in node.entries]
            if not any(node_agrees):
                self.possible_agree.append(set())
                continue
#            print('IFAgree node_agrees: {}'.format(node_agrees))
#            print('Agr maps: {}'.format(self.agr_maps))
            # Convert the string attributes to pairs of integers
            node_entry_agree_ints = [{self.agree_strings_to_ints(a) for a in agrees} \
                                          for agrees in node_agrees]
#            print('IFAgree node_entry_agree_ints: {}'.format(node_entry_agree_ints))
#            print('node {}, node_entry_agree_ints {}'.format(node, node_entry_agree_ints))
            # Create a determined set variable for each entry, with the set of possible int pairs as
            # its value
            nodedimD['agreevars'] = [DetSVar('{}{}_{}I'.format(self.var_pre, index, i), val) \
                                         for i, val in enumerate(node_entry_agree_ints)]
            # The set of all possible dim2, dim1 int pairs
            # Make this an attribute of the Principle object so we can use it in make_constraints too
#            print('Calculating possible agree for {}; {}'.format(self, node_entry_agree_ints))
            node_entry_agree_ints = set(itertools.chain(*node_entry_agree_ints))
            self.possible_agree.append(node_entry_agree_ints)
#            print('possible_agree {}'.format(self.possible_agree))
            # Create a set variable for the node with its dim2, dim1 feature pair as
            # its value; constrained with lexical selection constraint
            # (in make_constraints())
            nodedimD['agreevar'] = self.svar('{}I'.format(index), set(), node_entry_agree_ints)

    def agree_strings_to_ints(self, agree):
        """Convert an agree pair of feature strings to a pair of ints."""
        # Dim2 feature int
        feat2 = self.get_language2().get_feat_int(agree[0])
        # Dim1 feature int
        feat1 = self.get_language1().get_feat_int(agree[1])
        return feat2, feat1

    def _agr_map(self, feat1, feat2, l1=None, l2=''):
        l1 = l1 or self.get_language1()
        l2 = l2 or self.get_language2().abbrev
        return l1.get_agr_map(l2, feat1, feat2)

    def set_agr_maps(self):
        '''Find agr maps for target language and convert to tuple of tuples,
        as needed by projectors.'''
        maps = self.get_language1().agr_maps.get(self.get_language2().abbrev)
        rev_maps = self.get_language2().agr_maps.get(self.get_language1().abbrev)
        if maps:
            res = []
            # This is a dictionary of dictionaries
            for feats, dct in maps.items():
                # feats is a pair, either of strings or ints; include only
                # the ints
                if isinstance(feats[0], int):
                    res.append((feats, tuple(dct.items())))
            self.agr_maps = tuple(res)
            res = []
            for feats, dct in rev_maps.items():
                # feats is a pair, either of strings or ints; include only
                # the ints
                if isinstance(feats[0], int):
                    res.append((feats, tuple(dct.items())))
            self.rev_agr_maps = tuple(res)
        else:
            self.agr_maps = ()
            self.rev_agr_maps = ()
        
    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        lang1 = self.get_language1()
        lang2 = self.get_language2()
        agr_maps = self.agr_maps
        rev_agr_maps = self.rev_agr_maps
        for index, node in enumerate(problem.get_nodes()):
            nodedimD = self.get_nodedimD(node)
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            # Agr variables for this node on both dimensions (already created in AgrP)
            agrvars1D = nodedim1D['agrvars']
            agrvars2D = nodedim2D['agrvars']
            lexvar = node.lexvar
            index = node.index
            agreevar = nodedimD.get('agreevar')
            if not agreevar:
                continue
            agreevars = nodedimD['agreevars']
#            agr_maps = nodedimD['agrmaps']
            # Lexical selection constraint for this node for IF agree variable,
            # specifying the dim2, dim1 feature pair
            self.add_propagator(IntSelection(agreevar, lexvar, agreevars, problem=problem))
            ## Actual agreement constraint
            # Agr variables for dim2
            agr_list2 = [agrvars2D.get(feat, ZERO_TUPLE) for feat in lang2.feats]
            # Agr variables for dim1
            agr_list1 = [agrvars1D.get(feat, ZERO_TUPLE) for feat in lang1.feats]
#            print('Possible agree for {}/{}: {}'.format(self, node, self.possible_agree[index]))
            self.add_propagator(EqualitySelection(agr_list2, agreevar, agr_list1, problem=problem,
                                                  maxset=self.possible_agree[index],
                                                  agr_maps=agr_maps, rev_agr_maps=rev_agr_maps
#                                                  pattern=True
                                                  ))

class CrossGovernmentP(IFPrinciple):
    '''Similar to GovernmentP, except that the constraining arc label is on dim2 and the
    agreement for the daughter on dim1.
    As with GovernmentP, must be instantiated after AgreementP because it uses some of the variables
    created in AgreementP.make_variables()'''

    def __init__(self, problem, dimension, project=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='XGovP', project=project)

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        # Attrib can only be found in full nodes
        for node in problem.nodes:
            # See if there are any crossgov attributes for the entries of this node
            lexdims = [e.dims.get(abbrev) for e in node.entries]
            if any([lexdim.attribs.get('crossgov') for lexdim in lexdims if lexdim]):
                node_index = node.index
                nodedimD = self.get_nodedimD(node)
                # The crossgov variable for this node and dimension
                # Its value is a set of (label-feat, value) pairs, where
                # label-feat is an int corresponding to a label, daughter feature pair.
                nodedimD['xgovvar'] = self.svar('{}'.format(node_index),
                                                set(), set(self.language.crossgovern))
                govlabeldfeatvars = []
                nodedimD['xgovlabeldfeatvars'] = govlabeldfeatvars
                # Arc label / daughter feature variables
                # Each has the set of possible values for feature of daughters on arcs with label
                for label, dfeat in self.language.crossgovlabeldfeats:
                    values = self.language.agrs.get(dfeat, set())
                    govlabeldfeatvars.append(self.svar('{}{}D{}'.format(node_index, label, dfeat),
                                                       set(), values.copy()))

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        nodedimDs = [self.get_nodedimD(n) for n in problem.get_nodes()]
        if any('xgovvar' in dimD for dimD in nodedimDs):
            # There is some crossgovernment constraint on this dimension
            abbrev = self.dimension.abbrev
            dim1 = self.dimension.dim1
            dim2 = self.dimension.dim2
            l1 = dim1.language
            l2 = dim2.language
            # dict of feature variable lists by feature (duplicated from AgreementP; should be a Dimension
            # attribute maybe)
            featvars = {}
            nodedim1Ds = [node.dims[dim1] for node in problem.get_nodes()]
            for feat in self.language.feats:
                featvars[feat] = [nodedim1D['agrvars'].get(feat, ZERO_TUPLE) for nodedim1D in nodedim1Ds]

            for node in problem.nodes:
                nodedimD = self.get_nodedimD(node)
                nodedim1D = node.dims[dim1]
                nodedim2D = node.dims[dim2]
                govvar = nodedimD.get('xgovvar')
                if govvar:
                    agrvarD = nodedim1D['agrvars']
                    labeldfeatvars = nodedimD['xgovlabeldfeatvars']
                    lexvar = node.lexvar
                    index = node.index
         
                    # Make lexical selection constraint for government variable
                    gov_vals = [self._entry_dim_xgovern(entry, abbrev, l1, l2) for entry in node.entries]
                    gov_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), val) for i, val in enumerate(gov_vals)]
                    lex_selection = IntSelection(govvar, lexvar, gov_vars, problem=problem)
                    self.add_propagator(lex_selection)
                    
                    # Constrain the label daughter feature variables on dim2 to be the union of the agr feature values
                    # for the daughters of node on arcs with label
                    for ldvar, (label, dfeat) in zip(labeldfeatvars, self.language.crossgovlabeldfeats):
                        seqvars = featvars.get(dfeat)
                        if seqvars:
                            # pattern=True so that bound strengthening of seq vars is through unification rather
                            # than intersection
                            union_constraint = UnionSelection(ldvar, nodedim2D['outvars'][label][0], seqvars,
#                                                              pattern=True,
                                                              problem=problem)
                            self.add_propagator(union_constraint)
        
                    # Make the actual government constraint
                    equality_constraint = SimpleEqualitySelection(govvar, labeldfeatvars,
#                                                                  pattern=True,
                                                                  problem=problem)
                    self.add_propagator(equality_constraint)

    def _entry_dim_xgovern(self, entry, abbrev, lang1, lang2):
        """Get the cross government constraint for the LexDim of an entry. If none, the default is set()."""
        entry_dims = entry.dims
        if abbrev not in entry_dims:
            return set()
        entry_dim = entry_dims[abbrev]
        gov_strings = entry_dim.get_attrib('crossgov') or {}
        gov_ints = set()
        for label, (feat, value) in gov_strings.items():
            ints = lang1.crossgov_strings_to_ints((label, feat, value))
            if ints:
                gov_ints.add(ints)
            else:
                ints = lang2.crossgov_strings_to_ints((label, feat, value))
                if ints:
                    gov_ints.add(ints)
                else:
                    print("WARNING: crossgovern feature missing in languages")
        return gov_ints

class CrossOrderEqP(IFPrinciple):
    """New interface principle, not in Debusmann, that constrains the order of nodes on
    particular arcs in dimension 1 to be the same in dimension 2. Should follow OrderP.
    2013-06-03."""

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='XOrderEqP', project=project,
                             applies=applies)
            #        print('XOrderEqP: dim {}, dim1 {}, dim2 {}'.format(self.dimension, self.dimension.dim1, self.dimension.dim2))

    def _get_order_vars(self, abbrev=''):
        """Returns a list of L2 order variables, one for each real node."""
        if not abbrev:
            dim2 = self.dimension.dim2
            l2 = dim2.language
            abbrev = l2.order_dim
        return [node.get_dim_dict(abbrev).get('posvar') for node in self.problem.nodes]

    def _make_max_order_set(self, dim=None, labels=None):
        """Same as in OrderP.
        Maximum set of possible order pair tuples; this could be constrained
        a lot more, for example, to exclude pairs that are not possible outgoing
        arcs from the same nodes, like (detf, compf).
        """
        if not dim:
            dim = self.dimension.dim2
        if not labels:
            labels = range(len(dim.language.labels[dim.abbrev])+1)
        return set(itertools.permutations(labels, 2))

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        l1 = dim1.language
        l2 = dim2.language
        l2_order_dim = l2.order_dim
        # Position variables of nodes in L2
        self.posvars2 = self._get_order_vars()
        # If L2 does not have position variables, stop
        if not all(self.posvars2):
            return
        # Attrib can only be found in full nodes
        for node in problem.nodes:
            # See if there are any ordereq attributes for the entries of this node
            lexdims = [e.dims.get(abbrev, set()) for e in node.entries]
            lexordereq = [lexdim.attribs.get('ordereq') for lexdim in lexdims if lexdim]
            if any(lexordereq):
                # Principle applies because this node has the ordereq attribute
                self.applies = True
                lexvar = node.lexvar
                node_index = node.index
                dim = self.dimension
                nodedimD = self.get_nodedimD(node)
                lexordereqlist = [{l1.get_label_int(l, dim1.abbrev) for l in lexval} for lexval in lexordereq]
#                print('O=; node {}, lexordereq {}'.format(node, lexordereq))
                # The ordereq variable for this node and dimension
                if isinstance(lexvar, Determined):
                    # No lexical selection; the ordereq variable is also determined
                    ordereqvar = DetSVar('{}_O='.format(node_index), lexordereqlist[0])
                else:
                    vals = set().union(lexordereqlist)
                    # Lexical selection
                    ordereqvar = self.svar('{}'.format(node_index), set(), vals)
                    # Make the lexical selection constraint here; not normally needed since
                    # this principle will normally apply to unambiguous nodes
                    ordereqlexsel = IntSelection(ordereqvar, lexvar, lexordereqlist, problem=problem)
                    self.add_propagator(ordereqlexsel)
#                print('O=; ordereqvar {}'.format(ordereqvar))
                nodedimD['ordereqvar'] = ordereqvar
                # Variable to represent the union of all of the nodes on the arcs specified by ordereqvar
                ordereqnodes = self.svar('{}_N'.format(node_index), set(), problem.all_indices - {node_index})
#                print('O=; ordereqnodes {}'.format(ordereqnodes))
                nodedimD['ordereqnodes'] = ordereqnodes
 
    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        abbrev2 = dim1.abbrev
        l1 = dim1.language
        # Position variables of nodes in L2
        posvars2 = self.posvars2
        # Max set of order pairs
#        max_order_set = self._make_max_order_set()
        # Attrib can only be found in full nodes
        for node in problem.nodes:
            nodedimD = self.get_nodedimD(node)
            if 'ordereqvar' in nodedimD:
                # Variables, if any, are stored here
                lexvar = node.lexvar
                node_index = node.index
                nodedim1D = node.dims[dim1]
                ordereqvar = nodedimD['ordereqvar']
                ordereqnodes = nodedimD['ordereqnodes']
                seqvars = self.get_label_daughs(node, dim=dim1, nodedimD=nodedim1D)
#                print('O=; seqvars {}'.format(seqvars))
                # Constraint for ordereqnodes: the indices of the nodes whose order is to
                # be constrained in dim2
                sel_prop = UnionSelection(ordereqnodes, ordereqvar, seqvars, problem=problem)
#                print('O=; main var constraint {}'.format(sel_prop))
                self.add_propagator(sel_prop)
                # Position variables of nodes in L2
#                print('O=; posvars2 {}'.format(posvars2))
                # Use SimplePrecedenceSelection to constrain selected variables in posvars
                # to be in their L1 order
                # Get the possible daughter labels for L2
                lexdims = [e.dims.get(abbrev2) for e in node.entries]
                d_labels = [d.attribs.get('daughs', set()) for d in lexdims]
                d_labels = set().union(*d_labels)
                max_order_set = self._make_max_order_set(labels=d_labels)
#                print("O=; max order set {}".format(max_order_set))
                order_prop = SimplePrecedenceSelection(ordereqnodes, posvars2,
                                                       problem=problem,
                                                       maxset=max_order_set)
#                print('O=; order prop {}'.format(order_prop))
                self.add_propagator(order_prop)

class ArgP(IFPrinciple):
    """
    Interface principle.
    word
       dim
         arg: {dim2_label: [dim1_label, ...], ...}
    or:
         argrev: {dim1_label: [dim2_lael, ...], ...}
    For each dim1_label (rev: dim2_label), daughter of word on arc with dim2_label (rev: dim1_label)
    is daughter of some word on arc with dim1_label (rev: dim2_label).
    Subclasses for reverse=True and reverse=False
    """

    def __init__(self, problem, dimension, short_name='ArgP', reverse=False, label='arg',
                 project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name=short_name, reverse=reverse,
                             project=project, applies=applies) 
        self.label = label

    def make_variables(self, proc_direction=0):
        """Check to see whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2 if not self.reverse else self.dimension.dim1
        for node in problem.get_nodes():
            # list of arg dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, self.label) or {} for entry in node.entries]
            # Attribute is indexed by dim2 label in arg dict
            # Check all of the arc labels on dim2
            for label in self.get_arc_labels(dim2):
                # List of arg constraints for this label for all entries
                labelattribs = [attrib.get(label, ()) for attrib in nodeattribs]
                if any(labelattribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints(self.label)
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1 if not self.reverse else self.dimension.dim2
        dim2 = self.dimension.dim2 if not self.reverse else self.dimension.dim1
        label_language = dim1.language
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
#            print("Arg: node {}, nodedim {}".format(node, nodedimD))
            if dim2 not in node.dims:
                continue
            nodedim2D = node.dims[dim2]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # list of arg dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, self.label) or {} for entry in node.entries]
            # Attribute is indexed by dim2 label in arg dict
            # Check all of the arc labels on dim2
            for label in self.get_arc_labels(dim2):
                # List of arg constraints for this label for all entries
                labelattribs = [attrib.get(label, ()) for attrib in nodeattribs]
                if any(labelattribs):
                    # Only worry about labels for which there is some constraint
                    # Create an SVar for arg for this node/dim2 label combination.
                    # The value of nodeattribvar will be the set of dim1 arc labels
                    # that participate in the constraint (node --label-> daugh2)
                    nodeattribvar = self.svar('{}{}'.format(index, label),
                                              # Domain includes all possible arc labels (as ints)
                                              set(), self.attrib_values)
                    # Add this variable to the dictionary of node variables
                    nodeattribD[label] = nodeattribvar
                    # Convert arc label strings to ints (one for each entry)
                    labelattribs = [[label_language.get_label_int(l, dim1.abbrev) for l in v] for v in labelattribs]
                    # Create seq vars for lexical selection constraint. Each has as its value a set of integers
                    # representing dim1 arc labels.
                    labelattrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) for i, val in enumerate(labelattribs)]
                    # Create the lexical selection constraint for nodeattribvar.
                    # This determines the list of dim1 arc labels that participate in the constraint for
                    # the specific dim2 arc label.
                    self.add_propagator(IntSelection(nodeattribvar, lexvar, labelattrib_vars, problem=problem))

                    ## The main constraint requires
                    # (1) for each node, a variable representing the union of the dim1 daughter vars for each arc label in
                    #     the arg attributes list and
                    # (2) the corresponding union selection constraint
                    dim1daughvar_unions = []
                    for node1 in problem.get_nodes():
                        index1 = node1.index
                        node1dim1D = node1.dims[dim1]
                        # Variable representing the union of daughters of node1 across selected arc labels
                        dim1daughvar_union = self.svar('1:U{}_{}_{}D'.format(index1, index, label),
                                                       set(), problem.all_indices - {index1})
#                        print('Created svar', dim1daughvar_union)
                        # Daughter vars out of node1 for each arc label
                        daughvars = self.get_label_daughs(node1, dim=dim1, nodedimD=node1dim1D)
                        # Union selection constraint
                        self.add_propagator(UnionSelection(dim1daughvar_union, nodeattribvar, daughvars, problem=problem))
                        dim1daughvar_unions.append(dim1daughvar_union)
                    # (3) another variable representing the union of the union variables
                    dim1daughvarU_union = self.svar('1:U{}_{}D'.format(index, label),
                                                    set(), problem.all_indices)
                    # (4) the corresponding union constraint
                    self.add_derived_propagator(Union([dim1daughvarU_union] + dim1daughvar_unions, problem=problem))
                    # (5) the already existing variable for the daughters of node in dim2 along arc label
                    dim2daughvar = nodedim2D['outvars'][label][0]
                    # (6) the subset constraint relating (5) and (4): the daughters of node in arc label must
                    # be a subset of the union of union of dim1 daughters of all the nodes along the dim1 arc labels
                    # specified by nodeattribvar. BUT if nodeattribvar is empty (that is, lexical selection favors an
                    # entry that has no 'arg' attribute for label), then dim2daughvar can't be a (proper) subset
                    # of dim1daughvarU_union, which is empty (the union of empty sets).
                    # A variable to represent the truth value of the membership constraint
                    incltruthvar = self.ivar('{}{}_mem?'.format(index, label), {0, 1})
                    ## The inclusion constraint (reified to keep track of its truth value)
                    incl_constraint = ReifiedInclusion(dim2daughvar, dim1daughvarU_union, incltruthvar, problem=problem)
                    self.add_propagator(incl_constraint)
                    ## The equivalence constraint representing the agreement between the value of nodeattribvar and the
                    ## inclusion constraint
                    equiv_constraint = LogEquivalence([incltruthvar, nodeattribvar], problem=problem)
                    self.add_propagator(equiv_constraint)

class LinkingEndP(ArgP):
    """
    Interface principle.
    word
       dim
         arg: {dim2_label: [dim1_label, ...], ...}
    """

    def __init__(self, problem, dimension, project=False):
        ArgP.__init__(self, problem, dimension, short_name='LEP', reverse=False, label='arg') 

class RevLinkingEndP(ArgP):
    """
    Interface principle.
    word
       dim
         arg: {dim1_label: [dim2_label, ...], ...}
    """

    def __init__(self, problem, dimension, project=False):
        ArgP.__init__(self, problem, dimension, short_name='RevLEP', reverse=True, label='argrev') 

class LinkingDaughterEndP(IFPrinciple):
    """
    Interface principle.
    word
       lde: {dim2_label: [dim1_label, ...], ...}
    For each dim1_label, daughter of node on arc with dim2_label is daughter of same node on arc with dim1_label.
    """

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='LDEP', project=project,
                             applies=applies)

    def make_variables(self, proc_direction=0):
        """Check whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodeattribs = [entry.get_dimattrib(abbrev, 'ldend') or {} for entry in node.entries]
            for label2 in self.get_arc_labels(dim2):
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints('ldend')
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            if dim2 not in node.dims or dim2 not in node.dims:
                continue
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # list of ldend dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, 'ldend') or {} for entry in node.entries]
            # Attribute is indexed by dimension2 label in ldend dict
            for label2 in self.get_arc_labels(dim2):
                # list of ldend constraints for this label for all entries
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    # There is an ldend constraint for label2
                    ## Make the lexical selection constraint for this node, label2 combination
                    # Convert arc label strings to ints for all entries
                    label2attribs = [[self.language.get_label_int(l, dim1.abbrev) for l in v] for v in label2attribs]
                    # Create seq vars for selection constraint
                    label2attrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) \
                                             for i, val in enumerate(label2attribs)]
                    # Create an SVar for node, label2; mainvar of selection constraint
                    node_label2_attribvar = self.svar('{}{}'.format(index, label2),
                                                      # Domain includes all possible arc labels (as ints); is this right??
                                                      set(), self.attrib_values)
                    nodeattribD[label2] = node_label2_attribvar
                    # Lexical selection constraint: mainvar, selvar, seqvars
                    sel_constraint = IntSelection(node_label2_attribvar, lexvar, label2attrib_vars, problem=problem)
                    self.add_propagator(sel_constraint)
                    
                    ## Variables for dim2 and dim1 daughters
                    ## Get the node daughters var for label2
                    dim2daughvar = nodedim2D['outvars'][label2][0]
                    ## Daughters on dim1 depend on lexical selection constraint and value of main var.
                    # We need a selection constraint to select the dim1 daughters that agree with the constraint arc labels.
                    # Variable to represent the union of the daughters of node on dim1 over the relevant dim1 labels
                    # (the sel constraint main var)
                    dim1daughvar = self.svar('{}{}_D1'.format(index, label2),
                                             set(),  problem.all_indices - {index})
                    # Seq vars for selection constraint (a label-indexed list of SVars for node's dim1 daughters)
                    dim1daughvars = self.get_label_daughs(node, dim1, nodedim1D)
                    # The selection constraint for dim1 daughters
                    D1_sel_constraint = UnionSelection(dim1daughvar, node_label2_attribvar, dim1daughvars, problem=problem)
                    self.add_propagator(D1_sel_constraint)
                    ## Now the main constraint: the daughters of node on dim2 for label2 have to be daughters
                    ## of node on dim1 for one of labels1; that is, the intersection of dim2daughvar and dim1daughvar
                    ## must be equivalent to dim2daughvar if the ldend attrib is non-null.
                    ## If the ldend attrib is set(), the equality constraint need not hold (though it probably CAN).
                    # SVar for the intersection
                    dim1_2_daughI = self.svar('{}{}_I'.format(index, label2),
                                              set(), problem.all_indices - {index})
                    # The inters constraint
                    dim1_2_daughIC = Intersection([dim1_2_daughI, dim1daughvar, dim2daughvar], problem=problem)
                    self.add_derived_propagator(dim1_2_daughIC)
                    # The equality constraint
                    # A variable to represent the truth value of the equality constraint
                    eqtruthvar = self.ivar('{}{}_eq?'.format(index, label2), {0, 1})
                    # The equality constraint (reified to keep track of its truth value)
                    eq_constraint = ReifiedEquality(dim1_2_daughI, dim2daughvar, eqtruthvar, problem=problem)
                    self.add_propagator(eq_constraint)
                    # The logical implication constraint representing the relationship between the value of
                    # node_label2_attribvar and the equality constraint
                    implic_constraint = LogImplication([node_label2_attribvar, eqtruthvar], problem=problem)
                    self.add_propagator(implic_constraint)

class LinkingMotherEndP(IFPrinciple):
    """
    Interface principle.
    word
       mod: {dim2_label: [dim1_label, ...], ...}
    For each dim1_label, daughter of node on arc with dim2_label is mother of same node on arc with dim1_label.
    """

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='LMP', project=project,
                             applies=applies)

    def make_variables(self, proc_direction=0):
        """Check whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodeattribs = [entry.get_dimattrib(abbrev, 'mod') or {} for entry in node.entries]
            for label2 in self.get_arc_labels(dim2):
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints('mod')
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            if dim2 not in node.dims or dim2 not in node.dims:
                continue
            nodedim1D = node.dims[dim1]
            nodedim2D = node.dims[dim2]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # list of mod dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, 'mod') or {} for entry in node.entries]
            ### From here based on LinkingDaughterEndP

            # Attribute is indexed by dimension2 label in ldend dict
            for label2 in self.get_arc_labels(dim2):
                # list of mod constraints for this label for all entries
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    # There is a mod constraint for label2
                    ## Make the lexical selection constraint for this node, label2 combination
                    # Convert arc label strings to ints for all entries
                    label2attribs = [[self.language.get_label_int(l, dim1.abbrev) for l in v] for v in label2attribs]
                    # Create seq vars for selection constraint
                    label2attrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) for i, val in enumerate(label2attribs)]
                    # Create an SVar for node, label2; mainvar of selection constraint
                    node_label2_attribvar = self.svar('{}{}'.format(index, label2),
                                                      # Domain includes all possible arc labels (as ints); is this right??
                                                      set(), self.attrib_values)
                    nodeattribD[label2] = node_label2_attribvar
                    # Lexical selection constraint: mainvar, selvar, seqvars
                    sel_constraint = IntSelection(node_label2_attribvar, lexvar, label2attrib_vars, problem=problem)
                    self.add_propagator(sel_constraint)
                    
                    ## Variables for dim2 daughters and dim1 mothers
                    ## Get the node daughters var for label2
                    dim2daughvar = nodedim2D['outvars'][label2][0]
                    ## Daughters on dim1 depend on lexical selection constraint and value of main var
                    # We need a selection constraint variable to represent the union of the
                    # mothers of node on dim1 over the relevant dim1 labels
                    # (the sel constraint main var)
                    dim1mothvar = self.svar('{}{}_M1'.format(index, label2),
                                            set(),  problem.all_indices - {index})
                    # Seq vars for selection constraint (a label-indexed list of SVars for node's dim1 daughters)
                    dim1mothvars = self.get_label_moths(node, dim1, nodedim1D)
                    # The selection constraint for dim1 mothers
                    M1_sel_constraint = UnionSelection(dim1mothvar, node_label2_attribvar, dim1mothvars, problem=problem)
                    self.add_propagator(M1_sel_constraint)
                    ## Now the main constraint: the daughters of node on dim2 for label2 have to be mothers
                    ## of node on dim1 for one of labels1; that is, the intersection of dim2daughvar and dim1mothvar
                    ## must be equivalent to dim2daughvar if the mod attrib is non-null.
                    ## If the mod attrib is set(), the equality constraint need not hold (though it probably CAN).
                    # SVar for the intersection
                    dim1moth_2daughI = self.svar('{}{}_I'.format(index, label2),
                                                 set(), problem.all_indices - {index})
                    # The inters constraint
                    dim1moth_2daughIC = Intersection([dim1moth_2daughI, dim1mothvar, dim2daughvar], problem=problem)
                    self.add_derived_propagator(dim1moth_2daughIC)
                    # The equality constraint
                    # A variable to represent the truth value of the equality constraint
                    eqtruthvar = self.ivar('{}{}_eq?'.format(index, label2), {0, 1})
                    # The equality constraint (reified to keep track of its truth value)
                    eq_constraint = ReifiedEquality(dim1moth_2daughI, dim2daughvar, eqtruthvar, problem=problem)
                    self.add_propagator(eq_constraint)
                    # The logical implication constraint representing the relationship between the value of
                    # node_label2_attribvar and the equality constraint
                    implic_constraint = LogImplication([node_label2_attribvar, eqtruthvar], problem=problem)
                    self.add_propagator(implic_constraint)

class LinkingBelowStartP(IFPrinciple):
    """
    Interface principle. NOTE: THIS IS ACTUALLY LinkingBelow1or2Start!
    word
       lbstart: {dim2_label: [dim1_label, ...], ...}
    For each dim1_label, daughter of node on arc with dim2_label is daughter of same node on arc with dim1_label
    or granddaughter of one of those nodes.
    """

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='LBSP',
                             project=project, applies=applies)

    def make_variables(self, proc_direction=0):
        """Check whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodeattribs = [entry.get_dimattrib(abbrev, 'lbstart') or {} for entry in node.entries]
            for label2 in self.get_arc_labels(dim2):
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints('lbstart')
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            if dim2 not in node.dims or dim2 not in node.dims:
                continue
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # list of lbstart dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, 'lbstart') or {} for entry in node.entries]
            # Attribute is indexed by dimension2 label in lbstart dict
            for label2 in self.get_arc_labels(dim2):
                # list of lbstart constraints for this label for all entries
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    # There is an lbstart constraint for label2
                    ## Make the lexical selection constraint for this node, label2 combination
                    # Convert arc label strings to ints for all entries
                    label2attribs = [[self.language.get_label_int(l, dim1.abbrev) for l in v] for v in label2attribs]
                    # Create seq vars for selection constraint
                    label2attrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) for i, val in enumerate(label2attribs)]
                    # Create an SVar for node, label2; mainvar of selection constraint
                    # Its value represents the relevant dim1 labels that participate in the constraint
                    node_label2_attribvar = self.svar('{}{}'.format(index, label2),
                                                      # Domain includes all possible arc labels (as ints); is this right??
                                                      set(), self.attrib_values)
                    nodeattribD[label2] = node_label2_attribvar
                    # Lexical selection constraint: mainvar, selvar, seqvars
                    sel_constraint = IntSelection(node_label2_attribvar, lexvar, label2attrib_vars, problem=problem)
                    self.add_propagator(sel_constraint)

                    ## SAME UP TO THIS POINT FOR ALL LINKING PRINCIPLES
                    
                    ## Variables for dim2 and dim1 daughters
                    ## Get the node daughters var for label2
                    dim2daughvar = nodedim2D['outvars'][label2][0]
                    ## Daughters on dim1 depend on lexical selection constraint and value of main var.
                    # We need a selection constraint to select the dim1 daughters that agree with the constraint arc labels.
                    # Variable to represent the union of the daughters of node on dim1 over the relevant dim1 labels
                    # (the sel constraint main var)
                    dim1daughvar = self.svar('{}{}_D1'.format(index, label2),
                                             set(),  problem.all_indices - {index})
                    # Seq vars for selection constraint (a label-indexed list of SVars for node's dim1 daughters)
                    dim1daughvars = self.get_label_daughs(node, dim1, nodedim1D)
                    # The selection constraint for dim1 daughters
                    D1_sel_constraint = UnionSelection(dim1daughvar, node_label2_attribvar, dim1daughvars, problem=problem)
                    self.add_propagator(D1_sel_constraint)
                    # Granddaughters: daughters of nodes in dim1daughvar on all arcs; main var for union selection
                    # constraint
                    dim1granddaughters = self.svar('{}_GD'.format(index), set(), problem.all_indices)
                    # Sequence variables for union selection constraint: dim1 daughters of all nodes
                    dim1s = [n.dims[dim1] for n in problem.get_nodes()]
                    nodedim1_daughs = [d1['daughvar'] for d1 in dim1s]
                    # Union selection constraint for granddaughters of this node whose mothers are the nodes in dim1daughvar
                    dim1_gd_US_constraint = UnionSelection(dim1granddaughters,
                                                           # selection variable
                                                           dim1daughvar,
                                                           nodedim1_daughs, problem=problem)
                    self.add_propagator(dim1_gd_US_constraint)
                    # The union of the daughters and the granddaughters
                    dim1_D_GD = self.svar('U{}_D+GD'.format(index), set(), problem.all_indices)
                    # Union constraint
                    dim1_D_GD_U_constraint = Union([dim1_D_GD, dim1granddaughters, dim1daughvar], problem=problem)
                    self.add_derived_propagator(dim1_D_GD_U_constraint)

                    ## Now the main constraint: the daughters of node on dim2 for label2 have to be daughters
                    ## of node on dim1 for one of labels1 or granddaughters of those nodes; that is, the intersection
                    ## of dim2daughvar and dim1_D_GD must be equivalent to dim2daughvar if the lbstart attrib is non-null.
                    ## If the lbstart attrib is set(), the equality constraint need not hold (though it probably CAN).
                    # SVar for the intersection
                    dim1_2_daughI = self.svar('{}{}_I'.format(index, label2),
                                              set(), problem.all_indices - {index})
                    # The inters constraint
                    dim1_2_daughIC = Intersection([dim1_2_daughI, dim1_D_GD, dim2daughvar], problem=problem)
                    self.add_derived_propagator(dim1_2_daughIC)
                    # The equality constraint
                    # A variable to represent the truth value of the equality constraint
                    eqtruthvar = self.ivar('{}{}_eq?'.format(index, label2), {0, 1})
                    # The equality constraint (reified to keep track of its truth value)
                    eq_constraint = ReifiedEquality(dim1_2_daughI, dim2daughvar, eqtruthvar, problem=problem)
                    self.add_propagator(eq_constraint)
                    # The logical implication constraint representing the relationship between the value of
                    # node_label2_attribvar and the equality constraint
                    implic_constraint = LogImplication([node_label2_attribvar, eqtruthvar], problem=problem)
                    self.add_propagator(implic_constraint)

class LinkingBelowEndP(IFPrinciple):
    """
    New interface principle.
    word
       lbend: {dim2_label: [dim1_label, ...], ...}
    For each dim1_label, daughter of node N on arc with dim2_label is ancestor of daughter of node N on arc with dim1_label
    out of original node.
    """

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='LBEP',
                             project=project, applies=applies)

    def make_variables(self, proc_direction=0):
        """Check whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodeattribs = [entry.get_dimattrib(abbrev, 'lbend') or {} for entry in node.entries]
            for label2 in self.get_arc_labels(dim2):
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints('lbend')
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            if dim2 not in node.dims or dim2 not in node.dims:
                continue
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # list of lbend dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, 'lbend') or {} for entry in node.entries]
            # Attribute is indexed by dimension2 label in lbend dict
            for label2 in self.get_arc_labels(dim2):
                # list of lbend constraints for this label for all entries
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    # There is an lbend constraint for label2
                    ## Make the lexical selection constraint for this node, label2 combination
                    # Convert arc label strings to ints for all entries
                    label2attribs = [[self.language.get_label_int(l, dim1.abbrev) for l in v] for v in label2attribs]
                    # Create seq vars for selection constraint
                    label2attrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) for i, val in enumerate(label2attribs)]
                    # Create an SVar for node, label2; mainvar of selection constraint
                    node_label2_attribvar = self.svar('{}{}'.format(index, label2),
                                                      # Domain includes all possible arc labels (as ints); is this right??
                                                      set(), self.attrib_values)
                    nodeattribD[label2] = node_label2_attribvar
#                    print('node_label2_attribvar {}'.format(node_label2_attribvar))
                    # Lexical selection constraint: mainvar, selvar, seqvars
                    sel_constraint = IntSelection(node_label2_attribvar, lexvar, label2attrib_vars, problem=problem)
                    self.add_propagator(sel_constraint)

                    ## SAME UP TO THIS POINT FOR ALL LINKING PRINCIPLES
                    
                    ## Variables for dim2 and dim1 daughters
                    ## Variable for node daughters on label2
                    dim2daughvar = nodedim2D['outvars'][label2][0]
#                    print('dim2daughvar {}'.format(dim2daughvar))
                    ## Daughters on dim1 depend on lexical selection constraint and value of main var.
                    # We need a selection constraint to select the dim1 daughters that agree with the constraint arc labels.
                    # Variable to represent the union of the daughters of node on dim1 over the relevant dim1 labels
                    # (the sel constraint main var)
                    dim1daughvar = self.svar('{}{}_D1'.format(index, label2),
                                             set(),  problem.all_indices - {index})
#                    print('dim1daughvar {}'.format(dim1daughvar))
                    # Seq vars for selection constraint (a label-indexed list of SVars for node's dim1 daughters)
                    dim1daughvars = self.get_label_daughs(node, dim1, nodedim1D)
                    # The label-indexed selection constraint for dim1 daughters
                    D1_sel_constraint = UnionSelection(dim1daughvar, node_label2_attribvar, dim1daughvars, problem=problem)
                    self.add_propagator(D1_sel_constraint)
                    # Descendants of dim2daughs on dim1
                    dim2daugh_descendants1 = self.svar('{}_D_Desc1'.format(index), set(), problem.all_indices)
                    # Sequence variables for union selection constraint: dim1 descendants of all nodes
                    dim1s = [n.dims[dim1] for n in problem.get_nodes()]
                    nodedim1_descendants = [d1['downvar'] for d1 in dim1s]
                    # Union selection constraint for descendants
                    dim1_desc_US_constraint = UnionSelection(dim2daugh_descendants1,
                                                             # selection variable: indices of dim2 daughs of node on label2
                                                             dim2daughvar,
                                                             # sequence variables: dim1 descendants of all nodes
                                                             nodedim1_descendants, problem=problem)
                    self.add_propagator(dim1_desc_US_constraint)
#                    print('dim2daugh_descendants1 {}'.format(dim2daugh_descendants1))

                    ## Now the main constraint: the daughters of node on dim2 for label2 have to be dim1 ancestors
                    ## of nodes that are daughters of node on dim1 for labels1; that is, the intersection
                    ## of dim1daughvar and dim2daugh_descendants1 must be equivalent to dim1daughvar if the lbend attrib
                    ## is non-null. If the lbend attrib is set(), the equality constraint need not hold (though it probably CAN).
                    # SVar for the intersection
                    daugh_desc1_I = self.svar('{}{}_daugh_desc_I'.format(index, label2),
                                              set(), problem.all_indices - {index})
#                    print('daugh_desc1_I {}'.format(daugh_desc1_I))
                    # The intersection constraint
                    daugh_desc1_IC = Intersection([daugh_desc1_I, dim2daugh_descendants1, dim1daughvar], problem=problem)
                    self.add_derived_propagator(daugh_desc1_IC)
                    # The equality constraint
                    # A variable to represent the truth value of the equality constraint
                    eqtruthvar = self.ivar('{}{}_eq?'.format(index, label2), {0, 1})
                    # The equality constraint (reified to keep track of its truth value)
                    eq_constraint = ReifiedEquality(daugh_desc1_I, dim1daughvar, eqtruthvar, problem=problem)
                    self.add_propagator(eq_constraint)
                    # The logical implication constraint representing the relationship between the value of
                    # node_label2_attribvar and the equality constraint
                    implic_constraint = LogImplication([node_label2_attribvar, eqtruthvar], problem=problem)
                    self.add_propagator(implic_constraint)

class LinkingAboveEndP(IFPrinciple):
    """
    Interface principle.
    word
       dim
         laend: {dim2_label: [dim1_label, ...], ...}
    For each dim1_label, mother of word on arc with dim2_label is daughter or granddaughter
    of some word on arc path beginning with dim1_label.
    """

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='LAEP',
                             project=project, applies=applies) 

    def make_variables(self, proc_direction=0):
        """Check whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodeattribs = [entry.get_dimattrib(abbrev, 'laend') or {} for entry in node.entries]
            for label2 in self.get_arc_labels(dim2):
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints('laend')
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            if dim2 not in node.dims:
                continue
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # List of laend dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, 'laend') or {} for entry in node.entries]
            # Attribute is indexed by dimension2 label in laend dict
            for label2 in self.get_arc_labels(dim2):
                # list of laend constraints for this label for all entries
                label2labels1 = [attrib.get(label2, ()) for attrib in nodeattribs]
                # Only worry about labels for which there is some constraint
                if any(label2labels1):
                    # Create an SVar for laend for this node/label combination; this will specify the
                    # set of dim1 arc labels participating in the constraint for label2.
                    nodelabel2var = self.svar('{}{}'.format(index, label2),
                                              # Domain includes all possible dim1 arc labels (as ints)
                                              set(), self.attrib_values)
                    # Add this variable to the dictionary of node variables
                    nodeattribD[label2] = nodelabel2var
                    # Convert arc label strings to ints (one for each entry)
                    label2labels1 = [[self.language.get_label_int(l, dim1.abbrev) for l in v] for v in label2labels1]
                    # Create seq vars for lexical selection constraint. Each has as its value a set of integers
                    # representing dim1 arc labels.
                    label2labels1_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) for i, val in enumerate(label2labels1)]
                    # Create the lexical selection constraint for nodelabel2var, determining the dim1 labels for label2.
                    lexsel = IntSelection(nodelabel2var, lexvar, label2labels1_vars, problem=problem)
                    self.add_propagator(lexsel)
                    ## SAME UP TO THIS POINT FOR ALL LINKING PRINCIPLES

                    ## Existing variable for dim2 daughters of node on label2 arcs
                    dim2daughvar = nodedim2D['outvars'][label2][0]
                    ## Now we need a way to represent the intersection of the daughters of these nodes
                    ## on dim1 along arcs with the arc1 attribute labels. So we need a label-indexed list
                    ## of daughter variables for each of the nodes in dim2daughvar. But first we need
                    ## the unions of the dim1 daughters (and granddaughters) along the dim1 labels of *all*
                    ## of the nodes. So we'll create a node-indexed list for that purpose:
                    dim1_D_GD_unions = []
                    ## And to calculate the granddaughters, we'll need the same list of all daughter variables
                    ## for each node.
                    dim1s = [n.dims[dim1] for n in problem.get_nodes()]
                    nodedim1_daughs = [d1['daughvar'] for d1 in dim1s]
                    for node1 in problem.get_nodes():
                        index1 = node1.index
                        node1dim1D = node1.dims[dim1]
                        # Variable representing the union of daughters of node1 across selected arc labels
                        dim1daughvar_union = self.svar('1:U{}_{}D'.format(index1, index),
                                                       set(), problem.all_indices - {index1})
                        # Daughter vars out of node1 for each arc label
                        daughvars = self.get_label_daughs(node1, dim=dim1, nodedimD=node1dim1D)
                        # Union selection constraint
                        self.add_propagator(UnionSelection(dim1daughvar_union, nodelabel2var, daughvars, problem=problem))
                        # Now find the daughters of each of these on any arcs
                        dim1granddaughters = self.svar('1:{}_{}GD'.format(index1, index),
                                                       set(), problem.all_indices - {index1})
                        # Union selection constraint for granddaughters
                        dim1_gd_US_constraint = UnionSelection(dim1granddaughters, dim1daughvar_union, nodedim1_daughs, problem=problem)
                        self.add_propagator(dim1_gd_US_constraint)
                        # The union of the daughters and the granddaughters
                        dim1_D_GD_union = self.svar('1:U{}_{}D+GD'.format(index1, index),
                                                    set(), problem.all_indices - {index1})
                        # Union constraint
                        dim1_D_GD_U_constraint = Union([dim1_D_GD_union, dim1granddaughters, dim1daughvar_union], problem=problem)
                        self.add_derived_propagator(dim1_D_GD_U_constraint)
                        # Add the union of the daughters and granddaughters to the node-indexed list
                        dim1_D_GD_unions.append(dim1_D_GD_union)

                    ## OK, now we have a list of variables, each of which is bound to the union of possible (grand)daughters
                    ## on the
                    ## relevant dim1 labels for a single node. We need to restrict these to the nodes that are possible
                    ## daughters of the original node on dim2, that is, the nodes that are the value of dim2daughvar.
                    ## That is, we need another selection constraint, this time with dim2daughvar as the selvar.
                    ## Because the original node must be a member of *each* of the daughter node's dim1 (grand)daughter
                    ## sets, we want the intersection of the sets.
                    dim1daughters = self.svar('1:{}{}D_I'.format(index, label2), set(), problem.all_indices)
                    self.add_propagator(IntersectionSelection(dim1daughters, dim2daughvar, dim1_D_GD_unions, problem=problem))
                    ## So we have a variable, dim1daughters, that is bound to the intersection of all the dim1 (grand)daughters
                    ## (on the appropriate arcs) of all of the dim2 daughters (on the appropriate arcs) of the current node.
                    ## This list must contain the current node *if* the value of nodelabel2var is non-empty; otherwise it may
                    ## or may not contain the current node.
                    ## A determined IVar for the current node
                    nodeivar = DetIVar('{}{}'.format(self.var_pre, index), index)
                    ## A variable to represent the truth value of the membership constraint
                    memtruthvar = self.ivar('{}{}_mem?'.format(index, label2), {0, 1})
                    ## The membership constraint (reified to keep track of its truth value)
                    mem_constraint = ReifiedMembership(nodeivar, dim1daughters, memtruthvar, problem=problem)
                    self.add_propagator(mem_constraint)
                    ## The implication constraint representing the relation between the value of nodelabel2var and the
                    ## membership constraint
                    implic_constraint = LogImplication([nodelabel2var, memtruthvar], problem=problem)
                    self.add_propagator(implic_constraint)

class LinkingAboveBelow1or2StartP(IFPrinciple):
    """
    Interface principle. In fact the mother of all interface principles.
    word
       dim
         lab12s: {dim2_label: [dim1_label, ...], ...}
    Daughter of node N on arc with dim2_label is daughter or granddaughter
    of node on arc with some outgoing dim1_label which is either N or an ancestor of N.
    """

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='LAB12SP',
                             project=project, applies=applies)

    def make_variables(self, proc_direction=0):
        """Check whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodeattribs = [entry.get_dimattrib(abbrev, 'lab12s') or {} for entry in node.entries]
            for label2 in self.get_arc_labels(dim2):
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints('lab12s')
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        dim1s = [n.dims[dim1] for n in problem.get_nodes()]
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            if dim2 not in node.dims:
                continue
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # list of lab12s dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, 'lab12s') or {} for entry in node.entries]
            # Attribute is indexed by dim2 label in lab12s dict
            # Check all of the arc labels on dim2
            for label in self.get_arc_labels(dim2):
                # List of arg constraints for this label for all entries
                labelattribs = [attrib.get(label, ()) for attrib in nodeattribs]
                if any(labelattribs):
                    # Only worry about labels for which there is some constraint
                    # Create an SVar for lab12s for this node/dim2 label combination.
                    # The value of nodeattribvar will be the set of dim1 arc labels
                    # that participate in the constraint (node --label-> daugh2)
                    nodeattribvar = self.svar('{}{}'.format(index, label),
                                              # Domain includes all possible arc labels (as ints)
                                              set(), self.attrib_values)
                    # Add this variable to the dictionary of node variables
                    nodeattribD[label] = nodeattribvar
                    # Convert arc label strings to ints (one for each entry)
                    labelattribs = [[self.language.get_label_int(l, dim1.abbrev) for l in v] for v in labelattribs]
                    # Create seq vars for lexical selection constraint. Each has as its value a set of integers
                    # representing dim1 arc labels.
                    labelattrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) for i, val in enumerate(labelattribs)]
                    # Create the lexical selection constraint for nodeattribvar.
                    # This determines the list of dim1 arc labels that participate in the constraint for
                    # the specific dim2 arc label.
                    self.add_propagator(IntSelection(nodeattribvar, lexvar, labelattrib_vars, problem=problem))

                    ## Starting with the up= set for node, that is, node and its ancestors,
                    ## Look for all daughters of this set on the dim1 arc labels in nodeattribvar
                    # up= set for node
                    nodeequp = nodedim1D['equpvar']
                    ## Next get all of the daughters and granddaughters of these nodes on the dim1 arc labels in nodeattribvar
                    # First for each node a variable representing the union of all daughters on the dim1 arc labels in nodeattribvar
                    node1daughUs = []
                    # dim1 daughters of all nodes (needed in figuring the granddaughters)
                    nodedim1_daughs = [d1['daughvar'] for d1 in dim1s]
                    for node1 in self.problem.get_nodes():
                        index1 = node1.index
                        node1dim1D = node1.dims[dim1]
                        # Variable for union of daughters for node1
                        node1daughU = self.svar('{}_{}_{}_DU'.format(index, label, index1),
                                                set(), problem.all_indices)
                        # Daughter vars out of node1 for each arc label
                        node1daughvars = self.get_label_daughs(node1, dim=dim1, nodedimD=node1dim1D)
                        # Daughter union selection constraint
                        node1DUconstraint = UnionSelection(node1daughU, nodeattribvar, node1daughvars, problem=problem)
                        self.add_propagator(node1DUconstraint)
                        # OK, now what to do about the *grand*daughters --
                        # we need to get the union of all of the nodes in node1DUconstraint *and* their immediate daughters
                        # (on any arc)
                        node1DU_GD = self.svar('{}_{}_{}_DU_GD'.format(index, label, index1),
                                               set(), problem.all_indices)
                        # The union selection constraint for the granddaughters
                        node1DU_GDconstraint = UnionSelection(node1DU_GD, node1daughU, nodedim1_daughs, problem=problem)
                        self.add_propagator(node1DU_GDconstraint)
                        node1D_GD_U = self.svar('{}_{}_{}_D_GD_U'.format(index, label, index1),
                                                set(), problem.all_indices)
                        # The union constraint for the daughters and granddaughters
                        node1D_GD_U_constraint = Union([node1D_GD_U, node1DU_GD, node1daughU], problem=problem)
                        self.add_derived_propagator(node1D_GD_U_constraint)
                        # Add the union of the daughters and granddaughters to the list
                        node1daughUs.append(node1D_GD_U)
                    # Now we have variables representing all of the legal daughters and granddaughters of each node (or its ancestors)
                    # on dim1. We need the union of all of these that are included in up= of node.
                    # A variable for the union:
                    dim1D_GD_U = self.svar('{}_{}_D_GD_U'.format(index, label), set(), problem.all_indices)
                    # The union selection constraint:
                    dim1D_GD_U_constraint = UnionSelection(dim1D_GD_U, nodeequp, node1daughUs, problem=problem)
                    self.add_propagator(dim1D_GD_U_constraint)
                    # If nodeattribvar is not empty, the set of daughters of node on label must be included in this set.
                    nodelabel2daughs = nodedim2D['outvars'][label][0]
                    incltruthvar = self.ivar('{}{}_incl?'.format(index, label), {0, 1})
                    ## The inclusion constraint (reified to keep track of its truth value)
                    incl_constraint = ReifiedInclusion(nodelabel2daughs, dim1D_GD_U, incltruthvar, problem=problem)
                    self.add_propagator(incl_constraint)
                    ## nodeattribvar => incltruthvar (nothing can be inferred from the truth of incltruthvar)
                    # The logical implication constraint representing the relationship between the value of
                    # nodeattribvar and the inclusion constraint
                    implic_constraint = LogImplication([nodeattribvar, incltruthvar], problem=problem)
                    self.add_propagator(implic_constraint)

class LinkingAboveBelowStartP(IFPrinciple):
    """
    New interface principle, similar to LinkingAboveBelow1Or2StartP.
    word
       dim
         labs: {dim2_label: [dim1_label, ...], ...}
    Daughter of node N1 on arc with dim2_label is daughter
    of node N2 on arc with some outgoing dim1_label which is either N1 or an ancestor of N1.
    """

    def __init__(self, problem, dimension, project=False, applies=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='LABSP',
                             project=project, applies=applies)

    def make_variables(self, proc_direction=0):
        """Check whether the principle applies."""
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim2 = self.dimension.dim2
        for node in problem.get_nodes():
            nodeattribs = [entry.get_dimattrib(abbrev, 'labs') or {} for entry in node.entries]
            for label2 in self.get_arc_labels(dim2):
                label2attribs = [attrib.get(label2, ()) for attrib in nodeattribs]
                if any(label2attribs):
                    self.applies = True

    def make_constraints(self, weight=1, proc_direction=0):
        self.init_constraints('labs')
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        dim1s = [n.dims[dim1] for n in problem.get_nodes()]
        for node in problem.get_nodes():
            nodedimD = self.get_nodedimD(node)
            if dim2 not in node.dims:
                continue
            nodedim2D = node.dims[dim2]
            nodedim1D = node.dims[dim1]
            lexvar = node.lexvar
            index = node.index
            # A dict to keep the variables for different labels
            nodeattribD = {}
            # list of labs dicts for all entries
            nodeattribs = [entry.get_dimattrib(abbrev, 'labs') or {} for entry in node.entries]
            # Attribute is indexed by dim2 label in labs dict
            # Check all of the arc labels on dim2
            for label in self.get_arc_labels(dim2):
                # List of arg constraints for this label for all entries
                labelattribs = [attrib.get(label, ()) for attrib in nodeattribs]
                if any(labelattribs):
                    # Only worry about labels for which there is some constraint
                    # Create an SVar for labs for this node/dim2 label combination.
                    # The value of nodeattribvar will be the set of dim1 arc labels
                    # that participate in the constraint (node --label-> daugh2)
                    nodeattribvar = self.svar('{}{}'.format(index, label),
                                              # Domain includes all possible arc labels (as ints)
                                              set(), self.attrib_values)
                    # Add this variable to the dictionary of node variables
                    nodeattribD[label] = nodeattribvar
                    # Convert arc label strings to ints (one for each entry)
                    labelattribs = [[self.language.get_label_int(l, dim1.abbrev) for l in v] for v in labelattribs]
                    # Create seq vars for lexical selection constraint. Each has as its value a set of integers
                    # representing dim1 arc labels.
                    labelattrib_vars = [DetSVar('{}{}_{}'.format(self.var_pre, index, i), set(val)) for i, val in enumerate(labelattribs)]
                    # Create the lexical selection constraint for nodeattribvar.
                    # This determines the list of dim1 arc labels that participate in the constraint for
                    # the specific dim2 arc label.
                    self.add_propagator(IntSelection(nodeattribvar, lexvar, labelattrib_vars, problem=problem))

                    ## Starting with the up= set for node, that is, node and its ancestors,
                    ## Look for all daughters of this set on the dim1 arc labels in nodeattribvar
                    # up= set for node
                    nodeequp = nodedim1D['equpvar']
                    ## Next get all of the daughters and granddaughters of these nodes on the dim1 arc labels in nodeattribvar
                    # First for each node a variable representing the union of all daughters on the dim1 arc labels in nodeattribvar
                    node1daughUs = []
#                    # dim1 daughters of all nodes (needed in figuring the granddaughters)
#                    nodedim1_daughs = [d1['daughvar'] for d1 in dim1s]
                    for node1 in self.problem.get_nodes():
                        index1 = node1.index
                        node1dim1D = node1.dims[dim1]
                        # Variable for union of daughters for node1
                        node1daughU = self.svar('{}_{}_{}_DU'.format(index, label, index1),
                                                set(), problem.all_indices)
                        # Daughter vars out of node1 for each arc label
                        node1daughvars = self.get_label_daughs(node1, dim=dim1, nodedimD=node1dim1D)
                        # Daughter union selection constraint
                        node1DUconstraint = UnionSelection(node1daughU, nodeattribvar, node1daughvars, problem=problem)
                        self.add_propagator(node1DUconstraint)
                        # Add the daugh variable to the list
                        node1daughUs.append(node1daughU)
                    # Now we have variables representing all of the legal daughters of each node (or its ancestors)
                    # on dim1. We need the union of all of these that are included in up= of node.
                    # A variable for the union:
                    dim1D_ancU = self.svar('{}_{}_D_anc_U'.format(index, label), set(), problem.all_indices)
                    # The union selection constraint:
                    dim1D_ancU_constraint = UnionSelection(dim1D_ancU, nodeequp, node1daughUs, problem=problem)
                    self.add_propagator(dim1D_ancU_constraint)
                    # If nodeattribvar is not empty, the set of daughters of node on label must be included in this set.
                    nodelabel2daughs = nodedim2D['outvars'][label][0]
                    incltruthvar = self.ivar('{}{}_incl?'.format(index, label), {0, 1})
                    ## The inclusion constraint (reified to keep track of its truth value)
                    incl_constraint = ReifiedInclusion(nodelabel2daughs, dim1D_ancU, incltruthvar, problem=problem)
                    self.add_propagator(incl_constraint)
                    ## nodeattribvar => incltruthvar (nothing can be inferred from the truth of incltruthvar)
                    # The logical implication constraint representing the relationship between the value of
                    # nodeattribvar and the inclusion constraint
                    implic_constraint = LogImplication([nodeattribvar, incltruthvar], problem=problem)
                    self.add_propagator(implic_constraint)

class GroupP(Principle):
    """Members of a group must all be present and must be joined on arcs indicated by the groupouts attribute.
    MAKE THIS applies=False BY DEFAULT LATER."""

    def __init__(self, problem, dimension, project=False):
        Principle.__init__(self, problem, dimension, short_name='GrpP', project=project)
        # Dict for storing the possible group ids for each node
        self.nodegids = {}
        # Dict for storing nodes associated with each gid
        self.gidnodes = {}

    def make_variables(self, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        labbrev = self.language.abbrev
        # Check empty nodes as well as explicit nodes?
        for node in problem.get_nodes():
            node_index = node.index
            nodedimD = self.get_nodedimD(node)
            # set of group dicts for all entries; exclude 0
            nodegids = {entry.gids.get(labbrev, 0) for entry in node.entries}
            if 0 in nodegids:
                nodegids.remove(0)
            self.nodegids[node_index] = nodegids
            # Variable for the group id for this node and this language
            if labbrev not in node.groupvars:
                # A node must belong to one group or none
                node.groupvars[labbrev] = self.svar('{}'.format(node_index), set(), nodegids, 0, 1)
            entrydims = [entry.get_lexdim(abbrev) for entry in node.entries]
            groupouts = [lexdim.attribs.get('groupouts') for lexdim in entrydims if lexdim]
            mothergids = [entry.gids.get(labbrev, 0) if (labbrev in entry.gids and labbrev not in entry.gheads) else 0 for entry in node.entries]
#            print('node {}, dimension {}, mothergids {}, groupouts {}'.format(node, abbrev, mothergids, groupouts))
            if any(groupouts):
#                print('Making groupouts', groupouts, 'for node', node)
                grouplabels = [self.get_groupout_labels(lexdim, abbrev) for lexdim in entrydims]
                label_seqvars = [DetSVar('{}{}/{}lab'.format(self.var_pre, node_index, entry_i), labels) \
                                                 for entry_i, labels in enumerate(grouplabels)]
                nodedimD['label_seqvars'] = label_seqvars
                possible_labels = set().union(*[x.get_lower() for x in label_seqvars])
                # For this gid and node, there are groupout attributes, so we
                # need to make variables and constraints.
                # Variable for indices of the labels of the groupouts of this node
                # (later make lexical selection constraint using groupouts attribs)
                nodedimD['grouplabelvar'] = self.svar('{}labs'.format(node_index),
                                                      set(), possible_labels)
                # Variable for indices of within-group daughters
                nodedimD['groupdaughvar'] = self.svar('{}D'.format(node_index),
                                                      set(), problem.max_set - {problem.eos_index, node_index})
                # Variable for group ids of within-group daughters
                nodedimD['groupdaughIDvar'] = self.svar('{}D_ID'.format(node_index), set(), nodegids)
            # This node could also be in a group but have no groupout features. We still
            # have to make sure that at least one of its mothers is in its group.
            if any(mothergids):
            # Variable for union of mothers' group ids
                nodedimD['mothgroupIDvar'] = self.svar('{}M_ID'.format(node_index), set(), nodegids)
#            print('moth group ID var')
#            nodedimD['mothgroupIDvar'].pprint()

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        labbrev = self.language.abbrev
        groupvars = [node.groupvars[labbrev] for node in problem.get_nodes()]
        abbrev = self.dimension.abbrev
        for node in problem.nodes:
            index = node.index
            nodegids = self.nodegids[index]
            if not nodegids:
                # Only make constraints if there are group IDs in this dimension
                continue
            nodedimD = self.get_nodedimD(node)
            entrydims = [entry.get_lexdim(abbrev) for entry in node.entries]
            lexvar = node.lexvar
            groupvar = node.groupvars[labbrev]
#            print('Dimension {}, node {}, nodegids {}, groupvar {}'.format(abbrev, node, nodegids, groupvar))
            # Make the lexical selection constraint for the group var
            seq_vars = [DetSVar('{}{}/{}'.format(self.var_pre, index, entry_i), {entry.gid} if entry.gid else set()) \
                            for entry_i, entry, in enumerate(node.entries)]
            lexsel_constraint = IntSelection(groupvar, lexvar, seq_vars, problem=problem)
            self.add_propagator(lexsel_constraint)
            ## Group is possible for this node
            # If there's a grouplabelvar, make groupout constraints for this node, constraining daughters on particular arcs
            # to have the same group ID as the node.
            grouplabelvar = nodedimD.get('grouplabelvar')
            if grouplabelvar:
                # First create the lexical selection constraint for the groupout labels
                groupout_lexsel = IntSelection(grouplabelvar, lexvar, nodedimD['label_seqvars'],
                                               problem=problem)
                self.add_propagator(groupout_lexsel)
                # Make a union constraint that gathers the indices of the daughters for all within-group labels
                groupdaughvar = nodedimD.get('groupdaughvar')
                daughvars = self.get_label_daughs(node, nodedimD=nodedimD)
                withingroup_daugh_indices = UnionSelection(groupdaughvar, grouplabelvar, daughvars, problem=problem)
                self.add_propagator(withingroup_daugh_indices)
                # Make a union constraint that gathers the group IDs of the daughters for all within-group labels
                groupdaughIDvar = nodedimD.get('groupdaughIDvar')
                withingroup_daugh_ids = UnionSelection(groupdaughIDvar, groupdaughvar, groupvars, problem=problem)
                self.add_propagator(withingroup_daugh_ids)
                # Constrain the union of the within-group daughter GIDs to be the same as the node's GID
                gid_daughgid_eq = Equality([groupvar, groupdaughIDvar], problem=problem)
                self.add_derived_propagator(gid_daughgid_eq)
            mothgroupIDvar = nodedimD.get('mothgroupIDvar')
            if mothgroupIDvar:
                ## This node could be in a group, though it doesn't have any groupout attributes.
                # Make mothgroupIDvar be the union of the group IDs of the node's mothers.
                # The node's mother variable is the selection variable for union selection.
                mothvar = nodedimD['mothvar']
                moth_gids_constraint = UnionSelection(mothgroupIDvar, mothvar, groupvars, problem=problem)
                self.add_propagator(moth_gids_constraint)
                # The node's group var (a set of 1) must be included in mothgroupIDvar
                moth_gid_inclusion = Inclusion([groupvar, mothgroupIDvar], problem=problem)
                self.add_derived_propagator(moth_gid_inclusion)

    def get_groupout_labels(self, lexdim, dim_abbrev):
        """Get ints associated with groupout labels for a node's entry."""
        groupouts = lexdim.get_attrib('groupouts')
        if groupouts:
            return {self.language.get_label_int(label, dim_abbrev) for label in groupouts.keys()}
        else:
            return set()

class EmptyNodeP(Principle):
    """Empty nodes are constrained to be a daughter of their source node or
    to have a 'del' arc from the root.
    MAKE THIS applies=False BY DEFAULT LATER.
    """

    def __init__(self, problem, dimension, project=False):
        Principle.__init__(self, problem, dimension, short_name='ENP', project=project)

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        language = self.language
        for node in problem.empty_nodes:
            # Only apply this principle within source language
            if language in node.languages:
                continue
            if node.complex:
                continue
            nodedimD = self.get_nodedimD(node)
            index = node.index
            # Index of the node that is node's only possible real mother, other than
            # a possible antecedent
            src_index = node.src_node_index
            # Del arcs into node
            delarcsV = nodedimD['invars']['del'][0]
            ## Antecedent mother arcs
            antecMV = EMPTY
            # See if there's a variable for thsese
            antec = nodedimD['invars'].get('antec')
            if antec:
                antecMV = antec[0]
#            print('Antec var', antecMV)
            # Variable for the index of the node's source
            src_iV = DetSVar('{}{}_srcM'.format(self.var_pre, index), {src_index})
            # Variable for the union of src index and the antecedent mothers
            antec_src_U = self.svar('{}_antec_src_U'.format(index),
                                    # 2013.1.18: changed from max_set to all_indices
                                    # (source of antec link can be an empty node)
                                    set(), problem.all_indices - {index})
            # Union constraint for antec_src_U
            antec_src_U_constraint = Union([antec_src_U, src_iV, antecMV], problem=problem)
            self.add_derived_propagator(antec_src_U_constraint)
#            print('antec_src_U {}, constraint {}'.format(antec_src_U, antec_src_U_constraint))
            ## Constraint on node mothers:
            ## EITHER antec_src_U (union of antedecents and source index) 
            ## OR del mothers
            # All mothers of node
            mothersV = nodedimD['mothvar']
            # Int selection constraint for mothers
            mother_selV = self.ivar('{}_M_sel'.format(index), {0, 1})
            mother_or_constraint = IntSelection(mothersV, mother_selV, [antec_src_U, delarcsV], problem=problem)
            self.add_propagator(mother_or_constraint)

class ComplexEmptyNodeP(IFPrinciple):
    """Empty nodes that are constrained to have some relationship (mother, daughter,
    ancestor, descendant) to their trigger node. Still to work out: how this interacts
    with the trigger node's entry, and incorporating the arc label for the relationship."""

    def __init__(self, problem, dimension, project=False):
        IFPrinciple.__init__(self, problem, dimension, short_name='CENP', project=project)

    def make_constraints(self, weight=1, proc_direction=0):
        problem = self.problem
        abbrev = self.dimension.abbrev
        dim1 = self.dimension.dim1
        dim2 = self.dimension.dim2
        for node in problem.empty_nodes:
            if node.complex:
                if_dim = node.if_dim
#                print('if_dim {}, abbrev {}'.format(if_dim, abbrev))
#                trigger_entry = node.trigger_entry_index
                # Only do this if the IF dimension is right
                if node.language != self.get_language1() or self.get_language2() not in node.languages:
#                print('node l1 {}, l2 {}'.format(node.language, node.languages))
#                print('principle l1 {}, l2 {}'.format(self.get_language1(), self.get_language2()))
#                if if_dim != abbrev:
                    continue
                constraint_dim = dim1 if node.rev else dim2
                nodedimD = self.get_nodedimD(node)
                constraint_dimD = node.dims[constraint_dim]
#                print('Constraint dim {}'.format(constraint_dim))
                nodedim1D = node.dims[dim1]
                index = node.index
                # The relation constraint: a string ('mother', 'daughter', ...)
                # (node.rel is a list with the relation string as its first element).
                rel = node.rel[0]
                # Trigger
                trigger_index = node.src_node_index
#                print('{}, trigger index {}, trigger entry {}'.format(node, trigger_index, trigger_index))
                # The node (empty in dim1, full in dim2) must be related by rel
                # to the trigger node on dim2
                if rel == 'daughter':
                    # All mothers of empty node in dim2; this is apparently the only
                    # possibility with "reverse" empty nodes
                    relV = constraint_dimD['mothvar']
                elif rel == 'mother':
                    # All daughters of empty node in dim2
                    relV = constraint_dimD['daughvar']
                elif rel == 'ancestor':
                    # All descendants of empty node in dim2
                    relV = constraint_dimD['downvar']
                elif rel == 'descendant':
                    # All ancestors of empty node in dim2
                    relV = constraint_dimD['upvar']
#                print('Empty rel for {}: {}; relv {}; trigger {}'.format(node, rel, relV, trigger_index))
                if node.rev and rel == 'daughter':
                    # Just change the variable to include only the index of the trigger node
                    # and the EOS index
                    indices = {trigger_index, self.problem.eos_index}
                    relV.set_upper(indices, dstore=self.dstore)
                    relV.set_upper_card(2, dstore=self.dstore)
                else:
                    # The index of the trigger node must be in relV
                    triggerV = DetSVar('{}{}_trig'.format(self.var_pre, index), {trigger_index})
                    incl_constraint = Inclusion([triggerV, relV], problem=problem)
                    self.add_derived_propagator(incl_constraint)

class PrincipleError(Exception):
    '''Class for errors encountered during instantiation of principles.'''

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)

# dimension_class:abbreviation dictionary
DIM_DICT = {d: d.abbrev for d in ArcDimension.__subclasses__() + IFDimension.__subclasses__()}
# abbreviation:dimension_class dictionary
DIM_ABBREV_DICT = {abbrev: dim for dim, abbrev in DIM_DICT.items()}
