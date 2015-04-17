#   Implementation of variables and domain stores, as described in
#
#   Müller, T. (2001). Constraint propagation in Mozart. PhD Dissertation,
#   Universität des Saarlandes.
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
# 2010.07.24 (MG)
# -- Initially determined variables introduced (subclasses of
#    DeterminedVariable; constants)
# 2010.08.07 (MG)
# -- Variables can now be traced.
# 2010.08.12 (MG)
# -- determine() can now take an int or set so that it can apply to
#    either an int or set variable
# 2010.08.15 (MG)
# -- equals() and cant_equal() permit IVars to be "equal" to SVars
# 2010.08.16 (MG)
# -- Added pattern option to equals() predicates for pattern matching
#    with feature values (tuples); used mainly in EqualitySelection
# 2010.08.17 (MG)
# -- Moved pattern functions to static methods in Variable:
#    patmatch, patequate
# 2010.10.24 (MG)
# -- Pattern methods now use unify_fs (in lex).
# 2010.10.26 (MG)
# -- Fixed pattern methods (equate, patequate, cant_equal)
#    so they use unification instead of strict equality
# 2010.10.31
# -- determine_min() assigns IVar or SVar its minimum value.
# 2010.11.12
# -- strengthen_upper() has test of whether it is compatible with
#    current lower bound.
# 2010.11.12
# -- strengthen_upper() has pattern option so it works with
#    unification over agrs
# 2010.12.12
# -- pattern option added to SVar.determine(): value is determined at the unification
#    of the given value and the current upper domain of the variables. Used in
#    UnionSelection when pattern is True (for GovernmentPrinciple at least).
# 2010.12.18
# -- equate() does not cause determined variable to change its value, e.g.,
#    IVar with value () does not change to value of variable that it unifies with.
# 2011.02.23
# -- Fixed IVar.discard_upper so it discards all values instead of just first.
# 2011.02.25
# -- Some tweaking of feature matching possibilities. elim_specializations() can
#    be called in some cases. Probably still some outstanding issues.
# 2011.04.19
# -- Maximum set cardinality (MAX) increased to 20; should really depend on the sentence.
# 2011.04.22
# -- Variables can be "peripheral": they do not have to be determined for a DStore
#    to be determined. DStore has a method is_determined that takes this into account.
# 2011.04.24
# -- Peripheral variables are those with a weight below Variable.weight_thresh. Weights
#    are set when principles are instantiated.
# 2011.04.25
# -- DStore.is_determined() checks whether all non-peripheral variables are determined,
#    (undetermined contains only peripheral variables).
# 2011.05.15
# -- cant_equal_value() handles pattern matching (I think).
# 2011.05.20
# -- Another fix to cant_equal_value().
# 2011.05.21
# -- Fixes related to constraints between cardinality bounds and domain bounds for set
#    variables (in determined(), strengthen_upper(), strength_lower()).
# 2011.11.11
# -- Variable events
# 2011.12.02
# -- New low-level variable methods for determining the variables: det().
# 2011.12.05
# -- Added variable methods to kill their projectors (in the solver, could also be the
#    dstore).
# 2012.09.15
# -- Changed cant_equal_value (only used for Government Principles) so that it
#    returns False if the lower bound of the variable is empty.
# 2012.09.25
# -- Changed cant_equal and equate to fix lingering bugs in EqualitySelection with
#    propagators (but not projectors).
# 2012.09.29
# -- Changed IVar.equal() so that the variable cannot be changed if the lower bound
#    of the other variable is empty.
# 2012.10.15
# -- Yet another fix to cant_equal() to make EqualitySelection work with propagators.
# 2013.04.05
# -- equate() and cant_equal() take mapped arguments for mappings between languages
#    so that equality is more sophisticated than just simple equality.
# 2013.06.29
# -- Copied to variable.pyx and cythonized.

import random
# For extracting stuff from variable names
import re
from .lex import unify_fs, unify_values, unify_fssets, elim_specializations

# Later make these constants depend on the XDG problem.
MIN = 0
# Not clear what this maximum number of values should actually be...
MAX = 200
ALL = set(range(MAX))
NONE = set()

class DStore:
    """Domain store holding domains for variables. (Really the domains are held in
    dicts kept by the variables.)"""

    def __init__(self, name='', level=0, problem=None, parent=None):
        """This store is a strengthening of parent store if there is one."""
        self.problem = problem
        self.parent = parent
        self.children = []
        self.name = name
        self.level = level
        # Undetermined variables
        self.undetermined = []

    def __repr__(self):
        return '<DS {}/{}>'.format(self.name, self.level)

    def is_determined(self):
        """Are all variables in dstore determined that need to be determined?"""
        for v in self.undetermined:
            if not v.is_peripheral():
                return False
        if self.undetermined:
            print('{} is determined with {} undetermined variables'.format(self, len(self.undetermined)))
        return True
    
    def get_undet(self):
        return [v for v in self.undetermined if not v.is_peripheral()]

    def print_undet(self):
        """Show domains for undetermined variables."""
        undet = self.undetermined
        if undet:
            print('  {} undetermined variables:'.format(self))
            if len(undet) > 25:
                print('    {} variables'.format(len(undet)))
            else:
                for var in undet:
                    var.pprint(self, 4)

    def clone(self, constraint=None, name='', project=False, verbosity=0):
        """Create a new dstore by applying the basic constraint
        to the bindings in this store."""
        new_store = DStore(name=name or self.name, level=self.level+1,
                           problem=self.problem, parent=self)
        self.children.append(new_store)
        new_store.undetermined = self.undetermined[:]
        if not project:
            constraint.infer(dstore=new_store, verbosity=0, tracevar=[])
            for var in constraint.variables:
                # See if the new variable(?s) is now determined
                var.determined(dstore=new_store, verbosity=0)
        return new_store

DS0 = DStore(name='top')

class Variable:
    """Abstract class for variables."""

    # Threshold for "peripheral" variables
    weight_thresh = .5

    def __init__(self, name, problem=None, dstores=None, rootDS=None,
                 # 2011.04.24
                 # Variables with low weights are "peripheral".
                 weight=1,
                 # The principle responsible for creating the variable
                 principle=None):
        self.name = name
        self.problem = problem
        if problem:
            self.problem.add_variable(self)
        self.value = None
        self.max = problem.sentence_length if problem else MAX
        # Normally initialize with a top-level domain store
        self.rootDS = rootDS or DS0
        # Values of this variable in different domain stores
        self.dstores = dstores or {self.rootDS: {}}
        # Add the variable to the list of undetermined variables for
        # the dstore
        self.rootDS.undetermined.append(self)
        self.weight = weight
        # List of propagators that this variable is a parameter for
        self.propagators = []
        self.principle = principle
        # Set of variables that this variable interacts with
        # %% what was this for??
#        self.variables = set()

    ## Four ways a variable may cause a constraint to fail
    def bound_fail(self, dstore=None):
        """Fail if the lower bound is a superset of the upper bound."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def card_fail(self, dstore=None):
        """Fail if the lower cardinality bound is greater than the upper cardinality bound."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))
        
    def upper_bound_card_fail(self, dstore=None):
        """Fail if length of upper bound conflicts with lower cardinality bound."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))
        
    def lower_bound_card_fail(self, dstore=None):
        """Fail if length of lower bound conflicts with upper cardinality bound."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))
        
    def fail(self, dstore=None):
        """Fail one or the other way, or, for IVars, if the domain is empty."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def cost(self, dstore=None):
        """Distance from current state to determined state."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))
        
    def equals(self, var, dstore=None, pattern=False):
        """Does this variable have the same value as var in dstore?
        var could be an SVar."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def kill_projectors(self, solver=None):
        """Kill all of this variable's projectors."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def all_projectors(self):
        """All projectors for this variable."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def get_name(self):
        '''Function used in sorting lists of variables.'''
        return self.name

    def all_equal(self, variables, dstore=None, pattern=False):
        """Do all of these variables have the same value as this in dstore?"""
        return all([self.equals(var, dstore=dstore, pattern=pattern) for var in variables])

    def is_peripheral(self):
        """Is this variable non-essential in solutions?"""
        return self.weight < self.weight_thresh

    def get_dstore(self, dstore):
        """Returns the dictionary of value and domain(s) for dstore."""
        dstore = dstore or self.rootDS
        return self.dstores.get(dstore, {})

    def add_dstore(self, dstore):
        """Adds a domain store to the dstores dict."""
        self.dstores[dstore] = {}

    def get(self, dstore, feature, default=None):
        """Returns a value for feature associated with dstore, recursively
        checking dstore's parent is nothing is found."""
        dstore_dict = self.dstores.get(dstore, {})
        x = dstore_dict.get(feature, None)
        if x != None:
            return x
        parent = dstore.parent
        if parent:
            return self.get(parent, feature, default=default)
        return default

    def set(self, dstore, feature, value):
        """Sets feature to be value in dstore, creating a dict for dstore if one doesn't exist."""
        dstore = dstore or self.rootDS
        dsdict = self.dstores.get(dstore, None)
        if dsdict == None:
            dsdict = {'value': None}
            self.dstores[dstore] = dsdict
        dsdict[feature] = value

    def get_value(self, dstore=None):
        """Return the value of the variable in dstore."""
        dstore = dstore or self.rootDS
        return self.get(dstore, 'value', None)

    def set_value(self, value, dstore=None):
        """Sets the value of the variable in dstore."""
        self.set(dstore, 'value', value)

    def is_determined(self, dstore=None):
        """Is the variable already determined?"""
        return self.get_value(dstore=dstore) is not None

    def init_values(self, dstore=None):
        '''Reinitialize the values and bounds on it.'''
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def incr_rights(self, index):
        """Increment count of projector right-hand sides."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def get_undecided(self, dstore=None):
        """Returns values that may or may not be in the variable."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def determined(self, dstore=None, verbosity=0, constraint=None):
        '''If the variable is determined and doesn't have a value, assign the value.'''
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def det(self, dstore=None, verbosity=0, constraint=None):
        '''Like determined but does not check for failure.'''
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def clash(self, dstore=None):
        '''Is there a clash, given the bounds on the variable's value?'''
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def determine(self, value, dstore=None, constraint=None):
        '''Sets the value of the variable to value.'''
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def determine_min(self, dstore=None, constraint=None):
        '''Sets the value of the variable to its minimum value.'''
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def equate(self, var, mapped=None, pattern=False, dstore=None, constraint=None, reduce=False):
        '''Sets the value of the variable to value.'''
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def get_lower(self, dstore=None):
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def get_upper(self, dstore=None):
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def get_lower_card(self, dstore=None):
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def get_upper_card(self, dstore=None):
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def get_undecided(self, dstore=None):
        """Returns the set of values that may or may not be in the variable."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def strengthen_upper(self, upper2, dstore=None, pattern=False, constraint=None,
                         reduce=False):
        """Strengthens the upper bound by intersecting it with upper2."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def discard_upper(self, value, dstore=None, constraint=None):
        """Discard set or element from upper bound."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def strengthen_lower(self, lower2, dstore=None, constraint=None):
        """Strengthens the lower bound by unioning it with lower2."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def strengthen_lower_card(self, lower2, dstore=None, constraint=None):
        """Raises the lower bound on the cardinality of the set."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def strengthen_upper_card(self, upper2, dstore=None, constraint=None):
        """Lowers the upper bound on the cardinality of the set."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def is_true(self, dstore=None):
        """Is the variable not empty or not 0?"""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

    def is_false(self, dstore=None):
        """Is the variable empty or 0?"""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)

#    def combine_projectors(self):
#        """Combine right-hand sides of projector(s) to yield complex projector."""
#        pass

    @staticmethod
    def get_princ(var):
        """Returns the principle abbreviation portion from a variable name."""
        m = re.search("\|(.*?):", var.name)
        if m:
            return m.groups()[0]

    @staticmethod
    def string_values(value):
        return '{}'.format(value.__repr__() if value != None else '')

    @staticmethod
    def string_range(lower, upper):
        s = '{'
        for i,v in enumerate(upper):
            if i != 0:
                s += ','
            if v not in lower:
                s += '({})'.format(v)
            else:
                s += '{}'.format(v)
        return s + '}'

    # Later put in a separate Pattern class
    @staticmethod
    def patmatch(p1, p2):
        """Do the two patterns (tuples) match?"""
        if not p1 or not p2:
            # Empty tuple matches anything
            return True
        else:
            return unify_fs(p1, p2)

    @staticmethod
    def patequate(pset1, pset2, reduce=False):
        """Constrain pattern set1 to be equal to pattern set2."""
        if pset2 == set() or () in pset2:
            # Since () and set() match anything in pset1, we can't constrain it
            # further.
            return pset1
        else:
            return unify_fssets(pset1, pset2, elim_specs=reduce)

class IVar(Variable):
    """Finite integer variable."""

    def __init__(self, name='', init_domain=None, problem=None,
                 dstores=None, rootDS=None,
                 weight=1, principle=None):
        Variable.__init__(self, name, problem=problem,
                          dstores=dstores, rootDS=rootDS,
                          weight=weight, principle=principle)
        # init_domain could be a list
        if init_domain:
            if not isinstance(init_domain, set):
                init_domain = set(init_domain)
        else:
            init_domain = ALL.copy()
        self.init_domain = init_domain
        if any([isinstance(x, tuple) for x in self.init_domain]) and \
        any([isinstance(x, int) for x in self.init_domain]):
            print('Warning: mixed domain {}: {}'.format(self, self.init_domain))
        # Use default value when value of variable is irrelevant
        self.default_value = min(self.init_domain)
        self.init_values(dstore=self.rootDS)
        self.event = None
        self.projectors = []
        self.rights = 0
        # Compound projectors
        self.comp_proj = None

    def __repr__(self):
        dom = self.get_domain()
#        return '#{0}:{1}'.format(self.name, Variable.string_values(dom))
        return '#{}'.format(self.name)

    def all_projectors(self):
        """All projectors for this variable."""
        return self.projectors

    def cost(self, dstore=None):
        """Cost is one less than length of domain."""
        return len(self.get_domain(dstore=dstore)) - 1

    def incr_rights(self, index):
        self.rights += 1

    def kill_projectors(self, solver=None):
        """Kill all of this variable's projectors."""
        if solver:
            solver.newly_determined.add(self)
#            for p in self.projectors:
#                solver.dying_projectors.add(p)

#    def combine_projectors(self):
#        """Combine right-hand sides of projector(s) to yield complex projector."""
#        proj = CompIntProj(self, [proj.right for proj in self.projectors],
#                           recursive=any([proj.recursive for proj in self.projectors]))
#        self.comp_proj = proj

    def set_event(self, event, card=0, end=0):
        self.event = event

    def get_event(self, card=0, end=0):
        return self.event

    def bound_fail(self, dstore=None):
        """IVars don't have bounds, so can never fail this way."""
        return False

    def card_fail(self, dstore=None):
        """IVars don't have cardinality, so can never fail this way."""
        return False

    def upper_bound_card_fail(self, dstore=None):
        """IVars don't have cardinality bounds."""
        return False
        
    def lower_bound_card_fail(self, dstore=None):
        """IVars don't have cardinality bounds."""
        return False
        
    def fail(self, dstore=None):
        """IVars fail if their domain is empty."""
        return not self.get_domain(dstore=dstore)

    def pprint(self, dstore=None, spaces=0, end='\n'):
        string = '{0}#{1}:{2}'.format(spaces*' ',
                                      self.name,
                                      self.get_value(dstore=dstore) if self.is_determined(dstore=dstore) \
                                          else Variable.string_values(self.get_domain(dstore=dstore)))
        print(string)
        #, end=end)

    def get_domain(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'dom', set())

    def get_undecided(self, dstore=None):
        """Same as the domain for IVars."""
        return self.get_domain(dstore=dstore)

    def set_domain(self, domain, dstore=None):
        self.set(dstore, 'dom', domain)

    def init_values(self, dstore=None):
        # Start over with domain as value of set
        self.set_domain(self.init_domain, dstore=dstore)
        self.set_value(None, dstore=dstore)

    def det(self, check=False, dstore=None, verbosity=0):
        '''Attempt to determine variable.'''
        if verbosity > 1:
            print('Attempting to determine {} for dstore {}'.format(self, dstore))
            print(' domain {}'.format(self.get_domain(dstore=dstore)))
        if not check or len(self.get_domain(dstore=dstore)) == 1:
            val = list(self.get_domain(dstore=dstore))[0]
            self.set_value(val, dstore=dstore)
            if dstore and self in dstore.undetermined:
                dstore.undetermined.remove(self)
#                if verbosity > 1:
#                    print('Determining {} at {}'.format(self, value))
            return True
        return False

    def determined(self, dstore=None, verbosity=0, constraint=None):
        val = self.get_value(dstore=dstore)
        if val != None:
            return val
        if len(self.get_domain(dstore=dstore)) == 1:
            val = list(self.get_domain(dstore=dstore))[0]
            self.set_value(val, dstore=dstore)
            if dstore and self in dstore.undetermined:
                dstore.undetermined.remove(self)
            if verbosity > 1:
                print('  {} is determined at {}'.format(self, val))
            return val
        return False

    def clash(self, dstore=None):
        return len(self.get_domain(dstore=dstore)) == 0

    ## Methods that can change the variable's domain
        
    def determine(self, value, dstore=None, constraint=None):
        """Determine variable at value, returning True if it changes
        in the process."""
        val = self.get_value(dstore=dstore)
        if val != None:
            # Variable is already determined
            return False
        if constraint:
            print('  {} determining {} as {}'.format(constraint, self, value))
        orig_domain = self.get_domain(dstore=dstore)
        self.set_domain({value}, dstore=dstore)
        self.set_value(value, dstore=dstore)
        if dstore and self in dstore.undetermined:
            dstore.undetermined.remove(self)
        if orig_domain != self.get_domain(dstore=dstore):
            return True
        return False

#    def determine_dflt(self, dstore=None, constraint=None):
#        value = self.default_value # min(self.get_domain(dstore=dstore))
#        return self.determine(value, dstore=dstore, constraint=constraint)

    def equals(self, var, dstore=None, pattern=False):
        """Does this variable have the same value as var in dstore?
        var could be an SVar.
        If pattern is True, use 'pattern matching' criteria.
        """
        value = self.get_value(dstore=dstore)
        if value != None:
            var_val = var.get_value(dstore=dstore)
            if var_val == None:
                return False
            if isinstance(var, SVar):
                if var.get_lower_card(dstore=dstore) > 1:
                    return False
                # Use single value in SVar to compare to self
                var_val = list(var_val)[0] if var_val else ()
            if pattern:
                return Variable.patmatch(value, var_val)
            if value == var_val:
                return True
        return False
        
    def cant_equal_value(self, value, dstore=None, pattern=False):
        """Is it impossible for variable to have value?
        Pattern matching may be wrong!"""
        domain = self.get_domain(dstore=dstore)
        if not isinstance(value, set):
            value = {value}
        if pattern and (not domain or unify_fssets(value, domain)):
#        if pattern and (not domain or () in domain):
            return False
        if not domain & value:
            return True
        return False

    def cant_equal(self, var, dstore=None, mapped=None, pattern=False):
        """Is it impossible for self and var to be equal within dstore?"""
#        print('Can', self, 'equal', var, '?')
#        print(' Mapped', mapped)
        domain = self.get_domain(dstore=dstore)

        if isinstance(var, SVar):
#            print('  domain', domain, 'upper', var.get_upper(dstore=dstore))
#            print('  intersection', domain & var.get_upper(dstore=dstore))
            lcard = var.get_lower_card(dstore=dstore)
            # var must be length 1 or 0
            if lcard > 1:
                return True
            # but if it can be 0, then we don't know anything, so return False
            elif lcard == 0:
                return False
            # there must be unifying elements in self's domain and
            # var's upper bound if either is not empty
            var_upper = var.get_upper(dstore=dstore)
            if mapped:
                var_upper = mapped
            if pattern:
                if not var.get_lower(dstore=dstore) \
                   and var_upper \
                   and () not in var_upper \
                   and not unify_fssets(var_upper, domain):
                    return True
            elif not var_upper:
                # If var is empty, equality is meaningless
                return False
            elif not domain or not var_upper:
#                print('  not domain or not upper')
                return True
            elif not (domain & var_upper):
#                print('  empty intersection')
                return True
        else:
            var_domain = var.get_domain(dstore=dstore)
            if mapped:
                var_upper = mapped
            if pattern and not domain or not var_domain:
                return False
            # Domains must share something
            elif not unify_fssets(var_domain, domain):
                return True

        return False

    def equate(self, var, mapped=None, pattern=False, dstore=None, constraint=None, reduce=False):
        """Attempt to equate self with var."""
        sv = isinstance(var, SVar)
        if sv:
            values = var.get_upper(dstore=dstore)
        else:
            values = var.get_domain(dstore=dstore)
        if mapped:
            values = mapped
        if pattern:
            domain = self.get_domain(dstore=dstore)
            new_domain = Variable.patequate(domain, values)
            if len(new_domain) < len(domain):
                if isinstance(self, Determined):
                    # Don't change the value of an IVar that's determined as long as
                    # it matches the given value
                    return True
                if constraint:
                    string = '  {} equating {} with {}; domain1 {}, domain2 {} new domain {}'
                    print(string.format(constraint, self, var, domain, values, new_domain))
                self.set_domain(new_domain, dstore=dstore)
                # This may determine self
                self.determined(dstore=dstore, verbosity=(1 if constraint else 0), constraint=constraint)
                return True
        elif not values:
            # If the set of values for the other variable is empty, we can't change this variable.
            return False
        elif sv and not var.get_lower(dstore=dstore):
            # Added 2012.09.29
            # If the seq variable can be empty, then we can't constrain self yet
            return False
        else:
            return self.strengthen(values, dstore=dstore, constraint=constraint)

    def strengthen(self, values, dstore=None, constraint=None, det=False):
        """Strengthens the domain by intersecting it with values."""
        if not isinstance(values, set):
            values = {values}
        dom = self.get_domain(dstore=dstore)
        if not dom.issubset(values):
            if constraint:
                string = '  {} strengthening {}, domain {} intersected with {}'
                print(string.format(constraint, self, self.get_domain(dstore=dstore), values))
            new_domain = dom & values
            self.set_domain(new_domain, dstore=dstore)
            if det and len(new_domain) == 1:
#                print('Determining', self)
                value = list(new_domain)[0]
                self.set_value(value, dstore=dstore)
                if dstore and self in dstore.undetermined:
                    dstore.undetermined.remove(self)
            return True
        return False

    def discard_value(self, value, dstore=None, constraint=None):
        dom = self.get_domain(dstore=dstore)
        if value in dom:
            if constraint:
                print('  {} discarding {} from {}'.format(constraint, value, dom))
            self.set(dstore, 'dom', dom - {value})
            return True
        return False

    def is_true(self, dstore=None):
        """Is the variable not 0?"""
        return 0 not in self.get_domain(dstore=dstore)

    def is_false(self, dstore=None):
        """Is the variable empty or 0?"""
        return self.get_value(dstore=dstore) is 0 or self.get_domain(dstore=dstore) == {0}

    ### SVar methods which need to make sense for IVars when they appear in selection
    ### constraints
    
    def get_lower(self, dstore=None):
        if self.is_determined(dstore=dstore):
            return self.get_domain(dstore=dstore)
        return set()

    def get_upper(self, dstore=None):
        return self.get_domain(dstore=dstore)

    def get_lower_card(self, dstore=None):
        return 1

    def get_upper_card(self, dstore=None):
        return 1

    def get_undecided(self, dstore=None):
        """Returns the set of values that may or may not be in the variable."""
        return self.get_domain(dstore=dstore)

    def strengthen_upper(self, upper2, dstore=None, pattern=False, constraint=None,
                         reduce=False):
        """Strengthens the upper bound by intersecting it with upper2."""
        return self.strengthen(upper2, dstore=dstore, constraint=constraint)

    def discard_upper(self, value, dstore=None, constraint=None):
        """Discard set or element from upper bound."""
#        value = list(value)[0] if isinstance(value, set) else value
#        return self.discard_value(value, dstore=dstore, constraint=constraint)
        value = value if isinstance(value, set) else {value}
        dom = self.get_domain(dstore=dstore)
        if value & dom:
            new_dom = dom - value
            # If value and upper overlap
            if constraint:
                print('  {} discarding {} from {}'.format(constraint, value, self))
            self.set(dstore, 'dom', new_dom)
            return True
        return False

    def strengthen_lower(self, lower2, dstore=None, constraint=None):
        """Strengthens the lower bound by unioning it with lower2."""
        return False

    def strengthen_lower_card(self, lower2, dstore=None, constraint=None):
        """Raises the lower bound on the cardinality of the set."""
        return False

    def strengthen_upper_card(self, upper2, dstore=None, constraint=None):
        """Lowers the upper bound on the cardinality of the set."""
        return False

class SVar(Variable):
    """Set variable with a lower bound (the current value of the set) and an upper bound
    on its elements and lower and upper bounds on its cardinality."""

    def __init__(self, name='',
                 lower_domain=None, upper_domain=None,
                 lower_card=0, upper_card=MAX,
                 soft_lower_card=None, soft_upper_card=None,
                 problem=None, dstores=None, rootDS=None,
                 weight=1, principle=None):
        Variable.__init__(self, name, problem=problem,
                          dstores=dstores, rootDS=rootDS,
                          weight=weight, principle=principle)
        self.max_set = problem.max_set if problem else ALL
        if lower_domain != None:
            self.lower_domain = lower_domain
        else:
            self.lower_domain = set()
        if upper_domain != None:
            if not isinstance(upper_domain, set):
                upper_domain = set(upper_domain)
            self.upper_domain = upper_domain
        else:
            self.upper_domain = ALL.copy()
        self.init_lower_card = max(lower_card, len(self.lower_domain))
        self.init_upper_card = min(upper_card, len(self.upper_domain))
        self.soft_lower_card = soft_lower_card
        self.soft_upper_card = soft_upper_card
        self.init_values(dstore=self.rootDS)
        self.events = [None, None, None, None]
        self.projectors = [[], [], [], []]
        self.rights = [0, 0, 0, 0]
        # Compound projectrs
        self.comp_proj = [None] * 4

    def __repr__(self):
        return '${}'.format(self.name)

    ## Initializing bounds

    def init_values(self, dstore=None):
        self.set_lower(self.lower_domain, dstore=dstore)
        self.set_upper(self.upper_domain, dstore=dstore)
        self.set_lower_card(self.init_lower_card, dstore=dstore)
        self.set_upper_card(self.init_upper_card, dstore=dstore)
        self.set_value(None, dstore=dstore)

    def set_lower(self, lower, dstore=None):
        self.set(dstore, 'lower', lower)

    def set_upper(self, upper, dstore=None):
        self.set(dstore, 'upper', upper)

    def set_lower_card(self, lower_card, dstore=None):
        self.set(dstore, 'lower_card', lower_card)

    def set_upper_card(self, upper_card, dstore=None):
        self.set(dstore, 'upper_card', upper_card)

    # Soft cardinality bounds

    def get_soft_card(self, upper=False):
        if upper:
            return self.get_soft_upper_card()
        else:
            return self.get_soft_lower_card()

    def get_soft_lower_card(self):
        return self.soft_lower_card

    def get_soft_upper_card(self):
        return self.soft_upper_card

    def all_projectors(self):
        """All projectors for this variable."""
        return self.projectors[0] + self.projectors[1] + self.projectors[2] + self.projectors[3]

    def incr_rights(self, index):
        self.rights[index] += 1

    def cost(self, dstore=None):
        """Cost is difference between upper and lower bounds.
        (Could also be difference between upper and lower cardinality bounds.)
        """
        return len(self.get_upper(dstore=dstore)) - len(self.get_lower(dstore=dstore))

    def kill_projectors(self, solver=None):
        """Kill all of this variable's projectors."""
        if solver:
            solver.newly_determined.add(self)
#            for pp in self.projectors:
#                solver.dying_projectors.update(pp)

##        if solver:
##            for projs in self.projectors:
##                for p in projs:
##                    if p.recursive:
##                        solver.recursive_projectors.add(p)
##                    else:
##                        solver.dead_projectors.add(p)
#extend([p for p in projs if not p.recursive])

    ## Events
    ## self.events: [bottom_bound, top_bound, bottom_card, top_card]

    def set_event(self, event, card=0, end=0):
        self.events[card * 2 + end] = event

    def get_event(self, card=0, end=0):
        return self.events[card * 2 + end]

    ## Three ways a variable may cause a constraint to fail
    def bound_fail(self, dstore=None):
        """Fail if the lower bound includes any elements not in the upper bound."""
        return self.get_lower(dstore=dstore) - self.get_upper(dstore=dstore)

    def card_fail(self, dstore=None):
        """Fail if the lower cardinality bound is greater than the upper cardinality bound."""
        return self.get_lower_card(dstore=dstore) > self.get_upper_card(dstore=dstore)

    def upper_bound_card_fail(self, dstore=None):
         """Fail if the length of upper bound < lower card."""
         return len(self.get_upper(dstore=dstore)) < self.get_lower_card(dstore=dstore)

    def lower_bound_card_fail(self, dstore=None):
        """Fail if length of lower bound > upper card."""
        return len(self.get_lower(dstore=dstore)) > self.get_upper_card(dstore=dstore)
        
    def fail(self, dstore=None):
        """Fail in one of three ways."""
        return self.bound_fail(dstore=dstore) or self.card_fail(dstore=dstore)
#            or self.bound_card_fail(dstore=dstore)
        
    def pprint(self, dstore=None, spaces=0, end='\n'):
        string = '{0}${1}:{2}|{3},{4}|'.format(spaces*' ',
                                         self.name,
                                         Variable.string_range(self.get_lower(dstore=dstore),
                                                               self.get_upper(dstore=dstore)),
                                         self.get_lower_card(dstore=dstore),
                                         self.get_upper_card(dstore=dstore))
        print(string)
        #, end=end)

    @staticmethod
    def fromIVar(ivar):
        iv_det = ivar.determined(dstore=ivar.rootDS)
        if iv_det is not False:
            val = {ivar.get_value(dstore=ivar.rootDS)}
            lower = val
            upper = val
        else:
            lower = set()
            upper = ivar.init_domain

        svar = SVar(name='=' + ivar.name, lower_domain=lower, upper_domain=upper,
                    lower_card=1, upper_card=1, problem=ivar.problem,
                    rootDS=ivar.rootDS)

        if iv_det is not False:
            # ivar is determined, so svar must be too
            svar.determine(upper, dstore=ivar.rootDS)

        return svar

    def equals(self, var, dstore=None, pattern=False):
        """Does this variable have the same value as var in dstore?
        var could be an IVar."""
        value = self.get_value(dstore=dstore)
        var_val = var.get_value(dstore=dstore)
        is_ivar = isinstance(var, IVar)
        if value != None and var_val != None:
            if pattern:
                if len(value) > 1:
                    # Pattern matching only works for single tuples
                    return False
                else:
                    value = () if not value else list(value)[0]
                    if not is_ivar:
                        var_val = () if not var_val else list(var_val)[0]
                    return Variable.patmatch(value, var_val)
            elif is_ivar:
                var_val = {var_val} if var_val else set()
            if value == var_val:
                return True
        return False

    def cant_equal_value(self, value, dstore=None, pattern=False):
        """Is it impossible for variable to have value?
        Only used in SimpleEqualitySelection which is only used in the
        two Government principles.
        Pattern matching may be wrong!!!"""
        if not isinstance(value, set):
            value = {value}
        upper = self.get_upper(dstore=dstore)
        lower = self.get_lower(dstore=dstore)
        # If it's possible that the variable is empty, it can equal anything
        # (by definition??).
        if not lower:
            return False
        if pattern and unify_fssets(value, upper):
            return False
        if upper and not value & upper:
            return True
        return False

    def cant_equal(self, var, dstore=None, mapped=None, pattern=False):
        """Is it impossible for self and var to be equal within dstore?"""
        print('Can {} equal {}?'.format(self, var))
        print(' mapped {}'.format(mapped))
        upper = self.get_upper(dstore=dstore)
        if isinstance(var, IVar):
            # self must be length 1 or 0
            if self.get_lower_card(dstore=dstore) > 1:
                return True
            # there must be a common element in self's domain and
            # var's upper bound unless both are empty
            var_domain = var.get_domain(dstore=dstore)
            if mapped:
                var_domain = mapped
            if pattern:
                if upper and () not in upper \
                   and not self.get_lower(dstore=dstore) \
                   and not unify_fssets(var_domain, upper):
                    return True
            elif var_domain:
                if not var_domain & upper:
                    return True
            elif upper:
                # If one is empty, the other must be
                return True
        else:
            var_upper = var.get_upper(dstore=dstore)
            if mapped:
                var_upper = mapped
            if pattern and var.get_lower_card(dstore=dstore) > 1:
                return True
            # Upper bounds must share something unless both are empty
            elif upper:
                if not unify_fssets(var_upper, upper):
                    return True
            elif var_upper:
                # If one is empty, the other must be
                return True

        return False

    def get_lower(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'lower')

    def get_upper(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'upper')

    def get_lower_card(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'lower_card', 0)

    def get_upper_card(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'upper_card', MAX)

    def get_undecided(self, dstore=None):
        """Returns the set of values that may or may not be in the variable."""
        dstore = dstore or self.rootDS
        return self.get_upper(dstore=dstore) - self.get_lower(dstore=dstore)

    def det(self, dstore=None, check=False, verbosity=0):
        '''Attempt to determine variable without changing any of the
        components.
        '''
#        if verbosity > 1:
#            print('  Attempting to determine', self, 'for dstore', dstore)
#            print(' upper', self.get_upper(dstore=dstore),
#                  'lower', self.get_lower(dstore=dstore),
#                  'upper card', self.get_upper_card(dstore=dstore),
#                  'lower card', self.get_lower_card(dstore=dstore))
        if not check or \
                (self.get_lower(dstore=dstore) == self.get_upper(dstore=dstore) and \
                     self.get_upper_card(dstore=dstore) == self.get_lower_card(dstore=dstore)):
            value = self.get_lower(dstore=dstore)
            self.set_value(value, dstore=dstore)
            if dstore and self in dstore.undetermined:
                dstore.undetermined.remove(self)
#            if verbosity > 1:
#                print('  Determining {} at {}'.format(self, value))
            return True
        return False
            
#        def determined_help(value, dst, verb):
#            lower_card = self.get_lower_card(dstore=dst)
#            upper_card = self.get_upper_card(dstore=dst)
#            self.set_value(value, dstore=dst)
#            self.set_lower(value, dstore=dst)
#            self.set_upper(value, dstore=dst)
#            self.set_lower_card(value_card, dstore=dst)
#            self.set_upper_card(value_card, dstore=dst)
#            if dst:
#                dst.undetermined.remove(self)
#            return value
#        lower = self.get_lower(dstore=dstore)
#        upper = self.get_upper(dstore=dstore)
#        if lower == None or upper == None:
#            return False
#        # If upper and lower bounds are equal, determine at either
#        if lower == upper:
#            return determined_help(lower, dstore, verbosity)
#        # Combine cardinality and set bounds to determine
#        # If the length of the upper bound is <= the lower cardinality bound,
#        # then make the upper bound the value
#        if len(upper) <= self.get_lower_card(dstore=dstore):
#            return determined_help(upper, dstore, verbosity)
#        if len(lower) >= self.get_upper_card(dstore=dstore):
#            return determined_help(lower, dstore, verbosity)
#        return False

    def determined(self, dstore=None, constraint=None, verbosity=0):
        val = self.get_value(dstore=dstore)
        if val != None:
            return val
        def determined_help(value, dst, verb):
            value_card = len(value)
            lower_card = self.get_lower_card(dstore=dst)
            upper_card = self.get_upper_card(dstore=dst)
            if value_card < lower_card:
                s = "{} lowering lower card for {} to {}, less than previous value {}"
                raise(VariableError(s.format(constraint, self, value_card, lower_card)))
            if value_card > upper_card:
                s = "{} raising upper card for {} to {}, greater than previous value {}"
                raise(VariableError(s.format(constraint, self, value_card, upper_card)))
            self.set_value(value, dstore=dst)
            self.set_lower(value, dstore=dst)
            self.set_upper(value, dstore=dst)
            self.set_lower_card(value_card, dstore=dst)
            self.set_upper_card(value_card, dstore=dst)
            if verb > 1:
                print('  {} is determined at {}'.format(self, value))
            if dst:
                dst.undetermined.remove(self)
            return value
        lower = self.get_lower(dstore=dstore)
        upper = self.get_upper(dstore=dstore)
        if lower == None or upper == None:
            return False
        # If upper and lower bounds are equal, determine at either
        if lower == upper:
            return determined_help(lower, dstore, verbosity)
        # Combine cardinality and set bounds to determine
        # If the length of the upper bound is <= the lower cardinality bound,
        # then make the upper bound the value
        if len(upper) <= self.get_lower_card(dstore=dstore):
            return determined_help(upper, dstore, verbosity)
        if len(lower) >= self.get_upper_card(dstore=dstore):
            return determined_help(lower, dstore, verbosity)
        return False

    def clash(self, dstore=None):
        return not self.get_lower(dstore=dstore).issubset(self.get_upper(dstore=dstore))

    ## Methods that can change the variable's set bounds or cardinality bounds
        
    def determine(self, value, dstore=None, pattern=False, constraint=None):
        """If pattern is True, determine at unification of value and upper bound."""
        if self.is_determined(dstore=dstore):
            return False
        value = value if isinstance(value, set) else {value}
        orig_upper = self.get_upper(dstore=dstore)
        orig_lower = self.get_lower(dstore=dstore)
        upper = self.get_upper(dstore=dstore)
        if pattern:
            value = Variable.patequate(value, upper)
            if len(value) > self.get_upper_card(dstore=dstore):
                return False
        if not value.issubset(orig_upper):
            # Variable can't be determined at this value
            return False
        if constraint:
            print('  {} determining {} as {}'.format(constraint, self, value))
        val_card = len(value)
        self.set_lower(value, dstore=dstore)
        self.set_upper(value, dstore=dstore)
        self.set_value(value, dstore=dstore)
        self.set_lower_card(val_card, dstore=dstore)
        self.set_upper_card(val_card, dstore=dstore)
        if dstore and self in dstore.undetermined:
            dstore.undetermined.remove(self)
        if orig_upper != value or orig_lower != value:
            return True
        return False

    def determine_min(self, dstore=None, constraint=None):
        value = self.get_lower(dstore=dstore)
        return self.determine(value, dstore=dstore, constraint=constraint)

    def equate(self, var, mapped=None, pattern=False, dstore=None, constraint=None, reduce=False):
        """Attempt to equate self with var."""
        var_upper = var.get_domain(dstore=dstore) if isinstance(var, IVar) else var.get_upper(dstore=dstore)
        if mapped:
            var_upper = mapped
        var_lower = set() if isinstance(var, IVar) else var.get_lower(dstore=dstore)

        if pattern:
            upper = self.get_upper(dstore=dstore)
            new_upper = Variable.patequate(upper, var_upper)
            if new_upper != upper:
                if constraint:
                    string = '  {} equating {} with {}'
                    print(string.format(constraint, self, var))
                self.set_upper(new_upper, dstore=dstore)
                return True
            return False
        else:
            upper_changed = self.strengthen_upper(var_upper, dstore=dstore, constraint=constraint)
            lower_changed = self.strengthen_lower(var_lower, dstore=dstore, constraint=constraint)
            return upper_changed or lower_changed

    def strengthen_upper(self, upper2, dstore=None, pattern=False, constraint=None,
                         reduce=False, det=False):
        """Strengthens the upper bound by intersecting it with upper2, or if pattern
        is True, by unifying it with upper2.
        If det is True, attempt to determine variable.
        """
        upper = self.get_upper(dstore=dstore)
        if not isinstance(upper, set):
            print("{}'s upper {} is not set".format(self, upper))
        if not upper.issubset(upper2):
            # Use unification if pattern is True; !!! for now assume this always succeeds
            new_upper = unify_fssets(upper, upper2) if pattern else upper.intersection(upper2)
            lower_card = self.get_lower_card(dstore=dstore)
            if pattern and reduce:
                elim_specializations(new_upper)
            if new_upper == upper:
                return False
            lower = self.get_lower(dstore=dstore)
            if not lower.issubset(new_upper) and constraint:
                s = 'Warning: attempting to change upper bound of {} to {}, which is not a superset of lower bound {}'
                print(s.format(self, new_upper, lower))
            if len(new_upper) < lower_card and constraint:
                s = 'Warning: attempting to change upper bound of {} to {}, which is smaller than lower card {}'
                print(s.format(self, new_upper, lower_card))
            if constraint:
                s = '  {} strengthening upper bound of {} ({}) with {}, now {}'
                print(s.format(constraint, self, upper, upper2, new_upper))
            self.set_upper(new_upper, dstore=dstore)
            if det:
                if new_upper == lower:
#                    print('Determining', self)
                    val_len = len(lower)
                    self.set_value(lower, dstore=dstore)
                    self.set_lower_card(val_len, dstore=dstore)
                    self.set_upper_card(val_len, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        dstore.undetermined.remove(self)
                elif len(new_upper) == lower_card:
                    val_len = lower_card
                    self.set_lower(new_upper, dstore=dstore)
                    self.set_value(new_upper, dstore=dstore)
                    self.set_upper_card(val_len, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        dstore.undetermined.remove(self)
            return True
        return False

    def discard_upper(self, value, dstore=None, constraint=None):
        """Discard set or element from upper bound."""
        upper = self.get_upper(dstore=dstore)
        value = value if isinstance(value, set) else {value}
        if value & upper:
            new_upper = upper - value
            lower = self.get_lower(dstore=dstore)
            if len(new_upper) < len(lower) and constraint:
                s = 'Warning: attempting to discard {} from upper bound {} of {}, making it smaller than lower bound {}'
                print(s.format(value, upper, self, lower))
            # If value and upper overlap
            if constraint:
                print('  {} discarding {} from {}'.format(constraint, value, self))
            self.set_upper(new_upper, dstore=dstore)
            return True
        return False

    def strengthen_lower(self, lower2, dstore=None, constraint=None, det=False):
        """Strengthens the lower bound by unioning it with lower2."""
        lower = self.get_lower(dstore=dstore)
#        if constraint:
#            print('  {} attempting to strengthen lower bound of {} with {}'.format(constraint, self, lower2))
        if not lower.issuperset(lower2):
            new_lower = lower.union(lower2)
            upper = self.get_upper(dstore=dstore)
            upper_card = self.get_upper_card(dstore=dstore)
            if not new_lower.issubset(upper) and constraint:
                s = 'Warning: attempting to change lower bound of {} to {}, which is not a subset of upper bound {}'
                print(s.format(self, new_lower, upper))
            if len(new_lower) > upper_card and constraint:
                s = 'Warning: attempting to change lower bound of {} to {}, which is greater than upper card {}'
                print(s.format(self, new_lower, upper_card))
            if constraint:
                print('  {} strengthening lower bound of {} with {}'.format(constraint, self, lower2))
            self.set_lower(new_lower, dstore=dstore)
            if det:
                if new_lower == upper and upper_card == self.lower_card(dstore=dstore):
#                    print('Determining', self)
#                    val_len = len(upper)
                    self.set_value(upper, dstore=dstore)
#                    self.set_lower_card(val_len, dstore=dstore)
#                    self.set_upper_card(val_len, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        dstore.undetermined.remove(self)
#                elif len(new_lower) == upper_card:
#                    val_len = upper_card
#                    self.set_upper(new_lower, dstore=dstore)
#                    self.set_value(new_lower, dstore=dstore)
#                    self.set_lower_card(val_len, dstore=dstore)
#                    if dstore and self in dstore.undetermined:
#                        dstore.undetermined.remove(self)
            return True
        return False

    def strengthen_lower_card(self, lower2, dstore=None, constraint=None, det=False):
        """Raises the lower bound on the cardinality of the set."""
        if lower2 > self.get_lower_card(dstore=dstore):
            if constraint:
                print('  {} raising lower cardinality bound of {} to {}'.format(constraint, self, lower2))
            self.set_lower_card(lower2, dstore=dstore)
#            if det:
#                upper_card = self.get_upper_card(dstore=dstore)
#                if lower2 == upper_card:
#                    upper = self.get_upper(dstore=dstore)
#                    if len(upper) == upper_card:
#                        # Determine
#                        self.set_lower(upper, dstore=dstore)
#                        self.set_value(upper, dstore=dstore)
#                        if dstore and self in dstore.undetermined:
#                            dstore.undetermined.remove(self)
            return True
        return False

    def strengthen_upper_card(self, upper2, dstore=None, constraint=None, det=False):
        """Lowers the upper bound on the cardinality of the set."""
        if upper2 < self.get_upper_card(dstore=dstore):
            if constraint:
                print('  {} lowering upper cardinality bound of {} to {}'.format(constraint, self, upper2))
            self.set_upper_card(upper2, dstore=dstore)
            if det:
                lower_card = self.get_lower_card(dstore=dstore)
                if upper2 == lower_card:
                    lower = self.get_lower(dstore=dstore)
                    if len(lower) == lower_card:
                        # Determine
                        self.set_upper(lower, dstore=dstore)
                        self.set_value(lower, dstore=dstore)
                        if dstore and self in dstore.undetermined:
                            dstore.undetermined.remove(self)
            return True
        return False

    def is_true(self, dstore=None):
        """Is the variable not the empty set?"""
        return self.get_lower(dstore=dstore) != set() or self.get_lower_card(dstore=dstore) > 0

    def is_false(self, dstore=None):
        """Is the variable bound to the empty set?"""
        return self.get_value(dstore=dstore) == set()

##class LVar(Variable):
##    """List variable, elements are IVars (whose values may be tuples as well as ints)."""
##
##    def __init__(self, name='', variables=None,
##                 problem=None, dstores=None, rootDS=None,
##                 weight=1):
##        Variable.__init__(self, name, problem=problem,
##                          dstores=dstores, rootDS=rootDS,
##                          weight=weight)
##        self.variables = variables or []
##        self.length = len(self.variables)
##        self.init_values(dstore=self.rootDS)
##
##    def __repr__(self):
##        return '#[{}]'.format(self.name)
##
##    def pprint(self, dstore=None, spaces=0, end='\n'):
##        string = '{}#['
##        values = [spaces*' ', self.name]
##        for var in self.variables:
##            string += ' {}'
##            values.append(Variable.string_values(var.get_domain(dstore=dstore)))
##        string += ' ]'
##        formatted = string.format(*values)
##        print(formatted)
##        #, end=end)
##
##    def get_domain(self, index, dstore=None):
##        return self.variables[index].get_domain(dstore=dstore)
##
##    def get_undecided(self, index, dstore=None):
##        return self.get_domain(index, dstore=dstore)
##
##    def set_domain(self, domain, index, dstore=None):
##        self.variables[index].set_domain(domain, dstore=dstore)
##
##    def init_values(self, dstore=None):
##        # Start over with domain as value of set
##        for var in self.variables:
##            var.init_values(dstore=dstore)
##
##    def determined(self, dstore=None, verbosity=0, constraint=None):
##        result = []
##        for var in self.variables:
##            val = var.get_value(dstore=dstore)
##            if val != None:
##                result.append(val)
##            elif len(var.get_domain(dstore=dstore)) == 1:
##                val = list(var.get_domain(dstore=dstore))[0]
##                var.set_value(val, dstore=dstore)
##                if dstore and var in dstore.undetermined:
##                    dstore.undetermined.remove(var)
##                if verbosity > 1:
##                    print('  {} is determined at {}'.format(var, val))
##                result.append(val)
##            else:
##                return False
##        self.set_value(result, dstore=dstore)
##        if dstore and self in dstore.undetermined:
##            dstore.undetermined.remove(self)
##        if verbosity > 1:
##            print('  {} is determined at {}'.format(self, result))
##        return result
##
##    def clash(self, dstore=None):
##        return any([var.clash(dstore=dstore) for var in self.variables])
##
##    ## Methods that can change the variable's domain
##        
##    def determine(self, values, dstore=None, constraint=None):
##        if self.is_determined(dstore=dstore):
##            # The variable is already determined
##            return False
##        changed = False
##        if constraint:
##            print('  {} determining {} as {}'.format(constraint, self, values))
##        res = []
##        for var, val in zip(self.variables, values):
##            current_val = var.get_value(dstore=dstore)
##            if current_val == None:
##                orig_domain = var.get_domain(dstore=dstore)
##                var.set_domain({val}, dstore=dstore)
##                var.set_value(val, dstore=dstore)
##                if dstore and var in dstore.undetermined:
##                    dstore.undetermined.remove(var)
##                if orig_domain != var.get_domain(dstore=dstore):
##                    changed = True
##        self.set_value(values, dstore=dstore)
##        if dstore and self in dstore.undetermined:
##            dstore.undetermined.remove(self)
##        return changed
##
##    def strengthen(self, values, index, dstore=None, constraint=None):
##        """Strengthens the set of values by intersecting it with values."""
##        return self.variables[index].strengthen(values, dstore=dstore, constraint=constraint)
##
##    def discard_value(self, value, index, dstore=None, constraint=None):
##        return self.variables[index].discard_value(value, dstore=dstore, constraint=constraint)

class Determined(Variable):
    """Pre-determined variable. If DStore is not specified in constructor,
    the variable is determined in all DStores. Should not be modified.
    The value of peripheral for Determined variables is irrelevant."""

    def __init__(self, value, dstore=None):
        self.dstore = dstore
        if self.dstore:
            self.determine(value, dstore=dstore)
        else:
            self.value = value
        self.initialized = True

    def set(self, dstore, feature, value):
        """Override set in Variable to prevent changes."""
        if self.initialized:
             # This message should print out under some verbosity conditions.
#            s = 'Warning: attempting to change pre-determined variable {}, feature: {}, value: {}, orig value: {}'
#            print(s.format(self, feature, value, self.get(dstore, feature)))
            return False

    def is_determined(self, dstore=None):
        return True

class DetIVar(Determined, IVar):

    def __init__(self, name='', value=0, dstore=None):
        Variable.__init__(self, name, rootDS=dstore)
        Determined.__init__(self, value, dstore)
        # value could be the empty set
        self.init_domain = value if isinstance(value, set) else {value}
        self.default_value = value

    def __repr__(self):
        return '#!{}'.format(self.name)

    def incr_rights(self, index):
        pass

    def pprint(self, dstore=None, spaces=0, end='\n'):
        string = '{0}#!{1}:{2}'.format(spaces*' ', self.name, self.get(dstore, 'value'))
        print(string)
        #, end=end)

    def cost(self, dstore=None):
        return 0

    def determined(self, dstore=None, verbosity=0, constraint=None):
        if self.dstore:
            return IVar.determined(self, dstore=dstore, verbosity=verbosity, constraint=constraint)
        return self.value

    def get(self, dstore, feature, default=None):
        if self.dstore:
            return IVar.get(self, dstore, feature, default=default)
        if feature == 'value':
            return self.value
        if feature == 'dom':
            if isinstance(self.value, set):
                return self.value
            else:
                return {self.value}

class DetSVar(Determined, SVar):

    def __init__(self, name='', value=set(), dstore=None):
        Variable.__init__(self, name, rootDS=dstore)
        Determined.__init__(self, value, dstore)
        self.lower_domain = value
        self.upper_domain = value
        self.init_upper_card = len(value)
        self.init_lower_card = len(value)

    def __repr__(self):
        return '$!{}'.format(self.name)

    def incr_rights(self, index):
        pass

    def pprint(self, dstore=None, spaces=0, end='\n'):
        string = '{0}$!{1}:{2}'.format(spaces*' ', self.name, self.get(dstore, 'value'))
        print(string)
        #, end=end)

    def cost(self, dstore=None):
        return 0

    def determined(self, dstore=None, verbosity=0, constraint=None):
        if self.dstore:
            return SVar.determined(self, dstore=dstore, verbosity=verbosity, constraint=constraint)
        return self.value

    def get(self, dstore, feature, default=None):
        if self.dstore:
            return SVar.get(self, dstore, feature, default=default)
        if feature in {'value', 'lower', 'upper'}:
            return self.value
        if feature in {'lower_card', 'upper_card'}:
            return len(self.value)

class VariableError(Exception):
    '''Class for errors encountered when attempting to execute an event on a variable.'''

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)

# Constant variables, determined in all DStores
EMPTY = DetSVar("empty", set())
ZERO_SET = DetSVar("zero", {0})

ZERO_TUPLE_SET = DetSVar('{(0)}', {(0,)})
ZERO_TUPLE = DetIVar('(0)', (0,))

ZERO = DetIVar('zero', 0)
ONE = DetIVar('one', 1)

EMPTY_TUPLE_SET = ZERO_TUPLE_SET
# DetSVar('{()}', {()})
EMPTY_TUPLE = ZERO_TUPLE
#DetIVar('()', ())
