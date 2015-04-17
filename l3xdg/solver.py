#   A simplified implementation of Mozart constraint satisfaction, as
#   described in
#
#   Müller, T. (2001). Constraint propagation in Mozart. PhD Dissertation,
#   Universität des Saarlandes.
#
#   Includes selection constraints, as described in
#
#   Duchier, D. (2003). Configuration of labeled trees under lexicalized
#   constraints and principles. Research on Language and Computation, 1,
#   307-336.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within thProjectore
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
# -- With primitive constraints of all types (including selection
#    constraints), naive search (dfs, bfs, exhaustive search) works.
# 2010.08.08 (MG)
# -- Fixed bug that prevented propagators from being kept active during
#    distribution.
# 2010.08.09 (MG)
# -- Fixed additional bug that eliminated propagators during distribution.
# 2011.03.01
# -- Changed Solver so it can use the new search algorithm classes in search.py
#    to generate individual solutions or all solutions.
# 2011.03.25
# -- Constructor for Distributor to control the functions for selecting
#    variables (random by default) and variable values (in order of the values
#    by default).
# 2011.04.18
# -- Fixed CSpace.fixed_point() so it checks whether there are any propagators
#    before checking whether all variables are determined. This handles the situation
#    whether all variables are determined following the distribution step, but
#    some propagators that these variables participate in have to be checked because
#    they may fail with the new values.
# 2011.04.22
# -- CSpaces keep track of a penalty that accrues when propagators fail (the weight
#    of the failed propagator). Search fails only when the penalty exceeds
#    CSpace.max_penalty.
# -- When a changed variable encounters an error when an attempt is made to determine
#    it, the propagator that changed it fails. (Hopefully this will stop happening
#    when propagators are rewritten.)
# 2011.04.25
# -- Once a propagator is entailed or fails in a CSpace, it is not checked again in
#    descendants of that CSpace.
# -- "Lenient" variables need not be determined for a CSpace to succeed.
# 2011.12.26-31
# -- Incorporated projectors.
# 2012.01.22
# -- Distributor select_var function can take dstore into account. Default is now
#    upper_select, which selects on the basis of the length of the variable's upper bound,
#    rather than, ran_select.
# 2012.01.25
# -- Eliminated duplicate active projectors using set instead of list.
# 2012.01.29
# -- "Recursive" projectors are not eliminated when their variables are determined
#    (because they could still cause the CSpace to fail).

import random, time
from . import search
from .constraint import *

# Principle order for sorting projectors
PRINCS = \
[
    'OP', 'PP',                                   # Order
    'TP', 'DDDP', 'VP',                           # Graph, valency
    'AgreeP', 'AgrP', 'GovP', 'ArcAgrP',          # Agreement
    'LEP', 'RevLEP', 'LAB12SP',  'LDEP',          # Interface
    'LMP', 'LBSP', 'LBEP', 'LAEP', 'LABSP',
    'BarriersP', 'IAgreeP', 'XGovP', 'XOrderEqP',
    'GrpP'                                        # Group
    ]

class Solver:
    """A solver has a constraint satisfaction problem and a search algorithm."""

    def __init__(self, csp=None, search_algo=search.BFS()):
        self.search_algo = search_algo
        self.csp = csp

    def make_gen(self, test_verbosity=0, expand_verbosity=0,
                 tracevar=None):
        '''Return a solution generator.'''
        return self.search_algo.gen(self.csp, test_verbosity=test_verbosity, 
                                    expand_verbosity=expand_verbosity, 
                                    tracevar=tracevar)

    def run(self, test_verbosity=0, expand_verbosity=0,
            tracevar=None, timeit=False):
        """Return all solutions."""
#        if test_verbosity or expand_verbosity:
        if self.csp.report:
            print('Running solver for {}'.format(self.csp))
        if timeit:
            t1 = time.time()

        sol_generator = self.make_gen(test_verbosity=test_verbosity, 
                                      expand_verbosity=expand_verbosity, 
                                      tracevar=tracevar)
        solutions = [sol for sol in sol_generator]

        if timeit:
            print("Time: {0:.3f}".format(time.time() - t1))

        return solutions

class CSP(search.Problem):
    """Abstract class for constraint satisfaction problems, a subclass of search Problems.
    XDG is a subclass of this."""

    def __init__(self, name='', dstore=None, distributor=None,
                 project=False, report=0):
        self.name = name
        self.distributor = distributor or Distributor(problem=self)
        self.dstore = dstore or DStore(name=self.name)
        # whether to use projectors instead of propagators
        self.project = project
        self.report = report
        self.add_propagators()
        search.Problem.__init__(self,
                                CSpace(name='', dstore=self.dstore,
                                       propagators=self.propagators,
##                                       projectors=self.projectors,
                                       depth=0, verbosity=0))

    def __repr__(self):
        return "<CSP {}>".format(self.name)

    def add_propagators(self, weaken=None):
        """Create variables, propagators, and projectors."""
        self.propagators = []
        self.projectors = []
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def goal_test(self, state, verbosity=0, tracevar=None):
        state.run(verbosity=verbosity, tracevar=tracevar)
#                  project=self.project)
        return state.status == CSpace.succeeded

    def successor(self, state, verbosity=0):
        """Returns a list of (action, new_state) pairs.
        An action consists of a distribution step, restricting a
        single variable's domain in some way or another. This is represented by
        a pair: (variable, basic_constraint)."""
        return state.distribute(self.distributor,
                                project=self.project,
                                verbosity=verbosity)

    def value(self, state):
        """Value for a state. Low numbers are better.
        Number of undetermined variables in the state's DStore.
        """
#        return len(state.dstore.undetermined)
        return len(state.dstore.get_undet())

    def test_prop(self, state=None, verbosity=0, tracevar=None,
                  traceprops=None, traceprinc=None, timeit=False):
        """Propagate once and print out undetermined variables."""
        if verbosity:
            print('Testing propagation for {}'.format(self))
        state = state or self.initial
        # Trace propagators associated with any principle to be traced
        if not traceprops and traceprinc:
            traceprops = traceprinc.propagators
            # If there's a variable to be traced, filter out propagators that
            # don't have that variable
            if tracevar:
                traceprops = [prop for prop in traceprops if tracevar in prop.variables]
        if timeit:
            t1 = time.time()
        state.run(verbosity=verbosity, tracevar=tracevar, 
                  traceprops=traceprops,
                  project=project)
        if timeit:
            print("Time: {0:.3f}".format(time.time() - t1))
        state.dstore.print_undet()

class CSpace:
    """A computation space (Müller, p.20) contains a DStore and a set of
    propagators. This represents a state in the search space."""

    # Statuses
    running = 0
    succeeded = 1
    failed = 2
    distributable = 3
    skipped = 4

    # Penalty threshold for failure
    max_penalty = .9

    def __init__(self, name='', dstore=None,
                 propagators=None,
#                 projectors=None,
                 # propagators to awaken
                 awaken=None,
                 # penalty so far for failed propagators (in this CSpace
                 # and its ancestors)
                 penalty=0,
                 # propagators that are entailed or have failed in the CSpace
                 entailed = None, failed_props = None,
                 # projectors that have been eliminated because left or right
                 # variables are determined
#                 dead_projectors=None,
                 # projectors whose variables are determined but need to
                 # still be considered because they're recursive
#                 recursive_projectors=None,
                 variables=None, parent=None, depth=0, verbosity=0):
        self.name = name
        self.dstore = dstore
        self.propagators = propagators or []
##        self.projectors = projectors or []
##        self.dead_projectors = dead_projectors or set()
##        self.recursive_projectors = recursive_projectors or set()
##        self.dying_projectors = set()
        # Variables determined on the current iteration
        self.newly_determined = set()
        self.entailed = entailed or []
        # Propagators that have failed but are allowed to
        self.failed_props = failed_props or []
        self.parent = parent
        # Only for debugging?
        self.children = []
        self.status = CSpace.running
        self.variables = variables
        self.depth = depth
        self.penalty = penalty
        if not self.variables:
            self.variables = set()
            for prop in propagators:
                self.variables.update(prop.variables)
#        # Needed for project()
#        self.executed_events = set()
        if verbosity > 1:
            self.dstore.print_undet()
#        elif verbosity:
#            print(' {} has {} undetermined variables'.format(self, len(self.dstore.undetermined)))

    def __repr__(self):
        return "<CS {}/{}>".format(self.name, self.depth)
        
#    def cleanup_vars(self):
#        """Remove all variables that have no associated propagators."""
#        for var in self.variables.copy():
#            if not var.propagators:
#                print('{} has no propagators, removing'.format(var))
#            self.variables.remove(var)

    def print_domains(self):
        """Print domains for all variables in the dstore."""
        print('{} variable domains'.format(self))
        for var in self.variables:
            var.pprint(self.dstore, spaces=2)

    def fixed_point(self, awaken):
        if len(awaken) == 0:
            # No more constraints are awake
            if self.dstore.is_determined():
                # All variables are determined in the dstore or peripheral: success
                self.status = CSpace.succeeded
            else:
                # No more constraints apply: continue search
                self.status = CSpace.distributable
            return True
        # Keep propagating
        return False

    def run(self, verbosity=0, tracevar=None, traceprops=[], cutoff=100,
            # whether to use projectors instead of propagators
            project=False):
        """Run all of the awake propagators repeatedly until a fixed
        point is reached or propagation fails because max_penalty
        is reached."""
        if verbosity:
            s = 'RUNNING {}, penalty: {}, undetermined vars: {}/{}'
            undet = len(self.dstore.undetermined)
            core = len(self.dstore.get_undet())
            print(s.format(self, self.penalty, core, undet-core))
            print('N failed props:', len(self.failed_props))
##        if project:
##            return self.run_projectors(verbosity=verbosity, tracevar=tracevar,
##                                       traceprojs=traceprops, cutoff=cutoff)
##        else:
        awaken = self.propagators
        n = 0
        if verbosity:
            print('PROPAGATION: Iterations (active propagators)')
        while not self.fixed_point(awaken):
            if verbosity:
                if n % 1 == 0:
                    if (n + 1) % 10 == 0:
                        print()
                    print('{}({})'.format(n+1, len(awaken)), end=' ')
                    if tracevar:
                        print()
            if tracevar:
                print('Traced variables:')
                for v in tracevar:
                    v.pprint(dstore=self.dstore, spaces=2)
            awaken = self.propagate(awaken, verbosity=verbosity,
                                    tracevar=tracevar, traceprops=traceprops)
            if awaken == CSpace.failed:
                if verbosity:
                    print()
                    print('PROPAGATION FAILED in this CSpace at {} iterations!'.format(n))
                return False
            n += 1
            if n >= cutoff:
                if verbosity:
                    print()
                    print('HALTING, wakeful propagators')
                    for p in awaken:
                        print(p)
                break
        if verbosity:
            print()
        if verbosity and self.status == CSpace.succeeded:
            print('SUCCEEDED at {} iterations'.format(n))

    def propagate(self, propagators, verbosity=0, tracevar=None, traceprops=[], 
                  show_changed=False):
        """Run all of the awake propagators once.
        tracevar is a variable to trace."""
        awaken = set()
        for propagator in propagators:
            state, changed_vars = propagator.run(dstore=self.dstore, verbosity=verbosity, tracevar=tracevar)
            if propagator in traceprops:
                self.trace_prop(propagator, state, changed_vars)
            if state == Constraint.entailed:
                # Propagator is entailed; add it to the list of those.
                self.entailed.append(propagator)
                # Delete it from awaken if it's already there
                if propagator in awaken:
                    awaken.remove(propagator)

            # Check whether any of the changed vars cannot possibly be determined; if so,
            # the propagator fails
            if state != Constraint.failed:
                for var in changed_vars:
                    try:
                        var.determined(dstore=self.dstore, verbosity=verbosity)
                    except VariableError:
                        if verbosity:
                            print("{} CAN'T BE DETERMINED, SO {} MUST FAIL".format(var, propagator))
                        state = Constraint.failed
                        break

            if state == Constraint.failed:
                # propagator fails; remove it from the entailed or awaken lists if it's there
#                print('PROPAGATOR', propagator, 'FAILED!')
                if propagator in self.entailed:
                    self.entailed.remove(propagator)
                if propagator in awaken:
                    awaken.remove(propagator)
                # penalize the CSpace
                self.penalty += propagator.weight
                # and remember that it failed
                self.failed_props.append(propagator)
#                print('  Appending failed prop; now {} failed'.format(len(self.failed_props)))

            if self.penalty > self.max_penalty:
                # CSpace fails without running other propagators
                if verbosity:
                    print('PENALTY {} EXCEEDS MAXIMUM {}!'.format(self.penalty, self.max_penalty))
                self.status = CSpace.failed
                return CSpace.failed

            # If the propagator succeeds, add the propagators of its variables to awaken
            if state not in [Constraint.failed]:
                for var in changed_vars:
                    if show_changed:
                        print('Var', var)
                    update_props = {p for p in var.propagators if p not in self.entailed and p not in self.failed_props}
                    if var == tracevar and verbosity:
                        print('Adding {} propagators for changed variable {}'.format(len(update_props), tracevar))
                    # Add propagators for changed var to awaken unless those propagators are already entailed
                    # or failed
                    awaken.update(update_props)

        return awaken

    def distribute(self, distributor, project=False, verbosity=0):
        """Creates and returns two new cspaces by cloning the dstore with the distributor."""
        if self.status != CSpace.distributable:
            return []
        if verbosity:
            ndet = len(self.dstore.undetermined)
            print('DISTRIBUTION')
            print('Distributing, undetermined vars {}'.format(ndet))
            for v in list(self.dstore.undetermined)[:5]:
                v.pprint(dstore=self.dstore)
            if ndet > 5:
                print('...')
        # Select a variable and two disjoint basic constraints on it
        var, constraint1, constraint2 = distributor.select(self.dstore, verbosity=verbosity)
        if verbosity:
            print('Distribution constraints: a -- {}, b -- {}'.format(constraint1, constraint2))
        # The propagators of the selected variable (make copies)
        propagators = var.propagators[:]
        # Create the new dstores, applying one of the constraints to each
        new_dstore1 = self.dstore.clone(constraint1, name=self.name+'a', project=project)
        new_dstore2 = self.dstore.clone(constraint2, name=self.name+'b', project=project)
##        if project:
##            newproj1 = constraint1.get_projectors(assign_to_var=False)
##            newproj2 = constraint2.get_projectors(assign_to_var=False)
##        else:
##            newproj1 = newproj2 = []
        # Create a new CSpace for each dstore, preserving the accumulated penalty
        cspace1 = CSpace(name=self.name+'a', depth=self.depth+1,
                         variables=self.variables,
                         propagators=propagators,
##                         projectors=newproj1,
##                         dead_projectors=self.dead_projectors.copy(),
                         penalty=self.penalty,
                         parent=self,
                         dstore=new_dstore1,
                         failed_props=self.failed_props[:],
                         entailed=self.entailed[:],
                         verbosity=verbosity)
        cspace2 = CSpace(name=self.name+'b', depth=self.depth+1,
                         variables=self.variables,
                         propagators=propagators,
##                         projectors=newproj2,
##                         dead_projectors=self.dead_projectors.copy(),
                         penalty=self.penalty,
                         parent=self,
                         dstore=new_dstore2,
                         failed_props=self.failed_props[:],
                         entailed=self.entailed[:],
                         verbosity=verbosity)
        self.children.extend([cspace1, cspace2])
        return [((var, constraint2), cspace2), ((var, constraint1), cspace1)]
        
    def trace_prop(self, propagator, state, changed_vars):
        print('Tracing {}'.format(propagator))
        print('  Resulting state: {}, changed variables: {}'.format(state, changed_vars))

class Distributor:
    """Selects a variable and a non-determined value for the variable, given a DStore.
    Subclasses may use particular algorithms for selecting variables and values.
    """

    def __init__(self, var_select=False, val_select=False, problem=None):
        """Initialize the function for selecting variables, upper_select by default,
        and the function for selecting variable values, starting with smallest by default."""
        self.problem = problem
        if var_select:
            self.var_select = var_select
            # This tag doesn't make any sense but it's just for __repr__
            self.varsel_string = 'spec'
        else:
            self.var_select = Distributor.upper_select
            self.varsel_string = 'upper'
        self.val_select = val_select or Distributor.smallest_select
# (lambda values: values[0])

    def __repr__(self):
        return "<D {}>".format(self.varsel_string)

    # Static methods for variable selection and value selection
    @staticmethod
    def upper_select(vars, dstore=None):
        """Select variables by the length of their upper bounds."""
        return sorted(vars, key=lambda v: len(v.get_upper(dstore=dstore)))[0]

    @staticmethod
    def ran_select(vars, dstore=None):
        return random.choice(vars)

    @staticmethod
    def smallest_select(values):
        """Select smallest value."""
        value_list = list(values)
        value_list.sort()
        return value_list[0]

    def select_var(self, dstore):
        """Return a single undetermined variable by calling the distributor's variable selection function."""
        return self.var_select(dstore.undetermined, dstore)

    def select_values(self, dstore, variable):
        """For a selected variable, select a value by calling the distributor's value selection function,
        and return two sets of values: the selected value and the other values."""
        undecided = variable.get_undecided(dstore=dstore)
        # Split undecided into two non-empty subsets
        if not undecided:
            print("SOMETHING WRONG; {} HAS NO UNDECIDED VALUES".format(variable))
        elem = self.val_select(undecided)
#        value_list = list(undecided)
#        value_list.sort()
#        elem = self.val_select(value_list)
        return {elem}, undecided - {elem}

    def select_constraints(self, dstore, variable, verbosity=0):
        """Return a pair of constraints for the selected variable."""
        subset1, subset2 = self.select_values(dstore, variable)
        if verbosity:
            print(' variable selected: ', end='')
            variable.pprint(dstore=dstore)
        if isinstance(variable, IVar):
            if verbosity:
                print(' values: {}, {}'.format(subset1, subset2))
            return Member(variable, subset1, problem=self.problem), Member(variable, subset2, problem=self.problem)
        else:
            # For an SVar, add subset1 to the lower bound, subtract subset1
            # from the upper bound
            v1 = variable.get_lower(dstore=dstore) | subset1
            v2 = variable.get_upper(dstore=dstore) - subset1
            if verbosity:
                print(' values: {}, {}'.format(subset1, subset2))
            return Superset(variable, v1, problem=self.problem), Subset(variable, v2, problem=self.problem)

    def select(self, dstore, verbosity=0):
        """Returns selected variable and value."""
        var = self.select_var(dstore)
        return (var,) + self.select_constraints(dstore, var, verbosity=verbosity)
