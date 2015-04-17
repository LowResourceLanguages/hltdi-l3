#   
#   Hiiktuu CS: what is needed to implement l3 style constraint satisfaction
#   using the lexicon/grammars created.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2014, HLTDI <gasser@cs.indiana.edu>
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
# =========================================================================

# 2014.04.26
# -- Created
# 2014.05.11
# -- SearchState class created, so that Solver doesn't have to do double-duty.
# 2014.05.15
# -- Search implemented in Solver.

from .constraint import *
import queue, random

class Solver:
    """A solver for a constraint satisfaction problem, actually a state in the search space."""

    id = 0

    running = 0
    succeeded = 1
    failed = 2
    distributable = 3
    skipped = 4

    def __init__(self, constraints, dstore, name='',
                 description='', verbosity=0):
        self.constraints = constraints
        # Used in solver's printname
        self.description = description
        # Solver (state) that generated this one
        self.verbosity=verbosity
        self.id = Solver.id
        self.name = name or "({})={}=".format(description, self.id)
        self.init_state = SearchState(solver=self, dstore=dstore,
                                      constraints=constraints,
                                      verbosity=verbosity)
        Solver.id += 1

    def __repr__(self):
        return "Solver{}".format(self.name)

    def generator(self, cutoff=100, initial=None,
                  test_verbosity=False, expand_verbosity=False,
                  tracevar=None):
        '''A generator for solutions. Uses best-first search.'''
        tracevar = tracevar or []
        fringe = queue.PriorityQueue()
        init_state = initial or self.init_state
        fringe.put((init_state.get_value(), init_state))
        n = 0
        solutions = []
        ambiguity = False
        while not fringe.empty() and n < cutoff:
            if n > 0 and not ambiguity:
                if expand_verbosity:
                    print("Ambiguity: expanding from best state")
                ambiguity = True
            if (n+1) % 50 == 0 or test_verbosity or expand_verbosity:
                if test_verbosity or expand_verbosity:
                    print()
                print('>>>> SEARCH STATE {} <<<<'.format(n+1))
            if n >= cutoff:
                print('STOPPING AT CUTOFF')
            priority, state = fringe.get()
            # Goal test for this state
            state.run(verbosity=test_verbosity, tracevar=tracevar)
            if state.status == SearchState.succeeded:
                # Return this state
                yield state
            # Expand to next states if distributable
            if state.status == SearchState.distributable:
                for attribs, next_state in self.distribute(state=state, verbosity=expand_verbosity):
                    val = next_state.get_value()
                    # Add next state where it belongs in the queue
                    fringe.put((val, next_state))
            n += 1
        if test_verbosity or expand_verbosity:
            print()
            print('>>>> HALTED AT SEARCH STATE', n, '<<<<')

    def select_variable(self, variables, dstore=None, verbosity=0):
        """One possibility for selecting variables to branch on:
        prefer larger upper domains."""
        return sorted(variables, key=lambda v: len(v.get_upper(dstore=dstore)))[0]

    def split_var_values(self, variable, dstore=None, verbosity=0):
        """For a selected variable, select a value by calling the value selection function,
        and return two sets of values: the selected value and the other values. Assumes
        variable is a set or int variable."""
        undecided = variable.get_undecided(dstore=dstore)
        # Split undecided into two non-empty subsets
        if not undecided:
            print("SOMETHING WRONG; {} HAS NO UNDECIDED VALUES".format(variable))
        elem = Solver.ran_select(undecided)
        return {elem}, undecided - {elem}
        
    ## Two variable value selection functions.

    @staticmethod
    def ran_select(values):
        """Randomly select a value from a set of values."""
        return random.choice(list(values))

    @staticmethod
    def smallest_select(values):
        """Select smallest value."""
        value_list = list(values)
        value_list.sort()
        return value_list[0]

    def select_constraints(self, variable, dstore=None, verbosity=0):
        """Return a pair of constraints for the selected variable."""
        subset1, subset2 = self.split_var_values(variable, verbosity=verbosity)
        if isinstance(variable, IVar):
            if verbosity:
                print(' values: {}, {}'.format(subset1, subset2))
            return Member(variable, subset1, record=False), Member(variable, subset2, record=False)
        else:
            # For an set Var, add subset1 to the lower bound, subtract subset1
            # from the upper bound
            v1 = variable.get_lower(dstore=dstore) | subset1
            v2 = variable.get_upper(dstore=dstore) - subset1
            if verbosity:
                print(' values: {}, {}'.format(subset1, subset2))
            return Superset(variable, v1, record=False), Subset(variable, v2, record=False)

    def distribute(self, state=None, verbosity=0):
        """Creates and returns two new states by cloning the dstore with the distributor."""
#        if self.status != SearchState.distributable:
#            return []
        state = state or self.init_state
        undet = state.dstore.ess_undet
        if verbosity:
            ndet = len(undet)
            print('DISTRIBUTION')
            print('Distributing from state {}, undetermined vars {}'.format(state, ndet))
            for v in list(undet)[:5]:
                v.pprint(dstore=state.dstore)
            if ndet > 5:
                print('...')
        # Select a variable and two disjoint basic constraints on it
        var = self.select_variable(undet, dstore=state.dstore, verbosity=verbosity)
        constraint1, constraint2 = self.select_constraints(var, dstore=state.dstore,
                                                           verbosity=verbosity)
        if verbosity:
            print('Distribution constraints: a -- {}, b -- {}'.format(constraint1, constraint2))
        # The constraints of the selected variable (make copies)
        constraints = var.constraints[:]
        # Create the new solvers (states), applying one of the constraints to each
        new_dstore1 = state.dstore.clone(constraint1, name=self.name+'a')
        new_dstore2 = state.dstore.clone(constraint2, name=self.name+'b')
        # Create a new Solver for each dstore, preserving the accumulateod penalty
        state1 = SearchState(constraints=constraints, dstore=new_dstore1,
                             name=state.name+'a', depth=state.depth+1,
                             parent=state,
                             verbosity=verbosity)
        state2 = SearchState(constraints=constraints, dstore=new_dstore2,
                             name=state.name+'b', depth=state.depth+1,
                             parent=state,
                             verbosity=verbosity)
        state.children.extend([state, state2])
        return [((var, constraint2), state2), ((var, constraint1), state1)]

class SearchState:

    running = 0
    succeeded = 1
    failed = 2
    distributable = 3
    skipped = 4

    def __init__(self, solver=None, name='', dstore=None,
                 constraints=None, parent=None,
                 depth=0, verbosity=0):
        self.solver = solver                                  
        self.name = name
        self.dstore = dstore
        self.entailed = []
        self.failed = []
        self.constraints = constraints
        self.parent = parent
        self.children = []
        self.depth = depth
        self.status = SearchState.running
        self.verbosity = verbosity

    def __repr__(self):
        return "<SS {}/{}>".format(self.name, self.depth)

    def get_value(self):
        """A measure of how promising this state is: how many undetermined
        essential variables there are."""
        return len(self.dstore.ess_undet)

    def exit(self, result, verbosity=0):
        if result == Constraint.failed:
            return True
        else:
            return self.fixed_point(result, verbosity=verbosity)

    def fixed_point(self, awaken, verbosity=0):
        if verbosity:
            s = "# constraints to awaken: {}, # variables to determine: {}|{}"
            print(s.format(len(awaken), len(self.dstore.ess_undet), len(self.dstore.undetermined)))
        if self.dstore.is_determined():
            # All essential variables are determined
            self.status = SearchState.succeeded
            return True
        elif len(awaken) == 0:
            # More variables to determine; we have to distribute
            self.status = SearchState.distributable
            return True
        # Keep propagating
        return False

    def run(self, verbosity=0, tracevar=[]):
        """Run the constraints until CS fails or a fixed point is reached."""
        if verbosity:
            s = "Running {} with {}|{} undetermined variables, {} constraints"
            print(s.format(self, len(self.dstore.ess_undet), len(self.dstore.undetermined), len(self.constraints)))
        awaken = set(self.constraints)
        it = 0
        while not self.exit(awaken, verbosity=verbosity):
            if verbosity:
                print("Running iteration {}".format(it))
            awaken = self.run_constraints(awaken, verbosity=verbosity, tracevar=tracevar)
            it += 1

    def run_constraints(self, constraints, verbosity=0, tracevar=[]):
        awaken = set()
        all_changed = set()
        for constraint in constraints:
            state, changed_vars = constraint.run(dstore=self.dstore, verbosity=verbosity, tracevar=tracevar)
            all_changed.update(changed_vars)
            if state == Constraint.entailed:
                # Constraint is entailed; add it to the list of those.
                self.entailed.append(constraint)
                # Delete it from awaken if it's already there
                if constraint in awaken:
                    awaken.remove(constraint)

            if state == Constraint.failed:
                if verbosity:
                    print("FAILED {}".format(constraint))
                return Constraint.failed

            # Check whether any of the changed vars cannot possibly be determined; if so,
            # the constraint fails
            for var in changed_vars:
                try:
                    var.determined(dstore=self.dstore, verbosity=verbosity)
                except VarError:
                    if verbosity:
                        print("{} CAN'T BE DETERMINED, SO {} MUST FAIL".format(var, constraint))
                    return Constraint.failed

            for var in changed_vars:
                # Add constraints for changed var to awaken unless those constraints are already entailed
                # or failed
                update_cons = {c for c in var.constraints if c not in self.entailed and c not in self.failed}
                if var == tracevar and verbosity:
                    print('Adding {} constraints for changed variable {}'.format(len(update_cons), tracevar))
                awaken.update(update_cons)
        if verbosity > 1:
            print('# changed vars {}'.format(len(all_changed)))
        return awaken

