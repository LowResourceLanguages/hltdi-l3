#   Search algorithms based on code in the aima-python project,
#   implementing algorithms discussed in
#
#   Russell, S. and Norvig, P. (1995). Artificial Intelligence:
#   A modern approach (3rd Ed.). Prentice-Hall.
#   
#   http://aima-python.googlecode.com/svn/trunk/search.py
#   Copyright. Stuart Russell and Peter Norvig.
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
#   Michael Gasser <gasser@cs.indiana.edu>
#
# 2010.07.24
# -- Heuristic search doesn't work yet.
# 2011.02.06
# -- Added cutoff option to search algorithms, like in depth_limited_search,
#    which we're not using.
# 2011.03.01
# -- Made search algorithms classes with generators so we can output solutions
#    at will.
# 2011.04.25
# -- Add heuristic search (SmartSearch), which uses the number of undetermined
#    variables in a state's DStore to assign priority to states (nodes).

CUTOFF = 1000

import queue

class Problem:
    """The abstract class for a formal problem.  You should subclass this and
    implement the method successor, and possibly __init__, goal_test, and
    path_cost. Then you will create instances of your subclass and solve them
    with the various search functions."""

    def __init__(self, initial, goal=None):
        """The constructor specifies the initial state, and possibly a goal
        state, if there is a unique goal.  Your subclass's constructor can add
        other arguments."""
        self.initial = initial
        self.goal = goal
        self.report = 0
        
    def successor(self, state, verbosity=0):
        """Given a state, return a sequence of (action, state) pairs reachable
        from this state. If there are many successors, consider an iterator
        that yields the successors one at a time, rather than building them
        all at once. Iterators will work fine within the framework."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)
    
    def goal_test(self, state, verbosity=0, tracevar=None):
        """Return True if the state is a goal. The default method compares the
        state to self.goal, as specified in the constructor. Implement this
        method if checking against a single self.goal is not enough."""
        return state == self.goal
    
    def path_cost(self, c, state1, action, state2, verbosity=0):
        """Return the cost of a solution path that arrives at state2 from
        state1 via action, assuming cost c to get up to state1. If the problem
        is such that the path doesn't matter, this function will only look at
        state2.  If the path does matter, it will consider c and maybe state1
        and action. The default method costs 1 for every step in the path."""
        return c + 1

    def value(self, state):
        """For optimization problems, each state has a value.  Hill-climbing
        and related algorithms try to maximize this value."""
        raise NotImplementedError("%s is an abstract class" % self.__class__.__name__)
    
class Node:
    """A node in a search tree. Contains a pointer to the parent (the node
    that this is a successor of) and to the actual state for this node. Note
    that if a state is arrived at by two paths, then there are two nodes with
    the same state.  Also includes the action that got us to this state, and
    the total path_cost (also known as g) to reach the node.  Other functions
    may add an f and h value; see best_first_graph_search and astar_search for
    an explanation of how the f and h values are handled. You will not need to
    subclass this class."""

    def __init__(self, state, parent=None, action=None, path_cost=0):
        "Create a search tree Node, derived from a parent by an action."
        self.state = state
        self.parent = parent
        self.action = action
        self.path_cost = path_cost
        self.depth = 0
        if parent:
            self.depth = parent.depth + 1
            
    def __repr__(self):
        return "<Node {}>".format(self.state)

    ## Comparison methods needed so that smart search can work. Later fix these so
    ## they really compare.

    def __lt__(self, other):
        return True

    def __eq__(self, other):
        return True

    def path(self):
        """Create a list of nodes from the root to this node."""
        # Isn't this backwards???
        x, result = self, [self]
        while x.parent:
            result.append(x.parent)
            x = x.parent
        return result

    def expand(self, problem, verbosity=0, tracevar=None):
        """Return a list of nodes reachable from this node."""
        return [Node(next, self, act,
                     problem.path_cost(self.path_cost, self.state, act, next))
                for (act, next) in problem.successor(self.state, verbosity=verbosity)]

##______________________________________________________________________________
## Uninformed Search algorithms

class Search:

    def __init__(self, cutoff=CUTOFF):
        self.cutoff = cutoff

class TreeSearch(Search):

    def __init__(self, fringe_class, cutoff=CUTOFF):
        Search.__init__(self, cutoff=cutoff)
        self.fringe_class = fringe_class

    def gen(self, problem,
            test_verbosity=False, expand_verbosity=False,
            tracevar=None):
        '''A generator for solutions.'''
        fringe = self.fringe_class()
        fringe.put(Node(problem.initial))
        n = 0
        solutions = []
        while not fringe.empty() and n < self.cutoff:
            if test_verbosity or expand_verbosity:
                print("\n++++ Nodes searched:", n, '++++')
            node = fringe.get()
            if problem.goal_test(node.state,
                                 verbosity=test_verbosity, 
                                 tracevar=tracevar):
                yield node
            for item in node.expand(problem,
                                    verbosity=expand_verbosity, 
                                    tracevar=tracevar):
                fringe.put(item)
            n += 1

class BFS(TreeSearch):
    
    def __init__(self, cutoff=CUTOFF):
        TreeSearch.__init__(self, queue.Queue, cutoff=cutoff)

class DFS(TreeSearch):

    def __init__(self, cutoff=CUTOFF):
        TreeSearch.__init__(self, queue.LifoQueue, cutoff=cutoff)

class SmartSearch(Search):
    '''Sort the queue by # of determined variables in the DStores of the states.'''

    def __init__(self, cutoff=CUTOFF):
        Search.__init__(self, cutoff=cutoff)

    def gen(self, problem,
            test_verbosity=False, expand_verbosity=False,
            tracevar=None):
        '''A generator for solutions.'''
        fringe = queue.PriorityQueue()
        init_node = Node(problem.initial)
        fringe.put((problem.value(init_node.state), init_node))
        n = 0
        solutions = []
        while not fringe.empty() and n < self.cutoff:
            if (n+1) % 50 == 0 or test_verbosity or expand_verbosity:
                if test_verbosity or expand_verbosity:
                    print()
                print('>>>> SEARCH NODE {} <<<<'.format(n+1))
            if n >= self.cutoff:
                print('STOPPING AT CUTOFF')
            priority, node = fringe.get()
            if problem.goal_test(node.state,
                                 verbosity=test_verbosity, 
                                 tracevar=tracevar):
                yield node
            for item in node.expand(problem,
                                    verbosity=expand_verbosity, 
                                    tracevar=tracevar):
                val = problem.value(item.state)
#                print('Adding ({},{}) to fringe'.format(val, item))
                fringe.put((val, item))
            n += 1
        if test_verbosity or expand_verbosity:
            print()
        if problem.report:
            print('>>>> HALTED AT SEARCH NODE', n, '<<<<')
