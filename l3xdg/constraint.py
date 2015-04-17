#   Implementation of constraints, as described in
#
#   Müller, T. (2001). Constraint propagation in Mozart. PhD Dissertation,
#   Universität des Saarlandes.
#
#   and
#
#   Duchier, D. (2003). Configuration of labeled trees under lexicalized
#   constraints and principles. Research on Language and Computation, 1,
#   307-336.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010, 2011, 2012, 2013, 2014
#   the HLTDI L^3 Team <gasser@cs.indiana.edu>
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
# -- Primitive basic constraints and propagators work.
# 2010.07.25 (MG)
# -- Complex constraints introduced.
# 2010.08.07 (MG)
# -- Yikes; I'm way behind...
#    More complex constraints, including "Choice".
#    Various bugs in selection constraints fixed.
# -- Variables can now be traced via the constraints that change them.
# 2010.08.11 (MG)
# -- Implemented PrecedenceSelection, which uses sets of tuple variables
#    (neither of these in XDG of Mozart/Oz)
# -- Fixed fails() in CardinalitySubset
# 2010.08.12 (MG)
# -- Implemented IntSelection, replacing the derived constraint that is
#    used in Müller
# -- Fixed some problems in SetPrecedence
# 2010.08.13 (MG)
# -- Implemented SetConvexity (needed for projectivity principle)
# 2010.08.17 (MG)
# -- Implemented EqualitySelection (used in agreement principle);
#    not in Müller or Duchier as far as I know
# -- Fixed various bugs and gaps in IntSelection and UnionSelection
# 2010.09.04 (MG)
# -- Introduced names for constraints (also used in __repr__).
# -- Added Equality, a derived constraint equivalent to Inclusion([s1, s2]) and
#    Inclusion([s2, s1])
# 2010.10.31
# -- Added Complement (not tested yet).
# -- Added option in IntSelection to automatically determine undetermined
#    seqvars once the mainvar and selvar are determined. This allows "don't care"
#    for irrelevant variables such as agreement variables for lexical entries
#    that are not selected.
# -- PrecedenceSelection.infer() now has more ways to change seqvars; needed for
#    OrderP.
# 2010.11.11
# -- Fixed what appeared to be typos in UnionSelection (the following replacement):
#            if mainvar.strengthen_upper(set().union(*seq_uppers), dstore=dstore,
#    =>
#            if mainvar.strengthen_lower(set().union(*seq_lowers), dstore=dstore,
# 2010.11.12
# -- Selection constraints modified to allow for pattern option so they work with
#    unification, though this only changes UnionSelection and SimpleEqualitySelection
#    in a few places so far.
# 2010.12.12
# -- In UnionSelection, determine takes pattern option agreeing with value of
#    pattern attribute in the constraint. Used in GovernmentPrinciple.
# 2010.12.29
# -- Several changes to handle the case of variables whose values are "irrelevant".
#    See IntSelection.
# 2011.01.01
# -- Irrelevant variable problem solved in dimension.py. det_seq option elimintated
#    from UnionSelection.
# 2011.01.12
# -- It turns out infer() can sometimes make impossible changes to variables, something
#    that could first be checked in fails(). Caught the one case where this happened,
#    in UnionSelection, adding a test that causes infer() to return Constraint.failed
#    if the impossible action is attempted.
# 2011.02.06
# -- Added pattern option to IVMemberSV, affecting fails() and is_entailed(). It should
#    probably also affect infer().
# 2011.02.21
# -- Fixed a bug in IVMemberSV.is_entailed() that caused the constraint to be entailed
#    too early.
# 2011.02.25
# -- Some more tweaking of feature matching in constraints; probably still some problems.
# 2011.03.07
# -- Added new constraint class: SimplePrecedenceSelection
#    - to constrain empty and deleted nodes to appear in a single order
#    - variables:
#      sequence (position) variables: set variables specifying positions
#      selection variable: indices of sequence variables that must obey the constraint
#    - constraint: positions of selected variables constrained to be in the order in which they
#      appear in the sequence variable list
# 2011.03.15
# -- Selection now deletes any indices from the selection variable's upper
#    bound that are >= the length of the sequence variable list.
# 2011.03.25
# -- Fixed minor bugs in PrecedenceSelection constraints.
# 2011.03.26
# -- Added a further fail condition to UnionSelection, solving problems with the interaction
#    between this constraint and SetPrecedence in generating output positions for target
#    languages.
# 2011.03.30
# -- Added the pattern option to the new fail condition for UnionSelection
# 2011.04.08
# -- Added ReifiedMembership constraint, a propagator with two integer variables
#    I1 and I2, and a set variable S. It is satisfied if and only if the value
#    of I2 (0 or 1) agrees with the truth of the membership constraint I1 c S2.
#    Needed in one or more interface principles.
# 2011.04.09
# -- Added LogEquivalence, a propagator with two variables which is satisfied
#    if and only if the two variables are both "true" (non-0 for an IVar,
#    not empty for an SVar) or both "false" (0 for an IVar, set() for an SVar).
#    Needed in one or more interface principles.
# 2011.04.18
# -- Fail conditions for IntSelection extended to include what happens when
#    selection variable and selected sequence variable are both determined
#    and main variable cannot equal sequence variable. (How did this survive
#    so long??)
# 2011.05.20
# -- Fixed bug in fails() for UnionSelection with pattern=True.
# 2011.05.21
# -- Constraint.run() first tries to determine constraint variables, returning
#    those determined if any.
# 2011.09.26
# -- A start at implementing constraint propagation using projectors, as in Müller.
# 2011.11.12
# -- Projectors for about 6 constraint types.
# 2011.11.13-16
# -- Projectors for some selection constraints.
#    Constraints get assigned to projectors.
# 2011.11.20
# -- Projectors not created for determined variables.
# 2011.11.23
# -- Projectors for PrecedenceSelection (whew!).
# 2011.11.26
# -- More projectors for IVMemberSV
# -- Projectors for ReifiedMembership
# 2011.11.28
# -- Projectors for other reified and logical propagators
#    and other derived propagators
# -- New propagator, CardSelection, to handle lexical selection
#    of lower and upper cardinality for label variables; only
#    get_projectors() defined
# 2011.11.29
# -- Projectors for SimplePrecedenceSelection
# 2011.12.09
# -- Two fixes to CardinalitySubset (about to eliminated anyway);
#    how did the bugs last that long??
# 2011.12.22
# -- Patterns and unification eliminated.
# 2011.12.29
# -- Addition projector for each sequence variable for UnionSelection
#    (not mentioned in Duchier).
# -- Multiple trace variables.
# 2012.01.05
# -- Various fixes to get_projectors() for some constraints.
# 2012.01.10
# -- Fixed two problems with EqualitySelection projectors (mutual udates
#    to main (IVars) and seq (SVars)).
# 2012.01.15
# -- Added additional projector (LCardProj for main var) to UnionSelection
#    (not mentioned in Duchier).
# 2012.01.28
# -- Yet another update possibility added to UnionSelection (one already
#    incorporated into the associated projector); not mentioned in Duchier.
# 2012.01.31
# -- Another fix to projectors for SetConvexity.
#    Changes, including a new Constraint superclass, ExprGetter, to prevent
#    identical expressions (in projector right-hand sides) from being created
#    multiple times (resulting in a more than 50% saving in the number of expressions).
# 2012.02.15
# -- Additional propagators in SimplePrecSelection.
# 2012.07.27
# -- Fixed CardinalitySubset: now determines cardinality variable as soon as
#    sv1 is determined.
#    (Still need to eliminate this constraint.)
# 2012.09.16
# -- This last change now seems wrong. (Why did I change it anyway?) Changed
#    back. This shouldn't be serious since CardinalitySubset will go away once
#    constraint satisfaction is always by projectors.
# 2012.12.24
# -- Changed UnionSelection so the selection variable can contain values that
#    are beyond the length of the sequence variable list. (This can now happen
#    with the main constraint in BarriersPrinciple.) This involved changes in
#    Selection.infer(), UnionSelection.fails(), and UnionSelection.infer().
#    Note that the other selection constraints were not changed (they probably
#    should be).
# 2013.04.05
# -- EqualitySelection constructor takes an agr_maps argument so that
#    grammatical feature mappings can affect agreement between languages.
# 2013.04.19
# -- Two new propagators used in ArcAgreementP:
#    CardinalityEq fixed. (Partially implemented previously but not used.)
#    New variant on selection, IntIntSelection implemented. Sequence vars are
#    are determined int variables; both selection and main variables are int
#    variables.
# 2013.05.21
# -- Changes to EqualitySelection to accommodate reverse agr_maps.
# 2013.06.04
# -- Fixed a bug in Selection(!) that allowed UnionSelection to determine
#    main variable if all seq variables are equal and determined *and*
#    the selection variable can be empty.
# 2013.07.11
# -- Added principle parameter to propagators to help with debugging.
# 2013.11.03
# -- Projectors eliminated. It wasn't worth the trouble.

# from .projector import *
from .variable import *
import itertools

# from .lex import no_unify_fssets

##class ExprGetter:
##    """This class is just a place to keep methods for getting expressions."""
##
##    def constx(self, cls, element):
##        """Create a Constant Expression unless one already exists with this element."""
##        xD = self.problem.expressions[0]
##        elkey = element
##        if isinstance(element, set):
##            elkey = tuple(element)
##        x = self.findxD(elkey, xD)
##        if not x:
##            x = cls(element)
##            xD[elkey] = x
##        return x
##
##    def varx(self, cls, element):
##        """Create a Variable Expression unless one already exists with this element."""
##        xD = self.problem.expressions[1]
##        x = self.findxD(element, xD, tp=cls)
##        if not x:
##            x = cls(element)
##            xD[element] = x
##        x.var_right()
##        return x
##        
##    def compx(self, cls, *elements):
##        """Create a Complex Expression unless one already exists with these elements
##        (a tuple)."""
##        xD = self.problem.expressions[2]
##        if not isinstance(elements, tuple):
##            elements = tuple(elements)
##        x = self.findxD(elements, xD, tp=cls)
##        if not x:
##            x = cls(*elements)
##            xD[elements] = x
##        return x
##        
##    @staticmethod
##    def findxD(elements, dict, tp=None):
##        """Find elements (a tuple) in dict."""
##        x = dict.get(elements)
##        if x and (not tp or type(x) == tp):
##            return x

class Constraint:

    # Constants for outcome of running
    failed = 0
    entailed = 1
    sleeping = 2

    # Constant threshold for lenience
    lenience = .5

    def __init__(self, variables, problem=None,
                 principle=None, weight=1):
        self.variables = variables
        self.problem = problem
        self.weight = weight
#        self.projectors = []
        self.principle = principle
        self.name = ''

    def __repr__(self):
        return self.name

    ### Methods for creating projectors and expressions for projector right-hand sides.

##    def get_projectors(self, assign_to_var=True):
##        """The list of projectors associated with this constraint."""
###        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))
###        print("Warning: no projectors specified for", self)
##        return []

    def fails(self, dstore=None):
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def is_entailed(self, dstore=None):
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def is_lenient(self):
        return self.weight < Constraint.lenience

    def set_weight(self, weight):
        self.weight = weight

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """Should return state and variables that change."""
#        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def determine(self, dstore=None, verbosity=0, tracevar=None):
        """Try to determine each variable, returning the set if any determined."""
        det = set()
        for variable in self.variables:
            if not variable.is_determined(dstore=dstore) and \
                    variable.determined(dstore=dstore, constraint=self, verbosity=verbosity) is not False:
                if verbosity and variable in tracevar:
                    print('  {} determining {} at {}'.format(self, variable, variable.get_value(dstore=dstore)))
                det.add(variable)
        return det

    def run(self, dstore=None, verbosity=0, tracevar=None):
        if verbosity > 1:
            print(' Running {}'.format(self))
        determined = self.determine(dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        # Try to determine the variables
        if determined:
            if verbosity > 1:
                print('  Determined variables', determined)
            return Constraint.sleeping, determined
        # Otherwise see if the constraint fails
        if self.fails(dstore=dstore):
            if verbosity > 1:
                print('  Failed!')
            elif verbosity:
                print('{} failed; weight: {}'.format(self, self.weight))
            return Constraint.failed, set()
        # Otherwise see if the constraint is entailed
        if self.is_entailed(dstore=dstore):
            if verbosity > 1:
                print('  Entailed')
            return Constraint.entailed, set()
        # Otherwise try inferring variable values
        return self.infer(dstore=dstore, verbosity=verbosity, tracevar=tracevar)

    @staticmethod
    def string_set(s):
        if len(s) > 10:
            return '{{{0}...{1}}}'.format(min(s), max(s))
        else:
            return '{}'.format(set.__repr__(s))

    def print_vars(self):
        '''Print out components of constraint variables.'''
        for v in self.variables:
            print('{} :: {}'.format(v, v.dstores))

### Basic constraints

class BasicConstraint(Constraint):

    def get_var(self):
        """The single variable for this constraint."""
        return self.variables[0]

## Primitive basic constraints

# Integer domains

class Member(BasicConstraint):

    def __init__(self, var, domain, problem=None):
        """
        var: an IVar
        domain: a set of ints
        """
        Constraint.__init__(self, (var,), problem=problem)
        self.domain = domain
        self.name = '{0}<{1}'.format(self.get_var(), Constraint.string_set(self.domain))

##    def get_projectors(self, assign_to_var=True):
##        if not self.get_var().is_determined():
##            return [IntProj(self.get_var(), self.constx(ConstantIntX, self.domain),
##                            self)]
##        return [set()]

    def fails(self, dstore=None):
        """Is the constraint domain not a superset of the variable's domain?"""
        if not self.domain.issubset(self.get_var().get_domain(dstore=dstore)):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's domain a subset of the constraint's domain?"""
        if self.get_var().get_domain(dstore=dstore).issubset(self.domain):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's values are restricted to the intersection of
        their current values and the constraint's domain."""
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        var = self.get_var()
        if var.strengthen(self.domain, dstore=dstore, constraint=(verbosity>1 or var in tracevar) and self):
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

# Set domains

class Superset(BasicConstraint):
    """Set variable is constrained to be a superset of subset."""

    def __init__(self, var, subset, problem=None):
        """
        var:    a SVar
        subset: a set of ints
        """
        Constraint.__init__(self, (var,), problem=problem)
        self.subset = subset
        self.name = '{0} >= {1}'.format(self.get_var(), Constraint.string_set(self.subset))

##    def get_projectors(self, assign_to_var=True):
##        if not self.get_var().is_determined():
##            return [LowerProj(self.get_var(), self.constx(ConstantSetX, self.subset),
##                              self, assign_to_var=assign_to_var)]
##        return [set()]

    def fails(self, dstore=None):
        """Is the constraint subset not a subset of the var's upper bound?"""
        if not self.subset.issubset(self.get_var().get_upper(dstore=dstore)):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's lower bound a superset of the constraint's subset?"""
        if self.get_var().get_lower(dstore=dstore).issuperset(self.subset):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's values are restricted to be a superset of the union
        of the current lower bound and subset."""
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        var = self.get_var()
        if var.strengthen_lower(self.subset, dstore=dstore,
                                constraint=(verbosity>1 or var in tracevar) and self):
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

class Subset(BasicConstraint):
    """Set variable is constrained to be a subset of superset."""

    def __init__(self, var, superset, problem=None):
        """
        var:    a SVar
        superset: a set of ints
        """
        Constraint.__init__(self, (var,), problem=problem)
        self.superset = superset
        self.name = '{0} c= {1}'.format(self.get_var(), Constraint.string_set(self.superset))

##    def get_projectors(self, assign_to_var=True):
##        if not self.get_var().is_determined():
##            return [UpperProj(self.get_var(), self.constx(ConstantSetX, self.superset),
##                              self, assign_to_var=assign_to_var)]
##        return [set()]

    def fails(self, dstore=None):
        """Is the var's lower bound not a subset of the constraint superset?"""
        if not self.get_var().get_lower(dstore=dstore).issubset(self.superset):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's upper bound a subset of the constraint's superset?"""
        if self.get_var().get_upper(dstore=dstore).issubset(self.superset):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's values are restricted to be a subset of the intersection
        of the current upper bound and superset."""
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        var = self.get_var()
        if var.strengthen_upper(self.superset, dstore=dstore, constraint=(verbosity>1 or var in tracevar) and self):
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

# Set cardinality

class CardinalityGEQ(BasicConstraint):
    """Set variable's cardinality is constrained to be >= lower bound."""

    def __init__(self, var, lower, problem=None):
        Constraint.__init__(self, (var,), problem=problem)
        self.lower = lower
        self.name = '|{0}|>={1}'.format(self.get_var(), self.lower)

##    def get_projectors(self, assign_to_var=True):
##        if not self.get_var().is_determined():
##            return [LCardProj(self.get_var(), self.constx(ConstantIntX, self.lower),
##                              self)]
##        return [set()]

    def fails(self, dstore=None):
        """Is the var's upper cardinality bound < lower?"""
        if self.get_var().get_upper_card(dstore=dstore) < self.lower:
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's lower cardinality bound already >= lower?"""
        if self.get_var().get_lower_card(dstore=dstore) >= self.lower:
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's cardinality is restricted be >= lower: lower bound
        is raised if necessary."""
        Constraint.infer(self, verbosity=verbosity, tracevar=tracevar)
        var = self.get_var()
        if var.strengthen_lower_card(self.lower, dstore=dstore,
                                     constraint=(verbosity>1 or var in tracevar) and self):
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

class CardinalityLEQ(BasicConstraint):
    """Set variable's cardinality is constrained to be <= upper bound."""

    def __init__(self, var, upper, problem=None):
        Constraint.__init__(self, (var,), problem=problem)
        self.upper = upper
        self.name = '|{0}| c= {1}'.format(self.get_var(), self.upper)

##    def get_projectors(self, assign_to_var=True):
##        if not self.get_var().is_determined():
##            return [UCardProj(self.get_var(), self.constx(ConstantIntX, self.upper),
##                              self)]
##        return [set()]

    def fails(self, dstore=None):
        """Is the var's lower cardinality bound > upper?"""
        if self.get_var().get_lower_card(dstore=dstore) > self.upper:
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's upper cardinality bound already <= upper?"""
        if self.get_var().get_upper_card(dstore=dstore) <= self.upper:
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's cardinality is restricted to be <= upper:
        upper bound is lowered if necessary."""
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        var = self.get_var()
        if var.strengthen_upper_card(self.upper, dstore=dstore,
                                     constraint=(verbosity>1 or var in tracevar) and self):
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

### Propagators

class Propagator(Constraint):

    def __init__(self, variables, problem=None, propagate=True,
                 principle=None, weight=1):
        """Propagators can be 'used up' when there's nothing more to infer.
        If propagate is False, this propagator is only being used in the
        context of a real propagator, and its variables do not keep track
        of it."""
        Constraint.__init__(self, variables, problem=problem, principle=principle,
                            weight=weight)
        for var in variables:
#            if not var:
#                continue
            if propagate:
                if isinstance(var, Determined):
                    if problem:
                        props = problem.detvarsD.get(var, [])
                        props.append(self)
                        problem.detvarsD[var] = props
                else:
                    var.propagators.append(self)

## Primitive propagators

# Integer domain variables only

class LessThan(Propagator):
    """IVar1 is less than or equal to IVar2."""

    def __init__(self, variables, problem=None, principle=None, weight=1):
        Propagator.__init__(self, variables, problem=problem,
                            principle=principle, weight=weight)
        self.name = '{0} <= {1}'.format(self.get_iv1(), self.get_iv2())

##    def get_projectors(self, assign_to_var=True):
##        # Var 1's domain is the intersection of its current domain and
##        # all values from the minimum int and Var 2's domain's maximum
##        # Var 2's domain is the intersection of its current domain and
##        # all values from the minimum of Var 2's domain and the maximum int
##        proj = []
##        if not self.get_iv1().is_determined():
##            proj.append(IntProj(self.get_iv1(), 
##                                Min2MaxIntX(self.constx(ConstantIntX, MIN), SetMaxX(self.varx(DomainX, self.get_iv2()))),
##                                self))
##        if not self.get_iv2().is_determined():
##            proj.append(IntProj(self.get_iv2(),
##                                Min2MaxIntX(SetMinX(self.varx(DomainX, self.get_iv1())), self.constx(ConstantIntX, MAX)),
##                                self))
##        return proj

    def get_iv1(self):
        return self.variables[0]

    def get_iv2(self):
        return self.variables[1]

    def fails(self, dstore=None):
        """
        Fail if min of domain1 > max of domain2.
        """
        iv1 = self.get_iv1()
        iv2 = self.get_iv2()
        min1 = min(iv1.get_domain(dstore=dstore))
        max2 = max(iv2.get_domain(dstore=dstore))
        if min1 > max2:
            return True
        return False

    def is_entailed(self, dstore=None):
        """Entailed if max of domain1 <= min of domain2."""
        iv1 = self.get_iv1()
        iv2 = self.get_iv2()
        max1 = max(iv1.get_domain(dstore=dstore))
        min2 = min(iv2.get_domain(dstore=dstore))
        if max1 <= min2:
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        iv1 = self.get_iv1()
        iv2 = self.get_iv2()
        d1 = iv1.get_domain(dstore=dstore)
        d2 = iv2.get_domain(dstore=dstore)
        # iv2 must be between the min of iv1's domain and the maximum value
        iv2_values = set(range(min(d1), max(d2) + 1))
        if iv2.strengthen(iv2_values, dstore=dstore,
                          constraint=(verbosity>1 or iv2 in tracevar) and self):
                changed.add(iv2)
        # iv1 must be between the min of its domain and the max of iv2's domain
        # (iv2's domain may have changed)
        iv1_values = set(range(min(d1), max(iv2.get_domain(dstore=dstore)) + 1))
        # Maximum value of sv2's upper bound constrains sv1's upper card
        if iv1.strengthen(iv1_values, dstore=dstore,
                          constraint=(verbosity>1 or iv1 in tracevar) and self):
                changed.add(iv1)

        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return Constraint.sleeping, changed

class CardinalityEq(Propagator):
    """Set variable's cardinality is constrained to be equal to value of IVar."""

    def __init__(self, variables, problem=None, principle=None, weight=1):
        Propagator.__init__(self, variables, problem=problem,
                            principle=principle, weight=weight)
        self.sv = variables[0]
        self.iv = variables[1]
        self.name = '|{0}| = {1}'.format(self.sv, self.iv)

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        if not self.sv.is_determined():
##            # sv's upper cardinality is constrained by the maximum of iv's domain
##            # sv's lower cardinality is constrained by the minimum of iv's domain
##            proj.extend([UCardProj(self.sv,
##                                   SetMaxX(self.varx(DomainX, self.iv)),
##                                   self),
##                         LCardProj(self.sv,
##                                   SetMinX(self.varx(DomainX, self.iv)),
##                                   self)])
##        if not self.iv.is_determined():
##            # iv's domain is constrained by sv's lower cardinality
##            proj.extend([IntProj(self.iv,
##                                 Min2MaxIntX(self.constx(ConstantIntX, 0),
##                                             self.varx(UpperCardX, self.sv)),
##                                 self),
##                         IntProj(self.iv,
##                                 Min2MaxIntX(self.varx(LowerCardX, self.sv),
##                                             self.constx(ConstantIntX, self.sv.get_upper_card())),
##                                 self)])
##        return proj

    def fails(self, dstore=None):
        """Is the sv's lower cardinality bound > max of iv's domain?"""
        if self.iv.determined(dstore=dstore) is not False and self.sv.determined(dstore=dstore) is not False:
#            print('Both vars determined: {}, {}'.format(self.iv, self.sv))
            if self.iv.get_value(dstore=dstore) != self.sv.get_upper_card(dstore=dstore):
                return True
        if self.sv.get_lower_card(dstore=dstore) > max(self.iv.get_domain(dstore=dstore)):
            return True
        if min(self.iv.get_domain(dstore=dstore)) > self.sv.get_upper_card(dstore=dstore):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's upper cardinality bound already = iv?"""
        if self.iv.determined(dstore=dstore) is not False and self.sv.determined(dstore=dstore) is not False:
            if self.sv.get_upper_card(dstore=dstore) == self.iv.get_value(dstore=dstore):
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """sv's upper cardinality is restricted to be <= min of iv's domain.
        iv's domain is restricted to values >= lower cardinality of sv."""
        state = Constraint.sleeping
        changed = set()
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        sv = self.sv
        iv = self.iv
        sv_low_card = sv.get_lower_card(dstore=dstore)
        sv_up_card = sv.get_upper_card(dstore=dstore)
        if iv.strengthen(set(range(sv_low_card, sv.max)), dstore=dstore,
                         constraint=(verbosity>1 or iv in tracevar) and self):
            changed.add(iv)
            return state, changed
        if iv.strengthen(set(range(0, sv_up_card + 1)), dstore=dstore,
                         constraint=(verbosity>1 or iv in tracevar) and self):
            changed.add(iv)
            return state, changed
        iv_dom = iv.get_domain(dstore=dstore)
        if sv.strengthen_lower_card(min(iv_dom), dstore=dstore,
                                    constraint=(verbosity>1 or sv in tracevar) and self):
            changed.add(sv)
            return state, changed
        if sv.strengthen_upper_card(max(iv_dom), dstore=dstore,
                                    constraint=(verbosity>1 or sv in tracevar) and self):
            changed.add(sv)
            return state, changed

#        if sv.strengthen_upper_card(min(iv.get_domain(dstore=dstore)), dstore=dstore,
#                                    constraint=(verbosity>1 or sv in tracevar) and self):
#            changed.add(sv)
#        if iv.strengthen(sv.get_lower_card(dstore=dstore), dstore=dstore,
#                         constraint=(verbosity>1 or iv in tracevar) and self):
#            changed.add(iv)
        return state, changed

# Set domain variables only

class SetConvexity(Propagator):
    """There must not be any 'holes' in the (single) set variable, which represents
    the positions of the descendants of a node as well as that of the node itself."""

    def __init__(self, var, problem=None, principle=None, weight=1):
        """Only one variable, so a special constructor."""
        Propagator.__init__(self, [var], problem=problem,
                            principle=principle, weight=weight)
        self.var = self.variables[0]
        self.name = '{0} <>'.format(self.var)

##    ## Not in Müller (2001), based on Fig. 14 in Duchier (2003).
##    def get_projectors(self, assign_to_var=True):
##        if not self.var.is_determined():
##            return [LowerProj(self.var,
##                              self.varx(Min2MaxSetX, self.varx(LowerSetX, self.var)),
##                              self, recursive=True),
##                    UpperProj(self.var,
##                              ComplementSetX(LowestGapSetX(SetMaxX(self.varx(LowerSetX, self.var)),
##                                                           self.varx(UpperSetX, self.var))),
##                              self, recursive=True),
##                    UpperProj(self.var,
##                              ComplementSetX(LowestGapSetX(SetMaxX(self.varx(LowerSetX, self.var)),
##                                                           self.varx(UpperSetX, self.var),
##                                                           True)),
##                              self, recursive=True)]
##                    
###                            AppendSetX(SetMaxX(self.varx(LowerSetX, self.var)),
###self.compx(UnionSetX, self.varx(LowerSetX, self.var),
##        return [set()]

    def fails(self, dstore=None):
        """If the variable's upper does not include all values between
        min and max of lower bound, or if the determined value has gaps, fail."""
        if self.var.determined(dstore=dstore, constraint=self) is not False:
            val = self.var.get_value(dstore=dstore)
            # There can't be any holes
            if val:
                val_range = set(range(min(val), max(val)+1))
                if val_range - val:
                    return True
        lower = self.var.get_lower(dstore=dstore)
        if not lower:
            return False
        upper = self.var.get_upper(dstore=dstore)
        neces_range = set(range(min(lower), max(lower)+1))
        if neces_range - upper:
            # There is some value in necessary range not in upper bound
            return True
        return False

    def is_entailed(self, dstore=None):
        """If the variable is determined, or if the lower bound is convex,
        and the upper only adds a single vowel below or above the lower bound."""
        if self.var.determined(dstore=dstore, constraint=self) is not False:
            return True
        lower = self.var.get_lower(dstore=dstore)
        upper = self.var.get_upper(dstore=dstore)
        if not lower:
            return False
        min_lower = min(lower)
        max_lower = max(lower)
        if not set(range(min_lower, max_lower+1)) - lower:
            if min_lower - min(upper) <= 1 and max(upper) - max_lower <= 1:
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        # If the variable's lower bound is non-empty, every value between
        # the min and max of the lower bound must be in the variable, and
        # there can't be any gaps in the upper bound either.
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        v = self.var
        lower = v.get_lower(dstore=dstore)
        if len(lower) > 0:
            upper = v.get_upper(dstore=dstore)
            min_low = min(lower)
            max_low = max(lower)
            # Make the lower bound everything between the min and max
            if v.strengthen_lower(set(range(min_low, max_low+1)),
                                  dstore=dstore, constraint=(verbosity>1 or v in tracevar) and self):
                changed.add(v)
                return Constraint.sleeping, changed

            # Look for gaps in the upper bound
            # Starting at the max of the lower bound...
            max_up = max(upper)
            x = max_low+1
            while x in upper and x < max_up:
                x += 1
            if x < max_up:
                if v.discard_upper(set(range(x, max_up+1)),
                                   dstore=dstore, constraint=(verbosity>1 or v in tracevar) and self):
                    changed.add(v)
                    return Constraint.sleeping, changed
            # Starting at the min of the lower bound...
            min_up = min(upper)
            x = min_low-1
            while x in upper and x > min_up:
                x -= 1
            if x > min_up + 1:
                if v.discard_upper(set(range(min_up, x)),
                                   dstore=dstore, constraint=(verbosity>1 or v in tracevar) and self):
                    changed.add(v)
                    return Constraint.sleeping, changed
                
        return Constraint.sleeping, changed

class SupersetIntersection(Propagator):
    """Set var S1 is superset of intersection of set vars S2 and S3."""

    def __init__(self, variables, problem=None, principle=None, weight=1):
        Propagator.__init__(self, variables, problem=problem,
                            principle=principle, weight=weight)
        self.name = '{0} >= {1} ^ {2}'.format(self.variables[0], self.variables[1], self.variables[2])

##    ## Müller (12.1-6)
##    def get_projectors(self, assign_to_var=True):
##        v0 = self.variables[0]
##        v1 = self.variables[1]
##        v2 = self.variables[2]
##        if (v0 == EMPTY and v1 == EMPTY) or (v0 == EMPTY and v2 == EMPTY):
##            return []
##        proj = []
##        if not v0.is_determined():
##            proj.extend([LowerProj(v0,
##                                   self.compx(IntersectionSetX, self.varx(LowerSetX, v1), self.varx(LowerSetX, v2)),
##                                   self),
##                         LCardProj(v0,
##                                   DiffIntX(SumIntX(self.varx(LowerCardX, v1), self.varx(LowerCardX, v2)),
##                                            self.constx(ConstantIntX, MAX)),
##                                   self)])
##        if not v1.is_determined():
##            proj.extend([UpperProj(v1,
##                                   ComplementSetX(DiffSetX(self.varx(LowerSetX, v2), self.varx(UpperSetX, v0))),
##                                   self),
##                         UCardProj(v1,
##                                   SumIntX(self.constx(ConstantIntX, MAX),
##                                           DiffIntX(self.varx(UpperCardX, v0), self.varx(LowerCardX, v2))),
##                                  self)])
##        if not v2.is_determined():
##            proj.extend([UpperProj(v2,
##                                   ComplementSetX(DiffSetX(self.varx(LowerSetX, v1), self.varx(UpperSetX, v0))),
##                                   self),
##                         UCardProj(v2,
##                                   SumIntX(self.constx(ConstantIntX, MAX),
##                                           DiffIntX(self.varx(UpperCardX, v0), self.varx(LowerCardX, v1))),
##                                   self)])
##        return proj

    def fails(self, dstore=None):
        """Is the intersection of the lower bounds of S2 and S3 not a subset of
        the upper bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        s2_inters_s3 = s2.get_lower(dstore=dstore) & s3.get_lower(dstore=dstore)
        if not s2_inters_s3 <= s1.get_upper(dstore=dstore):
            return True
        # Fail on cardinalities
        if s1.get_upper_card(dstore=dstore) < len(s2_inters_s3):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the intersection of the upper bounds of S2 and S3 already a subset of
        the lower bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s2.get_upper(dstore=dstore) & s3.get_upper(dstore=dstore) <= s1.get_lower(dstore=dstore):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        # Intersection of lower bound of S2 and S3 is subset of lower bound of S1.
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s1.strengthen_lower(s2.get_lower(dstore=dstore) & s3.get_lower(dstore=dstore),
                               dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        # Upper bound of S2 and S3 excludes elements which are in the lower bounds of S3 and S2, respectively,
        # but not in the upper bound of S1.
        s1_up = s1.get_upper(dstore=dstore)
        s2_not_s1 = s2.get_lower(dstore=dstore) - s1_up
        s3_not_s1 = s3.get_lower(dstore=dstore) - s1_up
        for x in s3.get_upper(dstore=dstore).copy():
            if x in s2_not_s1:
                if s3.discard_upper(x, dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
                    changed.add(s3)
        for x in s2.get_upper(dstore=dstore).copy():
            if x in s3_not_s1:
                if s2.discard_upper(x, dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
                    changed.add(s2)
        # Inference based on cardinalities (from Müller, p. 104)
        s2Us3_card = len(s2.get_upper(dstore=dstore) | s3.get_upper(dstore=dstore))
        s1_up_card = s1.get_upper_card(dstore=dstore)
        s2_low_card = s2.get_lower_card(dstore=dstore)
        s3_low_card = s3.get_lower_card(dstore=dstore)
        if s1.strengthen_lower_card(s2_low_card + s3_low_card - s2Us3_card,
                                    dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        if s2.strengthen_upper_card(s2Us3_card + s1_up_card - s3_low_card,
                                    dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
            changed.add(s2)
        if s3.strengthen_upper_card(s2Us3_card + s1_up_card - s2_low_card,
                                    dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
            changed.add(s3)
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return Constraint.sleeping, changed

class SubsetUnion(Propagator):
    """Set var S1 is subset of union of set vars S2 and S3."""

    def __init__(self, variables, problem=None, propagate=True,
                 principle=None, weight=1):
        Propagator.__init__(self, variables, problem=problem, propagate=propagate,
                            principle=principle, weight=weight)
        self.name = '{0} c= {1} U {2}'.format(self.variables[0], self.variables[1], self.variables[2])

##    ## Müller (12.7-12)
##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        if not self.variables[0].is_determined():
##            proj.extend([UpperProj(self.variables[0],
##                                   self.compx(UnionSetX,
##                                              self.varx(UpperSetX, self.variables[1]),                                  
##                                              self.varx(UpperSetX, self.variables[2])),
##                                   self),
##                         UCardProj(self.variables[0],
##                                   SumIntX(self.varx(UpperCardX, self.variables[1]),
##                                           self.varx(UpperCardX, self.variables[2])),
##                                   self)])
##        if not self.variables[1].is_determined():
##            proj.extend([LowerProj(self.variables[1],
##                                   DiffSetX(self.varx(LowerSetX, self.variables[0]),
##                                            self.varx(UpperSetX, self.variables[2])),
##                                   self),
##                         LCardProj(self.variables[1],
##                                   DiffIntX(self.varx(LowerCardX, self.variables[0]),
##                                            self.varx(UpperCardX, self.variables[2])),
##                                   self)])
##        if not self.variables[2].is_determined():
##            proj.extend([LowerProj(self.variables[2],
##                                   DiffSetX(self.varx(LowerSetX, self.variables[0]),
##                                            self.varx(UpperSetX, self.variables[1])),
##                                   self),
##                         LCardProj(self.variables[2],
##                                   DiffIntX(self.varx(LowerCardX, self.variables[0]),
##                                            self.varx(UpperCardX, self.variables[1])),
##                                   self)])
##        return proj

    def fails(self, dstore=None):
        """Is the union of the upper bounds of S2 and S3 (the biggest it can be)
        not a superset of the lower bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        s2_union_s3 = s2.get_upper(dstore=dstore) | s3.get_upper(dstore=dstore)
        if not s2_union_s3 >= s1.get_lower(dstore=dstore):
            return True
        # Fail on cardinalities
        if s1.get_lower_card(dstore=dstore) > len(s2_union_s3):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the union of the lower bounds of S2 and S3 already a superset of
        the upper bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s2.get_lower(dstore=dstore) | s3.get_lower(dstore=dstore) >= s1.get_upper(dstore=dstore):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        # S1 must be a subset of the union of the upper bounds of S2 and S3
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s1.strengthen_upper(s2.get_upper(dstore=dstore) | s3.get_upper(dstore=dstore),
                               dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        # S2's and S3's lower bounds must contain elements that are in the lower bound of S1 but not
        # S3 and S2, respectively (note: Müller has *lower* bounds of S3 and S2 (Eq. 11.17, p. 105),
        # but this seems too strong).
        s1_not_s2 = s1.get_lower(dstore=dstore) - s2.get_upper(dstore=dstore)
        s1_not_s3 = s1.get_lower(dstore=dstore) - s3.get_upper(dstore=dstore)
        if s3.strengthen_lower(s1_not_s2, dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
            changed.add(s3)
        if s2.strengthen_lower(s1_not_s3, dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
            changed.add(s2)
        # Inference based on cardinalities (from Müller, p. 105, but there's apparently
        # a typo; in Eq. 11.19, n1 should be the upper, not the lower bound of S1)
        if s1.strengthen_upper_card(s2.get_upper_card(dstore=dstore) + s3.get_upper_card(dstore=dstore),
                                    dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        if s2.strengthen_lower_card(s1.get_lower_card(dstore=dstore) - s3.get_lower_card(dstore=dstore),
                                    dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
            changed.add(s2)
        if s3.strengthen_lower_card(s1.get_lower_card(dstore=dstore) - s2.get_lower_card(dstore=dstore),
                                    dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
            changed.add(s3)
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return Constraint.sleeping, changed

class CardinalitySubset(Propagator):
    """Cardinality of set variable 1 is within set variable 2. This constraint is not included
    in Müller, but it is needed for XDG valency with propagators (but not projectors).
    It could be handled with IVMemberSV."""

    def __init__(self, variables, problem=None, principle=None, weight=1):
        Propagator.__init__(self, variables, problem=problem,
                            principle=principle, weight=weight)
        self.name = '|{0}| c= {1}'.format(self.get_sv1(), self.get_sv2())

##    def get_projectors(self, assign_to_var=True):
##        return []

#    def run(self, dstore=None, verbosity=1, tracevar=None):
#        return Constraint.run(self, dstore=dstore, tracevar=tracevar, verbosity=2)

    def get_sv1(self):
        return self.variables[0]

    def get_sv2(self):
        return self.variables[1]

    def fails(self, dstore=None):
        """Fail if minimum cardinality of SV1 is greater than maximum possible value of SV2
        or if maximum cardinality of SV1 is less than the minimum possible value of SV2.
        Fixed 2011.12.09: minimum possible value of SV2 is minimum of *upper* bound, not
        lower bound."""
        sv1 = self.get_sv1()
        sv2 = self.get_sv2()
        upper2 = sv2.get_upper(dstore=dstore)
        max2card = max(upper2) if upper2 else 0
        if sv1.get_lower_card(dstore=dstore) > max2card:
            return True
#        lower2 = sv2.get_lower(dstore=dstore)
        min2card = min(upper2) if upper2 else 0
        # min(lower2) if lower2 else 0
        if sv1.get_upper_card(dstore=dstore) < min2card:
            return True
        return False

    def is_entailed(self, dstore=None):
        """Entailed if cardinality of SV1 determined, SV2 determined, and the former is in the latter."""
        sv1 = self.get_sv1()
        sv2 = self.get_sv2()
        if sv2.determined(dstore=dstore, constraint=self) is not False and \
           sv1.get_lower_card(dstore=dstore) == sv1.get_upper_card(dstore=dstore) in sv2.get_value(dstore=dstore):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        state = Constraint.sleeping
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        sv1 = self.get_sv1()
        sv2 = self.get_sv2()
        sv1_low_card = sv1.get_lower_card(dstore=dstore)
        sv1_up_card = sv1.get_upper_card(dstore=dstore)
#        if tracevar in self.variables:
#            print(self, 'INFERRING')
        # If sv1's cardinality is determined, then it must be in sv2
        if sv1_low_card == sv1_up_card:
#            print('SV1 {} has same upper and lower card {}'.format(sv1, sv1_low_card))
            if sv2.strengthen_lower({sv1_low_card}, dstore=dstore,
                                    constraint=(verbosity>1 or sv2 in tracevar) and self):
#                                    constraint=self):
#            if sv2.determine({sv1_low_card}, dstore=dstore,
#                             constraint=(verbosity>1 or sv2 in tracevar) and self):
                changed.add(sv2)
                return state, changed

#        if tracevar in self.variables:
#            print(self, 'GOT TO 0')

        sv2_upper = sv2.get_upper(dstore=dstore)
#        sv2_lower = sv2.get_lower(dstore=dstore)

        # Minimum value of sv2 constrains sv1's lower card
        # Fixed 2011.12.09: minimum value of sv2 is min of *upper* bound, not lower
        if sv2_upper:
            # Could be empty set, in which case no strengthening is possible
            if sv1.strengthen_lower_card(min(sv2_upper), dstore=dstore,
                                         constraint=(verbosity>1 or sv1 in tracevar) and self):
                changed.add(sv1)
                return state, changed

#        if tracevar in self.variables:
#            print(self, 'GOT TO 1')
        # Maximum value of sv2's upper bound constrains sv1's upper card
        upcard = max(sv2_upper) if sv2_upper else 0
        if sv1.strengthen_upper_card(upcard, dstore=dstore, constraint=(verbosity>1 or sv1 in tracevar) and self):
            changed.add(sv1)
            return state, changed
#        if tracevar in self.variables:
#            print(self, 'GOT TO 2')

        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return state, changed

class SetPrecedence(Propagator):
    """All elements of set variable 1 must precede all elements of set variable 2."""

    def __init__(self, variables, problem=None, principle=None, weight=1):
        Propagator.__init__(self, variables, problem=problem,
                            principle=principle, weight=weight)
        self.name = '{0} << {1}'.format(self.variables[0], self.variables[1])

##    def get_projectors(self, assign_to_var=True):
##        # Var 1's upper bound must exclude all elements greater than the maximum of Var 2's lower bound
##        # Var 2's upper bound must exclude all elements less than than the minimum of Var 1's lower bound
##        proj = []
##        if not self.variables[0].is_determined():
##            proj.append(UpperProj(self.variables[0],
##                                  ComplementSetX(Min2MaxIntX(SetMaxX(self.varx(UpperSetX, self.variables[1])),
##                                                             self.constx(ConstantIntX, MAX))),
##                                  self))
##        if not self.variables[1].is_determined():
##            proj.append(UpperProj(self.variables[1],
##                                  ComplementSetX(Min2MaxIntX(self.constx(ConstantIntX, MIN),
##                                                             SetMinX(self.varx(UpperSetX, self.variables[2])))),
##                                  self))
##        return proj

    # Also used in PrecedenceSelection

    @staticmethod
    def must_precede(svar1, svar2, dstore=None):
        """Is the highest value that can occur in svar1 < the lowest value that can occur in svar2?"""
        v1_upper = svar1.get_upper(dstore=dstore)
        v2_upper = svar2.get_upper(dstore=dstore)
        return v1_upper and v2_upper and (max(v1_upper) < min(v2_upper))

    @staticmethod
    def cant_precede(svar1, svar2, dstore=None):
        """Is the highest value that must occur in svar1 >= the lowest value that must occur in svar2?"""
        v1_lower = svar1.get_lower(dstore=dstore)
        v2_lower = svar2.get_lower(dstore=dstore)
        return v1_lower and v2_lower and (max(v1_lower) >= min(v2_lower))

    def fails(self, dstore=None):
        """Fail if any of set1's lower bound > any of set2's lower bound."""
        return SetPrecedence.cant_precede(self.variables[0], self.variables[1], dstore=dstore)

    def is_entailed(self, dstore=None):
        """Entailed if everything that can be in set1 precedes anything that can be in set2."""
        return SetPrecedence.must_precede(self.variables[0], self.variables[1], dstore=dstore)

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        Constraint.infer(self, verbosity=verbosity, tracevar=tracevar)
        v1 = self.variables[0]
        v1_low = v1.get_lower(dstore=dstore)
        v2 = self.variables[1]
        v2_low = v2.get_lower(dstore=dstore)
        # If the lower bound on v1 is not empty, v2 must be a subset of
        # {min(MAX, max(v1 + 1)), ..., MAX}
        if v1_low:
            v2_up_new = range(min([v1.max, max(v1_low) + 1]), v2.max+1)
            if v2.strengthen_upper(v2_up_new, dstore=dstore,
                                   constraint=(verbosity>1 or v2 in tracevar) and self):
                changed.add(v2)
        # If the lower bound on v2 is not empty, v1 must be a subset of
        # {0, ..., max(0, min(v2_low) - 1)}
        if v2_low:
            v1_up_new = range(0, max([0, min(v2_low) - 1]) + 1)
            if v1.strengthen_upper(v1_up_new, dstore=dstore,
                                   constraint=(verbosity>1 or v1 in tracevar) and self):
                changed.add(v1)

##class ListSetPrecedence(Propagator):
##    """Values of succeeding set variables in list must be in order.
##    New propagator; introduced 2013.06.03."""
##
##    def __init__(self, variables, problem=None, weight=1):
##        Propagator.__init__(self, variables, problem=problem, weight=weight)
##        self.name = '<< {}'.format(self.variables)
##
##    def get_projectors(self, assign_to_var=True):
##        # Var 1's upper bound must exclude all elements greater than the maximum of Var 2's lower bound
##        # Var 2's upper bound must exclude all elements less than than the minimum of Var 1's lower bound
##        proj = []
##        for index, var1 in enumerate(self.variables[:-1]):
##            # For each succeeding pair of variables
##            var2 = self.variables[index+1]
##            if not var1.is_determined():
##                proj.append(UpperProj(var1,
##                                      ComplementSetX(Min2MaxIntX(SetMaxX(self.varx(UpperSetX, var2)),
##                                                                 self.constx(ConstantIntX, MAX))),
##                                      self))
##            if not var2.is_determined():
##                proj.append(UpperProj(var1,
##                                      ComplementSetX(Min2MaxIntX(self.constx(ConstantIntX, MIN),
##                                                                 SetMinX(self.varx(UpperSetX, var2)))),
##                                      self))
##            return proj
##
##    def fails(self, dstore=None):
##        """For each succeeding pair of variables, fail if any of set1's lower bound > any of set2's lower bound."""
##        for index, var1 in enumerate(self.variables[:1]):
##            var2 = self.variables[index+1]
##            if SetPrecedence.cant_precede(var1, var2, dstore=dstore):
##                return True
##        return False
##
##    def is_entailed(self, dstore=None):
##        """Entailed if, for all pairs, everything that can be in set1 precedes anything that can be in set2."""
##        for index, var1 in enumerate(self.variables[:1]):
##            var2 = self.variables[index+1]
##            if not SetPrecedence.must_precede(var1, var2, dstore=dstore):
##                # For some pair of variables, the order is not entailed
##                return False
##        return True
##
##    def infer(self, dstore=None, verbosity=0, tracevar=None):
##        changed = set()
##        Constraint.infer(self, verbosity=verbosity, tracevar=tracevar)
##        for index, v1 in enumerate(self.variables[:1]):
##            v2 = self.variables[index+1]
##            v1_low = v1.get_lower(dstore=dstore)
##            v2_low = v2.get_lower(dstore=dstore)
##            # If the lower bound on v1 is not empty, v2 must be a subset of
##            # {min(MAX, max(v1 + 1)), ..., MAX}
##            if v1_low:
##                v2_up_new = range(min([v1.max, max(v1_low) + 1]), v2.max+1)
##                if v2.strengthen_upper(v2_up_new, dstore=dstore,
##                                       constraint=(verbosity>1 or v2 in tracevar) and self):
##                    changed.add(v2)
##            # If the lower bound on v2 is not empty, v1 must be a subset of
##            # {0, ..., max(0, min(v2_low) - 1)}
##            if v2_low:
##                v1_up_new = range(0, max([0, min(v2_low) - 1]) + 1)
##                if v1.strengthen_upper(v1_up_new, dstore=dstore,
##                                       constraint=(verbosity>1 or v1 in tracevar) and self):
##                    changed.add(v1)

# Integer domain and set domain variables

class IVMemberSV(Propagator):
    """Integer variable value must be member of set variable value."""

    def __init__(self, variables, problem=None, pattern=False, propagate=True,
                 principle=None, weight=1):
        """pattern option is required when variables are agreement features."""
        Propagator.__init__(self, variables, problem=problem, propagate=propagate,
                            principle=principle, weight=weight)
        self.pattern = pattern
        self.name = '{0} c {1}'.format(self.get_iv(), self.get_sv())

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        if not self.get_iv().is_determined():
##            proj.append(IntProj(self.get_iv(), self.varx(UpperSetX, self.get_sv()), self))
##        if not self.get_sv().is_determined():
##            # if the intersection of the domain of I and the lower bound of S is
##            # empty, then the lower card of S should be >= 1 greater than
##            # the length of the lower bound of S
##            #
##            # if I is determined (the length of its domain - 2 is negative),
##            # then update the lower bound of S to include I's value
##            proj.extend([LCardProj(self.get_sv(),
##                                   CondX(self.compx(IntersectionSetX, self.varx(DomainX, self.get_iv()),
##                                                     self.varx(LowerSetX, self.get_sv())),
##                                         SumIntX(self.varx(SetCardX, self.varx(LowerSetX, self.get_sv())),
##                                                 self.constx(ConstantIntX, 1)),
##                                         False),
##                                   self, recursive=True),
##                         LowerProj(self.get_sv(),
##                                   EqCondX(self.varx(SetCardX, self.varx(DomainX, self.get_iv())),
##                                           self.constx(ConstantIntX, 1),
##                                           self.varx(DomainX, self.get_iv())),
##                                   self)])
##        return proj

    def get_iv(self):
        """The domain variable."""
        return self.variables[0]

    def get_sv(self):
        """The set variable."""
        return self.variables[1]

    def fails(self, dstore=None):
        """Fail if none of the IV values are in SV upper bound."""
        iv = self.get_iv()
        sv = self.get_sv()
        iv_dom = iv.get_domain(dstore=dstore)
        sv_up = sv.get_upper(dstore=dstore)
        if self.pattern:
            # For patterns, fail if the domain of iv fails to unify with the upper bound of sv
            if not unify_fssets(iv_dom, sv_up):
                return True
        elif len(iv_dom & sv_up) == 0:
            return True
        return False

    def is_entailed(self, dstore=None):
        """Entailed if IV values are subset of SV lower bound, or, if pattern is True,
        if IV values unify with SV lower bound."""
        iv = self.get_iv()
        sv = self.get_sv()
        iv_dom = iv.get_domain(dstore=dstore)
        sv_low = sv.get_lower(dstore=dstore)
        if self.pattern:
            # For patterns, the propagator is entailed if every element in the domain of iv
            # unifies with the lower bound of sv
            if all([unify_fssets({tup}, sv_low) for tup in iv_dom]):
#            if unify_fssets(iv_dom, sv_low):
                return True
        elif iv_dom <= sv_low:
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        iv = self.get_iv()
        sv = self.get_sv()
        # Constrain the values of IV to be within upper bound of SV
        if iv.strengthen(sv.get_upper(dstore=dstore), dstore=dstore,
                         constraint=(verbosity>1 or iv in tracevar) and self):
            changed.add(iv)
        # If IV is determined, constrain SV to include it
        if iv.determined(dstore=dstore, verbosity=verbosity) is not False:
            if sv.strengthen_lower(iv.get_domain(dstore=dstore), dstore=dstore,
                                   constraint=(verbosity>1 or sv in tracevar) and self):
                changed.add(sv)
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return Constraint.sleeping, changed

# Selection constraint propagators

class Selection(Propagator):
    """Superclass for most selection constraints.

    mainvar: set domain var or int domain var (set var for primitive propagators)
    seqvars: set domain vars, int domain vars, constant sets, or constant ints
             (set var for primitive propagators)
    selvar: set domain var or int domain var (set var for primitive propagators)
    """

    def __init__(self, mainvar=None, selvar=None, seqvars=None, pattern=False, 
                 problem=None, principle=None, weight=1):
        Propagator.__init__(self, [mainvar, selvar] + seqvars, problem=problem,
                            principle=principle, weight=weight)
        self.selvar = selvar
        self.mainvar = mainvar
        self.seqvars = seqvars
        self.pattern = pattern

    def is_entailed(self, dstore=None):
        """Entailed only if all vars are determined.
        """
        if self.mainvar.determined(dstore=dstore, constraint=self) is not False \
           and self.selvar.determined(dstore=dstore, constraint=self) is not False \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.seqvars]):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """Some rules are common to all Selection subclasses."""

        changed = set()
        state = Constraint.sleeping
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar

        # If there is only one seqvar, then the main var is constrained to be that value
        # and the selection var has to be {0} or 0
        if len(seqvars) == 1:
            # since there's only one seq var to select, the selection variable has to
            # be {0} or 0
            if selvar.determine(0, dstore=dstore,
                                constraint=(verbosity>1 or selvar in tracevar) and self):
                changed.add(selvar)
            seqvar = seqvars[0]
            if seqvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                if mainvar.determine(seqvar.get_value(dstore=dstore), dstore=dstore,
                                     constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                state = Constraint.entailed
            else:
                if mainvar.strengthen_lower(seqvar.get_lower(dstore=dstore), dstore=dstore,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                if mainvar.strengthen_upper(seqvar.get_upper(dstore=dstore), dstore=dstore,
                                            pattern=self.pattern, 
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
##                if mainvar.determined(dstore=dstore, verbosity=verbosity) is not False:
##                    state = Constraint.entailed
            if changed:
                if verbosity > 1:
                    print('  Variables {} changed'.format(changed))
                return state, changed
        # If all of the seqvars are equal to one another and determined and the selection variable must
        # be non-empty, then the main var can be determined (as long as the seqvar value is in its domain)
        if all([v.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False for v in seqvars]) and \
             selvar.get_lower_card(dstore=dstore) > 0 and seqvars[0].all_equal(seqvars[1:], dstore=dstore):
            seq0_val = seqvars[0].get_value(dstore=dstore)
            if mainvar.determine(seq0_val, dstore=dstore, constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return state, changed
        # If the upper bound of selvar includes values that are greater than the length of selvars,
        # then those values can be eliminated from the upper bound.
#        selupper = selvar.get_upper(dstore=dstore)
#        n_seqvars = len(seqvars)
#        to_remove = {index for index in selupper if index >= n_seqvars}
#        if to_remove:
#            if selvar.discard_upper(to_remove, dstore=dstore, constraint=(verbosity>1 or mainvar in tracevar) and self):
#                changed.add(selvar)
#            if changed:
#                if verbosity > 1:
#                    print('  Variables {} changed'.format(changed))
#                return state, changed

        return False

    @staticmethod
    def format_seq(seq):
        string = '< '
        for i, elem in enumerate(seq):
            if i != 0:
                string += ', '
            if elem == set():
                string += '{}'
            else:
                string += elem.__repr__()
        return string + ' >'

    @staticmethod
    def format_list(seq):
        string = '['
        for i, elem in enumerate(seq):
            if i != 0:
                string += ', '
            if elem == set():
                string += '{}'
            else:
                string += elem.__repr__()
        return string + ']'

class IntSelection(Selection):
    """Selection constraint with integer variable as selection variable.
    Müller treats this as derived from UnionSelection, but it is more efficient
    to treat it as a primitive, at least in this program.
    """

    def __init__(self, mainvar=None, selvar=None, seqvars=None, problem=None, weight=1,
                 maxset=None):
        Selection.__init__(self, mainvar=mainvar, selvar=selvar, seqvars=seqvars,
                           problem=problem, weight=weight)
        self.maxset = maxset or ALL
        self.name = '{0} = {1} [{2}]'.format(self.mainvar, self.format_seq(self.seqvars), self.selvar)

##    def get_projectors(self, assign_to_var=True):
##        if not self.mainvar:
##            return []
##        proj = []
##        # seqvars could be IVars or SVars
##        seqs = self.seqvars
##        iseq = not self.seqvars or isinstance(seqs[0], IVar)
##        upseqs = tuple([self.varx(UpperSetX, s) for s in seqs])
##        conds2 = [self.compx(UnionSelectX, self.varx(DomainX, self.selvar), upseqs, k) for k, s in enumerate(seqs)]
##        conds2 = [DiffSetX(self.varx(LowerSetX, self.mainvar), c) for c in conds2]
##        if not self.selvar.is_determined():
##            # Apparently the sel IVar is already constrained to the set of seq indices
###            proj.append(IntProj(self.selvar, self.constx(ConstantSetX, set(range(len(seqs)))), self))
##            # If lower bound of seq var j /<= upper bound of main var, that is,
##            # if some element that must be in seq var j can't be in main var,
##            # then j is not in sel var
##            seqlow_mainup = [DiffSetX(self.varx(LowerSetX, s),
##                                      self.compx(IntersectionSetX, 
##                                                 self.varx(LowerSetX, s),
##                                                 self.varx(UpperSetX, self.mainvar))) \
##                                 for s in seqs]
##            seqlow_mainup_cond = [CondX(c, DiffSetX(self.constx(ConstantSetX, ALL),
##                                                    self.constx(ConstantSetX, {j}))) for j, c in enumerate(seqlow_mainup)]
##            proj.extend([IntProj(self.selvar, e, self, recursive=True) for e in seqlow_mainup_cond])
##            # If lower bound of main var />= upper bound of seq var j, that is,
##            # if some element that must be in main var can't be in seq var,
##            # the j is not in sel var
##            mainlow_sequp = [DiffSetX(self.varx(LowerSetX, self.mainvar),
##                                      self.compx(IntersectionSetX,
##                                                 self.varx(UpperSetX, s),
##                                                 self.varx(LowerSetX, self.mainvar))) \
##                                 for s in seqs]
##            mainlow_sequp_cond = [CondX(c, DiffSetX(self.constx(ConstantSetX, ALL),
##                                                    self.constx(ConstantSetX, {j}))) for j, c in enumerate(mainlow_sequp)]
##            proj.extend([IntProj(self.selvar, e, self, recursive=True) for e in mainlow_sequp_cond])
##            # If diff of lower bound of main var and union of upper bounds of all seq vars except j is not empty,
##            # then j is sel var
##            cond2exprs = [CondX(c, self.constx(ConstantSetX, {j})) for j, c in enumerate(conds2)]
##            proj.extend([IntProj(self.selvar, e, self, recursive=True) for e in cond2exprs])
##        if not self.mainvar.is_determined():
##            proj.extend([UpperProj(self.mainvar,
##                                   self.compx(UnionSelectX, self.varx(DomainX, self.selvar), upseqs),
##                                   self, upd_reexec_trig={Expr.get_event(self.selvar)}),
##                         LowerProj(self.mainvar,
##                                   IntersSelectX(self.varx(DomainX, self.selvar), [self.varx(LowerSetX, s) for s in seqs]),
##                                   self, upd_reexec_trig={Expr.get_event(self.selvar)})])
##        # If diff of lower bound of main var and union of upper bounds of all seq vars except j is not empty,
##        # then j is sel var and main and seq var are EQUAL
##        for j, (seq, c) in enumerate(zip(seqs, conds2)):
##            if not self.mainvar.is_determined():
##                if iseq:
##                    proj.extend([LowerProj(self.mainvar,
##                                           EqCondX(self.varx(SetCardX, self.varx(DomainX, seq)),
##                                                   self.constx(ConstantIntX, 1),
##                                                   CondX(c, self.varx(DomainX, seq))),
##                                           self, recursive=True,
##                                           upd_reexec_trig={Expr.get_event(self.selvar)}),
##                                 UpperProj(self.mainvar, CondX(c, self.varx(DomainX, seq)),
##                                           self, recursive=True,
##                                           upd_reexec_trig={Expr.get_event(self.selvar)})])
##                else:
##                    proj.extend([LowerProj(self.mainvar, CondX(c, self.varx(LowerSetX, seq)),
##                                           self, recursive=True,
##                                           upd_reexec_trig={Expr.get_event(self.selvar)}),
##                                 UpperProj(self.mainvar, CondX(c, self.varx(UpperSetX, seq)),
##                                           self, recursive=True,
##                                           upd_reexec_trig={Expr.get_event(self.selvar)})])
##            if not seq.is_determined():
##                proj.extend([LowerProj(seq, CondX(c, self.varx(LowerSetX, self.mainvar)),
##                                       self, recursive=True,
##                                       upd_reexec_trig={Expr.get_event(self.selvar)}),
##                             UpperProj(seq, CondX(c, self.varx(UpperSetX, self.mainvar)),
##                                       self, recursive=True,
##                                       upd_reexec_trig={Expr.get_event(self.selvar)})])
##        return proj

    def fails(self, dstore=None):
        """Fail if the domain of sel var includes only indices that are beyond the
        length of seq vars, of if the domain of sel var is empty."""
        selvar = self.selvar
        sel_domain = selvar.get_domain(dstore=dstore)
        if not sel_domain or min(sel_domain) >= len(self.seqvars):
            return True
        elif selvar.determined(dstore=dstore, constraint=self) is not False:
            # If the selvar is determined, check the selected seq var
            seqvar = self.seqvars[selvar.get_value(dstore=dstore)]
            if seqvar.determined(dstore=dstore, constraint=self) is not False:
                # The seqvar is determined too; see if it cannot be equal to the mainvar
                # This is true if the upper bound of mainvar fails to contain values in seqvar's value
                seqval = seqvar.get_value(dstore=dstore)
                # In case seqvar is an IVar, make its value a set
                if not isinstance(seqval, set):
                    seqval = {seqval}
                mainvar = self.mainvar
                mainvar_upper = mainvar.get_upper(dstore=dstore)
                if seqval - mainvar_upper:
                    return True
                # It's also true if the lower bound of mainvar contains values not in seqvar's value
                mainvar_lower = mainvar.get_lower(dstore=dstore)
                if mainvar_lower - seqval:
                    return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar
        changed = set()
        state = Constraint.sleeping

        sel_infer = Selection.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if sel_infer:
            return sel_infer

        if selvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
            # The selection var is determined
            
            # index of selected seq var
            selval = selvar.get_value(dstore=dstore)
            # selected seq var
            sel_seqvar = seqvars[selval]

            # If the selection var is determined, check whether the indexed sequence var
            # is also
            
            if sel_seqvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                selseq_value = sel_seqvar.get_value(dstore=dstore)
                # If it's determined, determine the main var
                if mainvar.determine(selseq_value, dstore=dstore,
                                     constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
#                if self.det_seqs:
#                    state = self.determine_seqs(dstore=dstore, verbosity=verbosity, tracevar=tracevar, changed=changed)                
                return state, changed

            # Otherwise check whether the main var is determined, in which case the selected
            # seq var can be constrained to its value
            if mainvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                mainvalue = mainvar.get_value(dstore=dstore)
                if sel_seqvar.determine(mainvalue, dstore=dstore,
                                        constraint=(verbosity>1 or sel_seqvar in tracevar) and self):
                    changed.add(sel_seqvar)
                    return state, changed

        sel_domain = selvar.get_domain(dstore=dstore)
        
        # The main variable must be a subset of the union of the upper bounds of all
        # sequence variables indexed by the elements in the domain of the selection variable,
        # that is, eliminate any elements from the upper bound that are not in this union
        seq_uppers = [seqvars[j].get_upper(dstore=dstore) for j in sel_domain]
        if mainvar.strengthen_upper(set().union(*seq_uppers), dstore=dstore,
                                    constraint=(verbosity>1 or mainvar in tracevar) and self):
            changed.add(mainvar)
            return state, changed

        # The main variable must be a superset of the intersection of the lower bounds of all
        # sequence variables indexed by the lower bound of the selection variable, that is,
        # add any elements to the lower bound that are in this intersection
        seq_lowers = [seqvars[j].get_lower(dstore=dstore) for j in sel_domain]
        if mainvar.strengthen_lower(seq_lowers[0].intersection(*seq_lowers[1:]), dstore=dstore,
                                    constraint=(verbosity>1 or mainvar in tracevar) and self):
            changed.add(mainvar)
            return state, changed
            
        # If the lower bound of some seqvar is not a subset of mainvar's upper bound,
        # or the upper bound of the seqvar is not a superset of mainvar's lower bound,
        # then exclude its index from selection var's domain
        for j in sel_domain.copy():
            seqvar = seqvars[j]
            if not seqvar.get_lower(dstore=dstore) <= mainvar.get_upper(dstore=dstore) or \
               not seqvar.get_upper(dstore=dstore) >= mainvar.get_lower(dstore=dstore):
                # mainvar cannot equal seqvar, so remove j from selvar's domain
                if selvar.discard_value(j, dstore=dstore,
                                        constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
                    return state, changed

        # If excluding any index from selection var's domain in figuring the
        # union of upper bounds of indexed sequence variables causes the lower bound
        # of the main variable to contain elements not in the union,
        # then that index must be the value of the selection var.
        for j in selvar.get_domain(dstore=dstore):   # Might have changed
            # Consider only indices that in the upper bound of selection variable
            # Exclude j
            indices = sel_domain - {j}
            # Get the union of the upper bounds of the indexed sequence variables
            seqvar_union = set().union(*[seqvars[i].get_upper(dstore=dstore) for i in indices])
            # Does the lower bound of the main variables have any elements not in the union?
            main_union_diff = mainvar.get_lower(dstore=dstore) - seqvar_union
            if len(main_union_diff) > 0:
                # Yes; add the difference to the excluded seq var's lower bound
                if seqvars[j].strengthen_lower(main_union_diff, dstore=dstore,
                                               constraint=(verbosity>1 or seqvars[j] in tracevar) and self):
                    changed.add(seqvars[j])
                    return state, changed
                # and make j the value of the selection var
                if selvar.determine(j, dstore=dstore,
                                    constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
                    return state, changed
        
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))

        return state, changed

class OneSelection(IntSelection):
    """Select one of seq vars for main var."""

    def __init__(self, mainvar, seqvars, problem=None, weight=1):
        selvar = IVar(mainvar.name + ':choice', set(range(len(seqvars))), problem=problem,
                      rootDS=problem.dstore if problem else None)
        IntSelection.__init__(self, mainvar, selvar, seqvars, problem=problem, weight=weight)

class IntIntSelection(Selection):
    """Selection constraint with integer variables as selection variable and main
    variable and determined int variables as seq variables."""

    def __init__(self, mainvar=None, selvar=None, seqvars=None, problem=None, weight=1,
                 maxset=None):
        Selection.__init__(self, mainvar=mainvar, selvar=selvar, seqvars=seqvars,
                           problem=problem, weight=weight)
        self.maxset = maxset or ALL
        self.name = '{0} = {1} [{2}]'.format(self.mainvar, self.format_seq(self.seqvars), self.selvar)

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        seqs = self.seqvars
##        seqvals = tuple([self.varx(DomainX, s) for s in seqs])
##        if not self.selvar.is_determined():
##            # If value of seq var j /<= domain of main var, that is,
##            # if some element in seq var j can't be in main var,
##            # then j is not in sel var
##            # Each s is determined but we need its domain (a set) instead of value (a tuple or int)
##            # because we're using set operations.
##            seqlow_mainup = [DiffSetX(self.varx(DomainX, s),
##                                      self.compx(IntersectionSetX, 
##                                                 self.varx(DomainX, s),
##                                                 self.varx(DomainX, self.mainvar))) \
##                                 for s in seqs]
##            seqlow_mainup_cond = [CondX(c, DiffSetX(self.constx(ConstantSetX, ALL),
##                                                    self.constx(ConstantSetX, {j}))) for j, c in enumerate(seqlow_mainup)]
##            proj.extend([IntProj(self.selvar, e, self, recursive=True) for e in seqlow_mainup_cond])
##        if not self.mainvar.is_determined():
##            proj.extend([IntProj(self.mainvar,
##                                 self.compx(UnionSelectX, self.varx(DomainX, self.selvar), seqvals),
##                                 self, upd_reexec_trig={Expr.get_event(self.selvar)})])
##        return proj

    def fails(self, dstore=None):
        """Fail if the domain of sel var includes only indices that are beyond the
        length of seq vars, of if the domain of sel var is empty."""
        selvar = self.selvar
        sel_domain = selvar.get_domain(dstore=dstore)
        if not sel_domain or min(sel_domain) >= len(self.seqvars):
            return True
        elif selvar.determined(dstore=dstore, constraint=self) is not False:
            # If the selvar is determined, check the selected seq var
            seqvar = self.seqvars[selvar.get_value(dstore=dstore)]
            # The seqvar is determined too; see if it cannot be equal to the mainvar
            # This is true if the upper bound of mainvar fails to contain values in seqvar's value
            seqval = {seqvar.get_value(dstore=dstore)}
            mainvar = self.mainvar
            mainvar_domain = mainvar.get_domain(dstore=dstore)
            if seqval - mainvar_domain:
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar
        changed = set()
        state = Constraint.sleeping

        sel_infer = Selection.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if sel_infer:
            return sel_infer

        if selvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
            # The selection var is determined
            
            # index of selected seq var
            selval = selvar.get_value(dstore=dstore)
            # selected seq var
            sel_seqvar = seqvars[selval]

            selseq_value = sel_seqvar.get_value(dstore=dstore)
            if mainvar.determine(selseq_value, dstore=dstore,
                                 constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return state, changed

        sel_domain = selvar.get_domain(dstore=dstore)
        
        # The main variable must be a subset of the union of the values of all
        # sequence variables indexed by the elements in the domain of the selection variable;
        # that is, eliminate any elements from the domain that are not in this union
        seq_vals = {seqvars[j].get_value(dstore=dstore) for j in sel_domain}
        if mainvar.strengthen(seq_vals, dstore=dstore,
                              constraint=(verbosity>1 or mainvar in tracevar) and self):
            changed.add(mainvar)
            return state, changed

        # If the lower bound of some seqvar is not a subset of mainvar's upper bound,
        # or the upper bound of the seqvar is not a superset of mainvar's lower bound,
        # then exclude its index from selection var's domain
        for j in sel_domain.copy():
            seqvar = seqvars[j]
            if seqvar.get_value(dstore=dstore) not in mainvar.get_domain(dstore=dstore):
                # mainvar cannot equal seqvar, so remove j from selvar's domain
                if selvar.discard_value(j, dstore=dstore,
                                        constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
                    return state, changed
        
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))

        return state, changed

class UnionSelection(Selection):
    '''All variables can be set vars; seq vars can also be int vars.
    Select the union of the selected sets.'''

    def __init__(self, mainvar=None, selvar=None, seqvars=None, pattern=False, problem=None, weight=1,
                 maxset=None):
        Selection.__init__(self, mainvar=mainvar, selvar=selvar, seqvars=seqvars,
                           pattern=pattern, problem=problem, weight=weight)
        self.pattern = pattern
        self.maxset = maxset or ALL
        self.name = '{0} = U{1} [{2}]'.format(self.mainvar, self.format_seq(self.seqvars), self.selvar)

##    def get_projectors(self, assign_to_var=True):
##        """Constraints from Duchier, Fig. 15."""
##        proj = []
##        sel, main, seqs = self.selvar, self.mainvar, self.seqvars
##        conds2 = [self.compx(UnionSelectX, self.varx(UpperSetX, sel), tuple([self.varx(UpperSetX, s) for s in seqs]), k)\
##                      for k, s in enumerate(seqs)]
##        conds2 = [DiffSetX(self.varx(LowerSetX, main), c) for c in conds2]
##        if not sel.is_determined():
##            # It seems that selvar's upper bound is already constrained to be within the
##            # set of seqvar indices
###            proj.append(UpperProj(sel, self.constx(ConstantSetX, set(range(len(seqs)))), self))
##            # If lower bound of seq var j /<= upper bound of main var, then j is not in sel var
##            conds1 = [DiffSetX(self.varx(LowerSetX, s),
##                               self.compx(IntersectionSetX,
##                                           self.varx(LowerSetX, s),
##                                           self.varx(UpperSetX, main))) \
##                          for s in seqs]
##            cond1exprs = [CondX(c, DiffSetX(self.constx(ConstantSetX, ALL),
##                                            self.constx(ConstantSetX, {j}))) for j, c in enumerate(conds1)]
##            proj.extend([UpperProj(sel, e, self) for e in cond1exprs])
##            # If diff of lower bound of main var and union of upper bounds of all seq vars except j is not empty,
##            # then j is in sel var
##            cond2exprs = [CondX(c, self.constx(ConstantSetX, {j})) for j, c in enumerate(conds2)]
##            proj.extend([LowerProj(sel, e, self, recursive=True,
##                                   upd_reexec_trig={Expr.get_event(sel, card=0, end=1)}) \
##                             for e in cond2exprs])
##        if not main.is_determined():
##            proj.extend([UpperProj(main, self.compx(UnionSelectX, self.varx(UpperSetX, sel),
##                                                    tuple([self.varx(UpperSetX, s) for s in seqs])),
##                                   self, upd_reexec_trig={Expr.get_event(sel, card=0, end=1)}),
##                         LowerProj(main, self.compx(UnionSelectX, self.varx(LowerSetX, sel),
##                                                    tuple([self.varx(LowerSetX, s) for s in seqs])),
##                                   self, upd_reexec_trig={Expr.get_event(sel, card=0, end=0)}),
##                         # Upper cardinality of main must be at most max of upper cardinalities of
##                         # possible sequence variables (not in Duchier!)
##                         # Should actually be the SUM of the upper cardinalities...
###                         UCardProj(main, SetMaxX(ListSelectX(self.varx(UpperSetX, sel), [self.varx(UpperCardX, s) for s in seqs])),
###                                   self, upd_reexec_trig={Expr.get_event(sel, card=0, end=0)}),
##                         # Lower cardinality of main must be at least max of lower cardinalities of
##                         # required sequence variables (not in Duchier!)
##                         LCardProj(main, SetMaxX(self.compx(ListSelectX,
##                                                            self.varx(LowerSetX, sel),
##                                                            tuple([self.varx(LowerCardX, s) for s in seqs]))),
##                                   self, upd_reexec_trig={Expr.get_event(sel, card=0, end=0)})])
##                         
##        # Lower bound of sel var j >= diff of lower bound of main var and union of upper bounds of all seq vars except j
##        # AND (not in Duchier!)
##        # for all seqs in lower bound of sel var, exclude from upper bound all elements not in upper bound of main var
##        for index, (seq, e) in enumerate(zip(seqs, conds2)):
##            if not seq.is_determined():
##                if isinstance(seq, IVar):
##                    proj.append(IntProj(seq,
##                                        MemCondX(self.varx(LowerSetX, sel), index,
##                                                 DiffSetX(self.constx(ConstantSetX, self.maxset),
##                                                          DiffSetX(self.varx(DomainX, seq), self.varx(UpperSetX, main)))),
##                                        self, recursive=True,
##                                        upd_reexec_trig={Expr.get_event(sel, card=0, end=0)}))
##                else:
##                    proj.extend([LowerProj(seq, e, self, upd_reexec_trig={Expr.get_event(sel, card=0, end=1)}),
##                                 UpperProj(seq,
##                                           MemCondX(self.varx(LowerSetX, sel), index,
##                                                    DiffSetX(self.constx(ConstantSetX, self.maxset),
##                                                             DiffSetX(self.varx(UpperSetX, seq), self.varx(UpperSetX, main)))),
##                                           self, recursive=True,
##                                           upd_reexec_trig={Expr.get_event(sel, card=0, end=0)})])
##        return proj

    def sel_lower(self, dstore=None):
        """Values that must be selected."""
        seq_len = len(self.seqvars)
        selvar_lower = self.selvar.get_lower(dstore=dstore)
        if any([i >= seq_len for i in selvar_lower]):
            return False
        res = set()
        for i in selvar_lower:
            if i < len(self.seqvars):
                res.update(self.seqvars[i].get_lower(dstore=dstore))
        return res

    def fails(self, dstore=None):
        """Fail
        (1) if the lower bound of sel var has indices beyond the length of seq vars
        (2) if the upper bound of mainvar excludes a value that must be in it
        (3) if the lower bound of mainvar includes values that cannot be in the union
            of selected seq vars (upper bounds of seq vars selected by upper bound of
            sel var)
        """
        sel_low = self.sel_lower(dstore=dstore)
        if sel_low is False:
#            print(self, 'fails because of sel_low')
            # This should actually fail but allow it to succeed
            sel_low = set()
        mainupper = self.mainvar.get_upper(dstore=dstore)
        if len(sel_low - self.mainvar.get_upper(dstore=dstore)) > 0:
            # If this is pattern matching mode, make sure mainvar's upper bound unifies
            # with selected seq variables' lower bounds.
            if self.pattern:
                if not unify_fssets(sel_low, mainupper):
#                    print(self, 'fails because', sel_low, 'and', mainupper, "don't unify")
                    return True
            else:
                # Values that must be selected for mainvar include at least one that is not
                # in the upper bound for mainvar
#                print(self, 'fails otherwise')
                return True
        # If the values that must be included in mainvar include values that are excluded
        # from those that can be selected, fail
        mainlower = self.mainvar.get_lower(dstore=dstore)
        selupper = self.selvar.get_upper(dstore=dstore)
        maxsel = set()
        for index, seq in enumerate(self.seqvars):
            if index in selupper:
                sequpper = seq.get_upper(dstore=dstore)
                maxsel.update(sequpper)
        if self.pattern:
            # Remove any wildcard patterns from mainlower
            mainlower_const = {x for x in mainlower if -1 not in x}
            if mainlower_const - unify_fssets(mainlower, maxsel):
                return True
        elif mainlower - maxsel:
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar
        changed = set()
        state = Constraint.sleeping

        sel_infer = Selection.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if sel_infer:
            return sel_infer

        if selvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
            # If the selection var is determined, check whether the indexed sequence vars
            # are also
            all_determined = True
            selval = selvar.get_value(dstore=dstore)
            selseqs = [seqvars[index] for index in selval if index < len(seqvars)]
            result = set()
            for seq in selseqs:
                if seq.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                    result.update(seq.get_lower(dstore=dstore))
                else:
                    all_determined = False
            if all_determined:
                # If so, determine the main var
                if mainvar.determine(result, dstore=dstore, pattern=self.pattern, 
                                     constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return state, changed
            # Also check whether the main var is determined, in which case the seq vars
            # can possibly be constrained
            if mainvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                mainvalue = mainvar.get_value(dstore=dstore)
                # Remove any values from upper bounds that are not in main var
                for seq in selseqs:
                    seq_up = seq.get_upper(dstore=dstore)
#                    if self.pattern:
#                        # unused_up is everything in seq's upper bound that fails to unify with mainvalue
#                        unused_up = no_unify_fssets(seq_up, mainvalue)
#                    else:
                        # unused_up is everything in seq's upper bound that's not in mainvalue
                    unused_up = seq_up - mainvalue
                    if unused_up:
                        if len(seq_up - unused_up) < seq.get_lower_card(dstore=dstore):
                            if verbosity:
                                if seq in tracevar:
                                    s = '  {} attempting to discard {} from upper bound of {}, making it too small'
                                    print(s.format(self, unused_up, seq))
                                print('{} failed'.format(self))
#                            print(self, 'failed because of attempt to make upper bound too small')
                            return Constraint.failed, set()
                        if seq.discard_upper(unused_up, dstore=dstore,
                                             constraint=(verbosity>1 or seq in tracevar) and self):
#                            if tracevar==seq:
#                                print(self, 'discarding', unused_up, 'from', seq, 'mainvalue', mainvalue, 'seq_up', seq_up)
                            changed.add(seq)
                            return state, changed
            # Even if seqvars are not determined, we may be able to constrain mainvar (as long as it's not
            # already determined)
            else:
                main_lowcard = max([seq.get_lower_card(dstore=dstore) for seq in selseqs])
                if mainvar.strengthen_lower_card(main_lowcard, dstore=dstore,
                                                 constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                    return state, changed
                seq_uppers = [seq.get_upper(dstore=dstore) for seq in selseqs]
                seq_up_union = set().union(*seq_uppers)
                if mainvar.strengthen_upper(seq_up_union, dstore=dstore, pattern=self.pattern, 
                                            reduce=True,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                    return state, changed
                if mainvar.strengthen_upper_card(len(seq_up_union), dstore=dstore,
                                                 constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                    return state, changed
                seq_lowers = [seq.get_lower(dstore=dstore) for seq in selseqs]
                if mainvar.strengthen_lower(set().union(*seq_lowers), dstore=dstore,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
#                    if tracevar in selseqs:
#                        print(self, 'strengthening lower main 1', seq_lowers, seq_uppers, mainvar.get_upper(dstore=dstore),
#                              mainvar.get_upper_card(dstore=dstore))
                    changed.add(mainvar)
                    return state, changed

        ## OK, so selvar is not determined; try changing mainvar if it's not determined
        if mainvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is False:
            # The main variable must be a subset of the union of the upper bounds of all
            # sequence variables indexed by the upper bound of the selection variable.
            selupper = selvar.get_upper(dstore=dstore)
            if not self.pattern or selvar.get_lower(dstore=dstore):
                for j in selupper:
                    if j >= len(seqvars):
                        print(self, 'seqvars', seqvars, 'too short for', selupper, 'of variable', selvar)
                seq_uppers = [seqvars[j].get_upper(dstore=dstore) for j in selupper if j < len(seqvars)]
                if mainvar.strengthen_upper(set().union(*seq_uppers), dstore=dstore, pattern=self.pattern, 
                                            reduce=True,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                    return state, changed
            # The main variable must be a superset of the union of the lower bounds of all
            # sequence variables indexed by the lower bound of the selection variable.
            seq_lowers = [seqvars[j].get_lower(dstore=dstore) for j in selvar.get_lower(dstore=dstore)]
            if mainvar.strengthen_lower(set().union(*seq_lowers), dstore=dstore,
                                        constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
                return state, changed
        # If the lower bound of some seqvar is not a subset of mainvar's upperbound,
        # then exclude its index from selection var (remove it from the selection var's
        # upper bound)
        for j in selvar.get_upper(dstore=dstore).copy():
            # Consider only indices for seq vars that are in the upper bound of selection variable
            if j >= len(seqvars):
                continue
            seqvar = seqvars[j]
            seqlower = seqvar.get_lower(dstore=dstore)
            mainupper = mainvar.get_upper(dstore=dstore)
            if not seqlower <= mainupper:
                # If pattern is True and seqlower and mainupper unify, it's still OK
                if not self.pattern or not unify_fssets(seqlower, mainupper):
                    # This should fail if by discarding j, the cardinality of upper has gone below lower card
                    if len(selvar.get_upper(dstore=dstore) - {j}) < selvar.get_lower_card(dstore=dstore):
                        if verbosity:
                            if selvar in tracevar:
                                s = '  {} attempting to discard {} from upper bound of {}, making it too small'
                                print(s.format(self, j, selvar))
                            print('{} failed'.format(self))
                        return Constraint.failed, set()
                    if selvar.discard_upper(j, dstore=dstore, constraint=(verbosity>1 or selvar in tracevar) and self):
                        changed.add(selvar)
                        return state, changed
        # If excluding any index from selection var's upper bound in figuring the
        # union of upper bounds of indexed sequence variables causes the lower bound
        # of the main variable to contain elements not in the union,
        # then add those elements to the excluded sequence
        # variable and the excluded index to the selection variable's lower bound
        selvar_upper = selvar.get_upper(dstore=dstore)
        for j in selvar_upper:
            if j >= len(seqvars):
                continue
            # Consider only indices in the upper bound of selection variable
            # Exclude j
            indices = selvar_upper - {j}
            # Get the union of the upper bounds of the indexed sequence variables
            seqvar_union = set().union(*[seqvars[i].get_upper(dstore=dstore) for i in indices if i < len(seqvars)])
            # Does the lower bound of the main variable have any elements not in the union?
            main_union_diff = mainvar.get_lower(dstore=dstore) - seqvar_union
            if len(main_union_diff) > 0:
#                print(self, 'excluding index', j, 'indices', indices, 'seqvar_union',
#                      seqvar_union, 'main_union_diff', main_union_diff)
#                print('  Attempting to strengthen lower bound of', seqvars[j])
                # Yes; add the difference to the excluded seq var's lower bound
                if seqvars[j].strengthen_lower(main_union_diff, dstore=dstore,
                                               constraint=(verbosity>1 or seqvars[j] in tracevar) and self):
                    changed.add(seqvars[j])
                    return state, changed
                # and add the index to selection var's lower bound
                if selvar.strengthen_lower({j}, dstore=dstore,
                                           constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
                    return state, changed
        # For all seq vars in the lower bound of selvar, exclude any elements that are not in the
        # upper bound of mainvar (not in Duchier??)
        selvar_lower = selvar.get_lower(dstore=dstore)
        mainvar_upper = mainvar.get_upper(dstore=dstore)
        seqvar_upper = set().union(*[seqvars[i].get_upper(dstore=dstore) for i in selvar_lower if i < len(seqvars)])
        seq_main_diff = seqvar_upper - mainvar_upper
        if seq_main_diff:
            for j in selvar_lower:
                if j >= len(seqvars):
                    continue
                seq = seqvars[j]
#                if seq in tracevar:
                if seq.discard_upper(seq_main_diff, dstore=dstore,
                                     constraint=(verbosity>1 or seq in tracevar) and self):
#                    print(self, 'discarding', seq_main_diff, 'from', seq,
#                          'mainvar_upper', mainvar_upper,
#                          'seqvar_upper', seqvar_upper,
#                          'selvar_lower', selvar_lower)
                    changed.add(seq)
                    return state, changed
                
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return state, changed

class IntersectionSelection(Selection):
    '''All variables are set vars. Select the intersection of the selected sets.'''

    def __init__(self, mainvar=None, selvar=None, seqvars=None, problem=None, weight=1):
        Selection.__init__(self, mainvar=mainvar, selvar=selvar, seqvars=seqvars,
                           problem=problem, weight=weight)
        self.name = '{0} = ^{1} [{2}]'.format(self.mainvar, self.format_seq(self.seqvars), self.selvar)

##    def get_projectors(self, assign_to_var=True):
##        """Constraints from Duchier, Fig. 15."""
##        proj = []
##        sel, main, seqs = self.selvar, self.mainvar, self.seqvars
##        # If diff of inters of lower bounds of all seq vars except j and upper bound of main var and  is not empty,
##        # then j e sel var
##        conds2 = [IntersSelectX(self.varx(LowerSetX, sel), [self.varx(LowerSetX, s) for s in seqs], k) for k, s in enumerate(seqs)]
##        conds2 = [DiffSetX(c, self.varx(UpperSetX, main), c) for c in conds2]
##        if not sel.is_determined():
##            proj.append(UpperProj(sel, self.constx(ConstantSetX, set(range(len(seqs)))), self))
##            # If lower bound of main var /<= upper bound of seq var j, then j /e sel var
##            conds1 = [DiffSetX(self.varx(LowerSetX, main), \
##                                   self.compx(IntersectionSetX, self.varx(LowerSetX, main), self.varx(UpperSetX, s))) \
##                          for s in seqs]
##            cond1exprs = [CondX(c, ComplementSetX(self.constx(ConstantSetX, {j}))) for j, c in enumerate(conds1)]
##            proj.extend([UpperProj(sel, e, self) for e in cond1exprs])
##            cond2exprs = [CondX(c, self.constx(ConstantSetX, {j})) for j, c in enumerate(conds2)]
##            proj.extend([LowerProj(sel, e, self, recursive=True,
##                                   upd_reexec_trig={Expr.get_event(sel, card=0, end=0)}) \
##                             for e in cond2exprs])
##        if not main.is_determined():
##            proj.extend([LowerProj(main, IntersSelectX(self.varx(UpperSetX, sel), [self.varx(LowerSetX, s) for s in seqs]),
##                                   self, recursive=True,
##                                   upd_reexec_trig={Expr.get_event(sel, card=0, end=1)}),
##                         UpperProj(main,
##                                   IntersSelectX(self.varx(LowerSetX, sel), [self.varx(UpperSetX, s) for s in seqs]),
##                                   self, recursive=True,
##                                   upd_reexec_trig={Expr.get_event(sel, card=0, end=0)})])
##        # Upper bound of seq var j in lower bound of sel var
##        # <= complement of diff of intersection of lower bounds of all seq vars except j
##        # and upper bound of main var
##        # AND (this one is NOT in Duchier!)
##        # Lower bound of seq var j in lower bound of sel var
##        # >=  lower bound of main var
##        for index, (seq, e) in enumerate(zip(seqs, conds2)):
##            if not seq.is_determined():
##                proj.extend([UpperProj(seq, ComplementSetX(e),
##                                       self, recursive=True,
##                                       upd_reexec_trig={Expr.get_event(sel, card=0, end=0)}),
##                             LowerProj(seq,
##                                       CondX(DiffSetX(self.constx(ConstantSetX, {index}), self.varx(LowerSetX, sel)),
##                                             self.varx(LowerSetX, main),
##                                             False),
##                                       self, recursive=True,
##                                       upd_reexec_trig={Expr.get_event(sel, card=0, end=0)})])
##        return proj

    def sel_upper(self, dstore=None):
        """Upper bound on values that *can* be selected."""
        seq_len = len(self.seqvars)
        selvar_lower = self.selvar.get_lower(dstore=dstore)
        if not selvar_lower:
            # There's nothing we can say about what must be selected
            return True
        if any([i >= seq_len for i in selvar_lower]):
            return False
        selvar_lower = list(selvar_lower)
        res = self.seqvars[selvar_lower[0]].get_upper(dstore=dstore)
        for i in selvar_lower[1:]:
            res = res & self.seqvars[i].get_upper(dstore=dstore)
        return res

    def fails(self, dstore=None):
        """Fail if the lower bound of sel var has indices beyond the length of seq vars
        or if the lower bound of mainvar is a superset of the values that can be included."""
        sel_upper = self.sel_upper(dstore=dstore)
        if sel_upper is False:
#            print('Failed because sel_upper', sel_upper, 'is False')
            return True
        if sel_upper is True:
            return False
        if sel_upper < self.mainvar.get_lower(dstore=dstore):
            # Lower bound of mainvar includes values that can't be selected
#            print('Failed because sel_upper', sel_upper, 'is less than main lower', self.mainvar.get_lower(dstore=dstore))
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar
        changed = set()
        state = Constraint.sleeping

        sel_infer = Selection.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if sel_infer:
            return sel_infer

        if selvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
            # If the selection var is determined, check whether the indexed sequence vars
            # are also
            all_determined = True
            selval = selvar.get_value(dstore=dstore)
            to_intersect = []
            for index in selval:
                seq = seqvars[index]
                if seq.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                    # Intersect result with lower bound of seq
                    to_intersect.append(seq.get_lower(dstore=dstore))
                else:
                    all_determined = False
            if all_determined:
                # Intersect the sets found in lower bounds
                if to_intersect:
                    inters = to_intersect[0].intersection(*to_intersect[1:])
                else:
                    inters = set()
                # If so, determine the main var using the accumulated intersection
                if mainvar.determine(inters, dstore=dstore, constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return state, changed
            # Also check whether the main var is determined, in which case the seq vars
            # can possibly be constrained
            if mainvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                mainvalue = mainvar.get_value(dstore=dstore)
                # Selected seq vars
                selseqs = [seqvars[i] for i in selval]
                # Lower bounds of selected seq vars
                seqlower = list([seq.get_lower(dstore=dstore) for seq in selseqs])
                # Upper bounds of selected seq vars
                sequpper = [seq.get_upper(dstore=dstore) for seq in selseqs]
                # Intersection of lower bounds
                seqinters = seqlower[0].intersection(*seqlower[1:])
                # Unaccounted for elements in main value; these have to appear in all seq vars
                unaccounted = mainvalue - seqinters
                for seq in selseqs:
                    if seq.strengthen_lower(unaccounted, dstore=dstore,
                                            constraint=(verbosity>1 or seq in tracevar) and self):
                        changed.add(seq)

        # The main variable must be a superset of the intersection of the lower bounds of all
        # sequence variables indexed by the upper bound of the selection variable.
        seq_lowers = list([seqvars[j].get_lower(dstore=dstore) for j in selvar.get_upper(dstore=dstore)])
        if mainvar.strengthen_lower(seq_lowers[0].intersection(*seq_lowers[1:]), dstore=dstore,
                                    constraint=(verbosity>1 or mainvar in tracevar) and self):
            changed.add(mainvar)
        sellower = selvar.get_lower(dstore=dstore)
        if len(sellower) > 0:
            # The main variable must be a subset of the intersection of the upper bounds of all
            # sequence variables indexed by the lower bound of the selection variable.
            seq_uppers = list([seqvars[j].get_upper(dstore=dstore) for j in sellower])
            if mainvar.strengthen_upper(seq_uppers[0].intersection(*seq_uppers[1:]), dstore=dstore,
                                        constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
        # If the upper bound of some seqvar is not a superset of mainvar's lower bound,
        # then exclude its index from selection var (remove it from the selection var's
        # upper bound)
        for j in selvar.get_upper(dstore=dstore).copy():
            # Consider only indices that are in the upper bound of selection variable
            seqvar = seqvars[j]
            if not seqvar.get_upper(dstore=dstore) >= mainvar.get_lower(dstore=dstore):
                if selvar.discard_upper(j, dstore=dstore, constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
        # If excluding any index from selection var's LOWER bound in figuring the
        # INTERSECTION of LOWER bounds of indexed sequence variables causes INTERSECTION to
        # contain elements not in the UPPER bound of the main variable,
        # then EXCLUDE those elements from the upper bound of the excluded seq var
        # and add the excluded index to the selection variable's lower bound
        for j in sellower:
            # Consider only indices that in the lower bound of selection variable
            # Exclude j
            indices = sellower - {j}
            # Get the intersection of the lower bounds of the indexed sequence variables
            seq_lowers = list([seqvars[i].get_lower(dstore=dstore) for i in indices])
            if not seq_lowers:
                continue
            seqvar_inters = seq_lowers[0].intersection(*seq_lowers[1:])
            # Does this intersection have any values not in the upper bound of the main var
            inters_main_diff = seqvar_inters - mainvar.get_upper(dstore=dstore)
            if len(inters_main_diff) > 0:
                # Yes; exclude the values in the intersection from the excluded seq var's upper bound
                for val in inters_main_diff:
                    if seqvars[j].discard_upper(val, dstore=dstore,
                                                constraint=(verbosity>1 or seqvars[j] in tracevar) and self):
                        changed.add(seqvars[j])
                # and add the index to selection var's lower bound
                if selvar.strengthen_lower({j}, dstore=dstore, constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return state, changed

class SimplePrecedenceSelection(Propagator):
    """
    Simpler than PrecedenceSelection.
    posvars: set vars consisting of int positions
    selvar: a set var consisting of indices within posvars, whose values must appear
      in the order they appear in in posvars
    """

    def __init__(self, selvar=None, posvars=None, problem=None,
                 principle=None, weight=1, maxset=None):
        Propagator.__init__(self, [selvar] + posvars, problem=problem,
                            principle=principle, weight=weight)
        self.selvar = selvar
        self.posvars = posvars
        self.maxset = maxset or ALL
        self.name = '<...< {} [{}]'.format(Selection.format_seq(self.posvars), self.selvar)

##    def get_projectors(self, assign_to_var=True):
##        """Selvar is a tuple set variable."""
##        proj = []
##        sel, pos = self.selvar, self.posvars
##        # For all positions indexed in the upper bound of selvar,
##        # if they cannot appear in the right order, remove the index from selvar
##        if not sel.is_determined():
##            proj.append(
##                UpperProj(sel,
##                          ComplementSetX(self.compx(SimplePrecSelectX,
##                                                     (self.varx(UpperSetX, sel), self.varx(LowerSetX, sel)),
##                                                     tuple([self.varx(LowerSetX, p) for p in pos]),
##                                                     (),
##                                                     0)),
##                          self, recursive=True))
##        # For each posvar indexed in sel's lower bound,
##        # eliminate positions in posvar's upper bound that are
##        # >= min of later posvars' lower bounds and
##        # <= max of earlier posvars' lower bounds and
##        # >= max of later posvars' upper bounds
##        # <= min of earlier posvar's upper bounds
##        for index, p in enumerate(pos):
##            if not p.is_determined():
##                proj.extend([
##                        UpperProj(p,
##                                  ComplementSetX(Min2MaxIntX(self.compx(SimplePrecSelectX,
##                                                                        (self.varx(LowerSetX, sel), None),
##                                                                        tuple([self.varx(UpperSetX, p1) for p1 in pos]),
##                                                                        tuple([self.varx(LowerSetX, p1) for p1 in pos]),
##                                                                        1, index),
##                                                             self.constx(ConstantIntX, MAX))),
##                                  self, recursive=True),
##                        UpperProj(p,
##                                  ComplementSetX(Min2MaxIntX(self.constx(ConstantIntX, 0),
##                                                             self.compx(SimplePrecSelectX,
##                                                                        (self.varx(LowerSetX, sel), None),
##                                                                        tuple([self.varx(UpperSetX, p1) for p1 in pos]),
##                                                                        tuple([self.varx(LowerSetX, p1) for p1 in pos]),
##                                                                        2, index))),
##                                  self, recursive=True),
##                        UpperProj(p,
##                                  ComplementSetX(Min2MaxIntX(self.compx(SimplePrecSelectX,
##                                                                        (self.varx(LowerSetX, sel), None),
##                                                                        tuple([self.varx(UpperSetX, p1) for p1 in pos]),
##                                                                        tuple([self.varx(LowerSetX, p1) for p1 in pos]),
##                                                                        3, index),
##                                                             self.constx(ConstantIntX, MAX))),
##                                  self, recursive=True),
##                        UpperProj(p,
##                                  ComplementSetX(Min2MaxIntX(self.constx(ConstantIntX, 0),
##                                                             self.compx(SimplePrecSelectX,
##                                                                        (self.varx(LowerSetX, sel), None),
##                                                                        tuple([self.varx(UpperSetX, p1) for p1 in pos]),
##                                                                        tuple([self.varx(LowerSetX, p1) for p1 in pos]),
##                                                                        4, index))),
##                                  self, recursive=True),
##                        ])
##        return proj

    def get_upper_posvars(self, dstore=None):
        """All posvars included in the upper bound of the selvar."""
        selupper = self.selvar.get_upper(dstore=dstore)
        return [posvar for index, posvar in enumerate(self.posvars) if index in selupper]

    def get_lower_posvars(self, dstore=None):
        """All posvars included in the lower bound of the selvar."""
        sellower = self.selvar.get_lower(dstore=dstore)
        return [posvar for index, posvar in enumerate(self.posvars) if index in sellower]

    def is_entailed(self, dstore=None):
        """Entailed if all variables are determined or
        if all indices that *could* be included are already in the right order.
        """
        if self.selvar.determined(dstore=dstore, constraint=self) is not False \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.posvars]):
            return True
        upperposvars = self.get_upper_posvars(dstore=dstore)
        for posvar1, posvar2 in itertools.combinations(upperposvars, 2):
            if not SetPrecedence.must_precede(posvar1, posvar2, dstore=dstore):
                return False
        return True

    def fails(self, dstore=None):
        """Fail if the lower bound of selvar includes position variables
        that necessarily violate the precedence constraint."""
        lowerposvars = self.get_lower_posvars(dstore=dstore)
        for posvar1, posvar2 in itertools.combinations(lowerposvars, 2):
            if SetPrecedence.cant_precede(posvar1, posvar2, dstore=dstore):
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        state = Constraint.sleeping
        Constraint.infer(self, verbosity=verbosity, tracevar=tracevar)

        ## Constrain the selection variable based on the position variables.
        # For each index in the sel var's upper bound, check to see whether
        # the possible precedence constraints can't succeed
        discard_selup = set()
        strengthen_sellow = set()
        selupper = self.selvar.get_upper(dstore=dstore)
        sellower = self.selvar.get_lower(dstore=dstore)
        upper_i_var = [(index, self.posvars[index]) for index in selupper]
        lower_i_var = [(index, self.posvars[index]) for index in sellower]
        for index1, posvar1 in upper_i_var:
            for index2, posvar2 in lower_i_var:
                if index1 < index2:
                    if SetPrecedence.cant_precede(posvar1, posvar2, dstore=dstore):
                        discard_selup.add(index1)
                elif index1 > index2:
                    if SetPrecedence.cant_precede(posvar2, posvar1, dstore=dstore):
                        discard_selup.add(index1)
        if discard_selup:
            if self.selvar.discard_upper(discard_selup, dstore=dstore,
                                         constraint=(verbosity>1 or self.selvar in tracevar) and self):
                changed.add(self.selvar)
                return state, changed

        ## Constrain the position variables based on the selection variable.
        # For each pair of indices in the sel var's lower bound, check to see
        # whether indices can be excluded from the upper bounds of the corresponding
        # position variables.
        lowerposvars = self.get_lower_posvars(dstore=dstore)
        for index, v1 in enumerate(lowerposvars[:-1]):
            for v2 in lowerposvars[index+1:]:
                v1_low = v1.get_lower(dstore=dstore)
                v2_low = v2.get_lower(dstore=dstore)
                v1_up = v1.get_upper(dstore=dstore)
                v2_up = v2.get_upper(dstore=dstore)

                # If the lower bound on v1 is not empty, v2 must be a subset of
                # {min(MAX, max(v1 + 1)), ..., MAX}
                if v1_low and v1_up and v2_up:
                    v2_up_new = range(min([max(v1_up), max(v1_low) + 1]), max(v2_up)+1)
                    if v2.strengthen_upper(v2_up_new, dstore=dstore,
                                           constraint=(verbosity>1 or v2 in tracevar) and self):
                        changed.add(v2)
                        return state, changed
                # If the lower bound on v2 is not empty, v1 must be a subset of
                # {0, ..., max(0, min(v2_low) - 1)}
                if v2_low:
                    v1_up_new = range(0, max([0, min(v2_low) - 1]) + 1)
                    if v1.strengthen_upper(v1_up_new, dstore=dstore,
                                           constraint=(verbosity>1 or v1 in tracevar) and self):
                        changed.add(v1)
                        return state, changed
                v1_up = v1.get_upper(dstore=dstore)
                v2_up = v2.get_upper(dstore=dstore)            
                if v1_up and v2_up and v1.get_lower_card(dstore=dstore) and v2.get_lower_card(dstore=dstore):
                    # Eliminate elements of v1 upper that are >= max of v2 upper
                    lowenough1 = {x for x in v1_up if x < max(v2_up)}
                    if v1.strengthen_upper(lowenough1, dstore=dstore, 
                                           constraint=(verbosity>1 or v1 in tracevar) and self):
                        changed.add(v1)
                        return state, changed
                    # Eliminate elements of v2 upper that are <= min of v1 upper
                    # (v1_up might have changed and might now be empty)
                    v1_up = v1.get_upper(dstore=dstore)
                    if v1_up:
                        highenough2 = {x for x in v2_up if x > min(v1_up)}
                        if v2.strengthen_upper(highenough2, dstore=dstore, 
                                               constraint=(verbosity>1 or v2 in tracevar) and self):
                            changed.add(v2)
                            return state, changed
        return state, changed

##class CardSelection(Propagator):
##    """
##    Only used for projectors.
##
##    mainvar: set var whose cardinalities are selected for
##    cardvars: int vars (always determined?) representing either lower or upper card
##    selvar: an int var specifying an index within the list of cardvars
##    """
##
##    def __init__(self, mainvar=None, selvar=None, cardvars=None, problem=None,
##                 principle=None, weight=1, lower=True):
##        Propagator.__init__(self, [mainvar, selvar] + cardvars, problem=problem,
##                            principle=principle, weight=weight)
##        self.mainvar = mainvar
##        self.selvar = selvar
##        self.cardvars = cardvars
##        # Whether cardvars represent lower, as opposed to, upper cardinalities
##        self.lower = lower
##        self.name = '|{0}| = {1} [{2}]'.format(self.mainvar, Selection.format_seq(self.cardvars), self.selvar)
##
##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        main, sel, cards = self.mainvar, self.selvar, self.cardvars
##        # For the card vars indexed in the domain of selvar
##        # if any is incompatible with mainvar, that is, if the
##        # lower card in card var > length of mainvar's upper bound or the
##        # upper card in card var < length of mainvar's lower bound, then
##        # remove its index from selvar
##        if not sel.is_determined():
##            for index, card in enumerate(cards):
##                if self.lower:
##                    proj.append(IntProj(sel,
##                                        CondX(DiffIntX(self.compx(CardSelectX, self.varx(DomainX, sel),
##                                                                  tuple([self.varx(ValueIntX, c) for c in cards]),
##                                                                  index),
##                                                       SumIntX(self.constx(ConstantIntX, 1),
##                                                               self.varx(SetCardX, self.varx(UpperSetX, main)))),
##                                              ComplementSetX(self.constx(ConstantSetX, {index}))),
##                                        self, recursive=True))
##                else:
##                    proj.append(IntProj(sel,
##                                        CondX(DiffIntX(self.varx(SetCardX, self.varx(LowerSetX, main)),
##                                                       SumIntX(self.constx(ConstantIntX, 1),
##                                                               self.compx(CardSelectX, self.varx(DomainX, sel),
##                                                                           tuple([self.varx(ValueIntX, c) for c in cards]),
##                                                                           index))),
##                                              ComplementSetX(self.constx(ConstantSetX, {index}))),
##                                        self, recursive=True))
##        if not main.is_determined():
##            # Constrain mainvar's upper cardinality by the maximum of the selected upper cardinalities
##            # and constrain its lower cardinality by the minimum of the selected lower cardinalities
##            if self.lower:
##                proj.append(LCardProj(main,
##                                      SetMinX(self.compx(CardSelectX, self.varx(DomainX, sel),
##                                                         tuple([self.varx(ValueIntX, c) for c in cards]))),
##                                      self))
##            else:
##                proj.append(UCardProj(main,
##                                      SetMaxX(self.compx(CardSelectX, self.varx(DomainX, sel),
##                                                         tuple([self.varx(ValueIntX, c) for c in cards]))),
##                                      self))
##        return proj

class PrecedenceSelection(Propagator):
    """
    PrecedenceSelection is different enough from UnionSelection and IntersectionSelection
    in that it doesn't inherit from the Selection class.
    
    posvars: set vars consisting of int positions (determined for analysis, not for generation)
    selvar: a set var consisting of pairs of indices within posvars, each
    pair specifying a precedence constraint between the corresponding sets
    """

    def __init__(self, selvar=None, posvars=None, problem=None,
                 weight=1, principle=None, maxset=None):
        Propagator.__init__(self, [selvar] + posvars, problem=problem,
                            principle=principle, weight=weight)
        self.selvar = selvar
        self.posvars = posvars
        # Maximum set of tuples for the particular problem (normally depends on number of arc
        # labels for LP dimension)
        self.maxset = maxset or ALL
        self.name = '<< {} [{}]'.format(Selection.format_seq(self.posvars), self.selvar)

##    def get_projectors(self, assign_to_var=True):
##        """Selvar is a tuple set variable."""
##        proj = []
##        sel, pos = self.selvar, self.posvars
##        # For all seq pairs indexed in the upper bound of selvar,
##        # if they cannot appear in the right order, remove the pair from selvar
##        if not sel.is_determined():
##            proj.append(
##                UpperProj(sel,
##                          DiffSetX(self.constx(ConstantSetX, self.maxset),
##                                   MapCond(self.compx(PrecSelectX,
##                                                       self.varx(UpperSetX, sel),
##                                                       tuple([self.varx(LowerSetX, s) for s in pos]),
##                                                       (1, 0), 0),
##                                           2, 0)),
##                          self, recursive=True))
##        ## Each of these, when evaluated, returns a list of tuples of this form:
##        ## (arc_index1, arc_index2), (max/min_of_value1, max/min_of_value2),
##        ## {indices_satisfying_constraint}, (lowercard1, lowercard2)
##        # arg2: all position indices > max of var1-
##        pos_precsel1 = self.compx(PrecSelectX,
##                                   self.varx(LowerSetX, sel),
##                                   tuple([self.varx(LowerSetX, s) for s in pos]),
##                                   (1, 0), 1)
##        # arg2: all position indices < min of var2-
##        pos_precsel2 = self.compx(PrecSelectX,
##                                   self.varx(LowerSetX, sel),
##                                   tuple([self.varx(LowerSetX, s) for s in pos]),
##                                   (1, 0), 2)
##        # arg2: all position indices > min of var1+
##        pos_precsel3 = self.compx(PrecSelectX,
##                                   self.varx(LowerSetX, sel),
##                                   tuple([self.varx(UpperSetX, s) for s in pos]),
##                                   (0, 1), 1)
##        # arg2: all position indices < max of var2+
##        pos_precsel4 = self.compx(PrecSelectX,
##                                   self.varx(LowerSetX, sel),
##                                   tuple([self.varx(UpperSetX, s) for s in pos]),
##                                   (0, 1), 2)
##        for index, p in enumerate(pos):
##            if not p.is_determined():
##                proj.extend([
##                        # For all patterns in pos_precsel1, if arc_index2 matches index,
##                        # intersect indices_satisfying_constraint with the accumulated set,
##                        # that is, discard indices in p that are <= max(var1-)
##                        UpperProj(p, SelectCondX(pos_precsel1, (1, index)), self,
##                                  recursive=True,
##                                  tag=1),
##                        # For all patterns in pos_precsel2, if arc_index1 matches index,
##                        # intersect indices_satisfying_constraint with the accumulated set,
##                        # that is, discard indices in p that are >= min(var2-)
##                        UpperProj(p, SelectCondX(pos_precsel2, (0, index)), self,
##                                  recursive=True,
##                                  tag=2),
##                        # For all patterns in pos_precsel3, if arc_index2 matches index,
##                        # and neither lower cardinality is 0,
##                        # intersect indices_satisfying_constraint with the accumulated set,
##                        # that is, discard indices in p that are <= min(var1+)
##                        UpperProj(p, SelectCondX(pos_precsel3, (1, index), True), self,
##                                  recursive=True,
##                                  tag=3),
##                        # For all patterns in pos_precsel4, if arc_index1 matches index,
##                        # and neither lower cardinality is 0,
##                        # intersect indices_satisfying_constraint with the accumulated set,
##                        # that is, discard indices in p that are >= max(var2+)
##                        UpperProj(p, SelectCondX(pos_precsel4, (0, index), True), self,
##                                  recursive=True,
##                                  tag=4)
##                        ])
##        return proj

    def is_entailed(self, dstore=None):
        """Entailed if all variables are determined or
        if all pairs of indices that *could* be included correspond to
        constraints that are already satisfied.
        """
        if self.selvar.determined(dstore=dstore, constraint=self) is not False \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.posvars]):
            return True
        selupper = self.selvar.get_upper(dstore=dstore)
        for first, second in selupper:
            var1 = self.posvars[first]
            var2 = self.posvars[second]
            if not SetPrecedence.must_precede(var1, var2, dstore=dstore):
                return False
        return True

    def fails(self, dstore=None):
        """Fail if the lower bound of selvar includes pairs representing variables
        that necessarily violate the precedence constraint."""
        sellower = self.selvar.get_lower(dstore=dstore)
        for first, second in sellower:
            # elements in first variable must precede those in second
            # as in SetPrecedence
            var1 = self.posvars[first]
            var2 = self.posvars[second]
            if SetPrecedence.cant_precede(var1, var2, dstore=dstore):
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        state = Constraint.sleeping
        Constraint.infer(self, verbosity=verbosity, tracevar=tracevar)

        ## Constrain the selection variable based on the position variables.
        # For each pair of indices in the sel var's upper bound, check to see
        # whether the corresponding precedence constraint can't succeed
        discard_selup = set()
        strengthen_sellow = set()
        for first, second in self.selvar.get_upper(dstore=dstore):
            var1 = self.posvars[first]
            var2 = self.posvars[second]
            if SetPrecedence.cant_precede(var1, var2, dstore=dstore):
                discard_selup.add((first, second))
        if discard_selup:
            if self.selvar.discard_upper(discard_selup, dstore=dstore,
                                         constraint=(verbosity>1 or self.selvar in tracevar) and self):
                changed.add(self.selvar)
                return state, changed

        ## Constrain the position variables based on the selection variable.
        # For each pair of indices in the sel var's lower bound, check to see
        # whether indices can be excluded from the upper bounds of the corresponding
        # position variables.
        for first, second in self.selvar.get_lower(dstore=dstore):
            v1 = self.posvars[first]
            v2 = self.posvars[second]
            v1_low = v1.get_lower(dstore=dstore)
            v2_low = v2.get_lower(dstore=dstore)
            v1_up = v1.get_upper(dstore=dstore)
            v2_up = v2.get_upper(dstore=dstore)
            # If the lower bound on v1 is not empty, v2 must be a subset of
            # {min(MAX, max(v1 + 1)), ..., MAX}
            if v1_low and v1_up and v2_up:
                v2_up_new = range(min([max(v1_up), max(v1_low) + 1]), max(v2_up)+1)
                if v2.strengthen_upper(v2_up_new, dstore=dstore,
                                       constraint=(verbosity>1 or v2 in tracevar) and self):
                    changed.add(v2)
#                    print('1 Strengthened', v2)
                    return state, changed
            # If the lower bound on v2 is not empty, v1 must be a subset of
            # {0, ..., max(0, min(v2_low) - 1)}
            if v2_low:
                v1_up_new = range(0, max([0, min(v2_low) - 1]) + 1)
                if v1.strengthen_upper(v1_up_new, dstore=dstore,
                                       constraint=(verbosity>1 or v1 in tracevar) and self):
                    changed.add(v1)
#                    print('2 Strengthened', v1)
                    return state, changed
            v1_up = v1.get_upper(dstore=dstore)
            v2_up = v2.get_upper(dstore=dstore)
#            if verbosity>1 or v1 in tracevar:
#                print('v1', v1, 'v2', v2,
#                      'v1_up', v1_up, 'v2_up', v2_up,
#                      'v1_lc', v1.get_lower_card(dstore=dstore),
#                      'v2_lc', v2.get_lower_card(dstore=dstore))
            if v1_up and v2_up and v1.get_lower_card(dstore=dstore) and v2.get_lower_card(dstore=dstore):
                # Eliminate elements of v1 upper that are >= max of v2 upper
                lowenough1 = {x for x in v1_up if x < max(v2_up)}
                if v1.strengthen_upper(lowenough1, dstore=dstore, 
                                       constraint=(verbosity>1 or v1 in tracevar) and self):
                    changed.add(v1)
#                    print('4 Strengthened', v1)
                    return state, changed
                # Eliminate elements of v2 upper that are <= min of v1 upper
                # (v1_up might have changed so assign again and check whether it's empty)
                v1_up = v1.get_upper(dstore=dstore)
                if v1_up:
                    highenough2 = {x for x in v2_up if x > min(v1_up)}
                    if v2.strengthen_upper(highenough2, dstore=dstore, 
                                           constraint=(verbosity>1 or v2 in tracevar) and self):
#                        print('3 Strengthened', v2)
                        changed.add(v2)
                        return state, changed
        return state, changed

class EqualitySelection(Propagator):
    """Elements of main var list are constrained to be equal to elements of seq vars.
    Selection var is a set of pairs: (main_var_index, seq_var_index)

    mainvars: list of IVars
    seqvars: SVars or IVars
    selvar: SVar of (int, int) tuples
    pattern: whether equality should be by pattern matching
    """

    def __init__(self, mainvars=None, selvar=None, seqvars=None,
                 pattern=False,
                 problem=None, principle=None, weight=1,
                 maxset=None, agr_maps=None, rev_agr_maps=None):
        Propagator.__init__(self, mainvars + [selvar] + seqvars, problem=problem,
                            principle=principle, weight=weight)
        self.mainvars = mainvars
        self.selvar = selvar
        self.seqvars = seqvars
        self.pattern = pattern
        # Maximum set of tuples for the particular problem
        self.maxset = maxset or ALL
        # Dictionary for use in CrossAgreement, mapping feature values between languages
        self.agr_maps = agr_maps
        self.rev_agr_maps = rev_agr_maps
        self.name = '{} = {} [{}]'.format(Selection.format_list(self.mainvars),
                                          Selection.format_seq(self.seqvars),
                                          self.selvar)
#        print('Created ES constraint {}'.format(self.name))
#        if self.agr_maps:
#            print('Agr maps: {}'.format(self.agr_maps))

##    def get_projectors(self, assign_to_var=True):
##        """Selvar is a tuple set variable."""
##        proj = []
##        mains, sel, seqs = self.mainvars, self.selvar, self.seqvars
##        # For all seq pairs indexed in the upper bound of selvar,
##        # if they cannot be equal, remove the pair from selvar
##        if not sel.is_determined():
##            proj.append(UpperProj(sel,
##                                  DiffSetX(self.constx(ConstantSetX, self.maxset),
##                                           self.compx(EqSelectX,
##                                                      self.varx(UpperSetX, sel),
##                                                      tuple([self.varx(DomainX, m) for m in mains]),
##                                                      tuple([self.varx(UpperSetX, s) for s in seqs]),
##                                                      False,
##                                                      self.agr_maps)),
##                                  self, recursive=True))
##        # For all main, seq pairs indexed in the lower bound of selvar,
##        # constrain them to be "equal": seq SVar has a single value which
##        # is the value of the corresponding main IVar.
##        # Update the lower bound of each with the lower bound of the other.
##        eqsel = self.compx(EqSelectX,
##                            self.varx(LowerSetX, sel),
##                            tuple([self.varx(DomainX, m) for m in mains]),
##                            tuple([self.varx(UpperSetX, s) for s in seqs]),
##                            True, self.agr_maps)
##        for index, main in enumerate(mains):
##            if not main.is_determined():
##                # mains are always IVars
##                proj.append(IntProj(main,
##                                    EqSelectCondX(eqsel, (0, index), True),
##                                    self, recursive=True))
##                    
##        upeqsel = self.compx(EqSelectX,
##                             self.varx(LowerSetX, sel),
##                             tuple([self.varx(DomainX, m) for m in mains]),
##                             tuple([self.varx(UpperSetX, s) for s in seqs]),
##                             True, self.rev_agr_maps, True)
##        loweqsel = self.compx(EqSelectX,
##                              self.varx(LowerSetX, sel),
##                              tuple([self.varx(LowerSetX, m) for m in mains]),
##                              tuple([self.varx(LowerSetX, s) for s in seqs]),
##                              True, self.rev_agr_maps, True)
##        for index, seq in enumerate(seqs):
##            if not seq.is_determined():
##                if isinstance(seq, IVar):
##                    proj.append(IntProj(seq,
##                                        EqSelectCondX(upeqsel, (1, index), True),
##                                        self, recursive=True))
##                else:
##                    proj.extend([UpperProj(seq,
##                                           EqSelectCondX(upeqsel, (1, index), False),
##                                           self, recursive=True),
##                                 LowerProj(seq,
##                                           EqSelectCondX(loweqsel, (1, index), False),
##                                           self, recursive=True)])
##        return proj

    def is_entailed(self, dstore=None):
        """Entailed if all variables are determined or
        if all pairs of indices that *could* be included correspond to
        constraints that are already satisfied.
        """
        if self.selvar.determined(dstore=dstore, constraint=self) is not False \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.mainvars]) \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.seqvars]):
            return True
        selupper = self.selvar.get_upper(dstore=dstore)
        for mainindex, seqindex in selupper:
            mainvar = self.mainvars[mainindex]
            seqvar = self.seqvars[seqindex]
            # Are mainvar and seqvar not already equal?
            if not mainvar.equals(seqvar, dstore=dstore, pattern=self.pattern):
                return False
        return True

    def get_mapped_feats(self, src_feats, indices, rev=False):
        map = None
        agr_maps = self.rev_agr_maps if rev else self.agr_maps
        for feats, m in agr_maps:
            if indices == feats:
                map = m
                break
        res = set()
        if not map:
#            print('No mapping found for {} | {}'.format(src_feats, indices))
            return res
        for sfeat in src_feats:
            m = set()
            for msfeat, mtfeats in map:
                if sfeat == msfeat:
                    m.update(mtfeats)
            if m:
                res.update(m)
            else:
                # no explicit mapping; just copy the source feature
                res.add(sfeat)
#        print('Mapped feats for {}: {}'.format(src_feats, res))
        return res

    def fails(self, dstore=None):
        """Fail if the lower bound of selvar includes at least one representing an equivalence
        that can't hold."""
        sellower = self.selvar.get_lower(dstore=dstore)
        for mainindex, seqindex in sellower:
            mainvar = self.mainvars[mainindex]
            seqvar = self.seqvars[seqindex]
            mapped = None
            agr_map = self.agr_maps
            if agr_map:
                mapped = self.get_mapped_feats(seqvar.get_upper(dstore=dstore), (seqindex, mainindex))
            if mainvar.cant_equal(seqvar, dstore=dstore, mapped=mapped, pattern=self.pattern):
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        state = Constraint.sleeping
        Constraint.infer(self, verbosity=verbosity, tracevar=tracevar)

        selvar = self.selvar
        mainvars = self.mainvars
        seqvars = self.seqvars

        ## Constrain the selection variable
        sel_discard = set()
        for mainindex, seqindex in selvar.get_upper(dstore=dstore):
            # For each mainvar and seqvar indexed in sel var's upper bound,
            # check to see if they can't be equal
            mapped = None
            agr_map = self.agr_maps
            seqvar = seqvars[seqindex]
            if agr_map:
                mapped = self.get_mapped_feats(seqvar.get_upper(dstore=dstore), (seqindex, mainindex))
            if mainvars[mainindex].cant_equal(seqvar, dstore=dstore, mapped=mapped,
                                              pattern=self.pattern):
                sel_discard.add((mainindex, seqindex))
        if selvar.discard_upper(sel_discard, dstore=dstore,
                                constraint=(verbosity>1 or selvar in tracevar) and self):
            changed.add(selvar)

        ## Constrain the main and/or seq variables
        for mainindex, seqindex in selvar.get_lower(dstore=dstore):
            # For each mainvar and seqvar indexed in sel var's lower bound,
            # attempt to equate them
            mainvar = mainvars[mainindex]
            seqvar = seqvars[seqindex]
            mapped = None
            rev_mapped = None
            agr_map = self.agr_maps
            seqvar = seqvars[seqindex]
            if agr_map:
                mapped = self.get_mapped_feats(seqvar.get_upper(dstore=dstore), (seqindex, mainindex))
                rev_mapped = self.get_mapped_feats(seqvar.get_upper(dstore=dstore), (mainindex, seqindex), True)
            if mainvar.equate(seqvar, dstore=dstore, mapped=mapped, pattern=self.pattern,
                              constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
            if seqvar.equate(mainvar, dstore=dstore, mapped=rev_mapped, pattern=self.pattern,
                             constraint=(verbosity>1 or seqvar in tracevar) and self):
#                print('Changed seqvar', seqvar)
#                if mapped:
#                    print('  mapped', mapped, 'mainvar', mainvar, 'seqvar', seqvar)
#                    print('  revmapped', rev_mapped, 'mainvar', mainvar, 'seqvar', seqvar)
                changed.add(seqvar)

        return state, changed

class SimpleEqualitySelection(Propagator):
    """Selection var is a set of pairs: (seq_var_index, value), where value is a
    tuple of ints. For each indexed seq var in the selection var, the value
    is a set, either the empty set or a single tuple of ints. This value must
    match the value specified in the selection var or be empty."""

    def __init__(self, selvar=None, seqvars=None,
                 pattern=False,
                 problem=None, principle=None, weight=1,
                 maxset=None):
        Propagator.__init__(self, [selvar] + seqvars, problem=problem,
                            principle=principle, weight=weight)
        self.selvar = selvar
        self.seqvars = seqvars
        self.pattern = pattern
        self.maxset = maxset or ALL
        self.name = '= {} [{}]'.format(Selection.format_seq(self.seqvars), self.selvar)

##    def get_projectors(self, assign_to_var=True):
##        """Selvar is a tuple set variable."""
##        proj = []
##        sel, seqs = self.selvar, self.seqvars
##        # For all seq pairs indexed in the upper bound of selvar,
##        # if they cannot contain the value, remove the pair from selvar
##        if not sel.is_determined():
##            proj.append(UpperProj(sel,
##                                  DiffSetX(self.constx(ConstantSetX, self.maxset),
##                                           self.compx(MemSelectX,
##                                                       self.varx(UpperSetX, sel),
##                                                       tuple([self.varx(LowerSetX, s) for s in seqs]),
##                                                       False)),
##                                  self, recursive=True))
##        # For all seq vars indexed in the lower bound of selvar,
##        # remove all but the specified value from their upper bound
##        for index, seq in enumerate(seqs):
##            if not seq.is_determined():
##                proj.append(UpperProj(seq,
##                                      CondX(self.compx(IntersectionSetX, self.constx(ConstantSetX, {index}),
##                                                        self.compx(MapIndexX, self.varx(LowerSetX, sel), 0)),
##                                            self.compx(IndValSelectX, self.varx(LowerSetX, sel), index)),
##                                      self))
###                proj.append(UpperProj(seq,
###                                      SimpEqSelectCondX(eqsel, (0, index)),
###                                      self))
##        return proj

    def is_entailed(self, dstore=None):
        """Entailed if all variables are determined."""
        if self.selvar.determined(dstore=dstore, constraint=self) is not False \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.seqvars]):
            return True
        return False

    def fails(self, dstore=None):
        """Fail if the lower bound of selvar includes at least one representing an equivalence
        that can't hold."""
        sellower = self.selvar.get_lower(dstore=dstore)
        for seqindex, value in sellower:
            seqvar = self.seqvars[seqindex]
#            print('Cant equal value?', seqvar, value)
            if seqvar.cant_equal_value(value, dstore=dstore, pattern=self.pattern):
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        changed = set()
        state = Constraint.sleeping
        Constraint.infer(self, verbosity=verbosity, tracevar=tracevar)

        selvar = self.selvar
        seqvars = self.seqvars

        ## Constrain the selection variable
        sel_discard = set()
        for seqindex, value in selvar.get_upper(dstore=dstore):
            # For each seqvar indexed in sel var's upper bound,
            # check to see if the value is possible
            if seqvars[seqindex].cant_equal_value(value, dstore=dstore, pattern=self.pattern):
                sel_discard.add((seqindex, value))
        if selvar.discard_upper(sel_discard, dstore=dstore,
                                constraint=(verbosity>1 or selvar in tracevar) and self):
            changed.add(selvar)

        ## Constrain seq variables
        for seqindex, value in selvar.get_lower(dstore=dstore):
            # For each seqvar indexed in sel var's lower bound,
            # attempt to equate it with value
            seqvar = seqvars[seqindex]
            # value may be an integer or tuple
            if not isinstance(value, set):
                value = {value}
            seqvar.strengthen_upper(value, dstore=dstore, pattern=self.pattern, 
                                    constraint=(verbosity>1 or seqvar in tracevar) and self)

        return state, changed

### Propagators derived from other Propagators
        
class DerivedConstraint:
    """Abstract class for
    constraints that are equivalent to a conjunction of primitive or derived constraints."""

    def __init__(self, variables, problem=None, propagate=True, principle=None, weight=1):
        self.variables = variables
        self.problem = problem
        self.weight = weight
        self.propagate = propagate
        self.principle = principle
        self.init_constraints()

    def init_constraints(self):
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def set_weight(self, weight):
        self.weight = weight
        for c in self.constraints:
            c.weight = weight

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        for c in self.constraints:
##            proj.extend(c.get_projectors())
##        return proj

#class IntEquality(DerivedConstraint):
#    """IVar equality:
#    I1 <= I2 and I2 <= I1.
#    """
#    def init_constraints(self):
#        self.constraints = [LessThan(self.variables, problem=self.problem,
#                                     weight=self.weight),
#                            LessThan(list(reversed(self.variables)), problem=self.problem,
#                                     weight=self.weight)]

class Inclusion(DerivedConstraint):
    """Set inclusion:
    S1 c= S2: S1 c= S2 U S3 and S3 c= 0
    """

    def init_constraints(self):
        sv3 = EMPTY
        self.constraints = [SubsetUnion(self.variables + [sv3], problem=self.problem, propagate=self.propagate,
                                        principle=self.principle, weight=self.weight)]

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        # Constrain lower bound and lower cardinality of svar2 to be within those of svar1
##        # and upper bound and upper cardinality of svar1 to be within those of svar2
##        if not self.variables[0].is_determined():
##            proj.extend([UpperProj(self.variables[0], self.varx(UpperSetX, self.variables[1]), self),
##                         UCardProj(self.variables[0], self.varx(UpperCardX, self.variables[1]), self)])
##        if not self.variables[1].is_determined():
##            proj.extend([LowerProj(self.variables[1], self.varx(LowerSetX, self.variables[0]), self),
##                         LCardProj(self.variables[1], self.varx(LowerCardX, self.variables[0]), self)])
##        return proj

class Equality(DerivedConstraint):
    """Set equality:
    S1 c= S2 and S2 c= S1.
    """

    def init_constraints(self):
        sv3 = EMPTY
        rev_vars = list(reversed(self.variables))
        self.constraints = [SubsetUnion(self.variables + [sv3], problem=self.problem, propagate=self.propagate,
                                        principle=self.principle, weight=self.weight),
                            SubsetUnion(rev_vars + [sv3], problem=self.problem, propagate=self.propagate,
                                        principle=self.principle, weight=self.weight)]

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        # Mutually constrain lower bounds, lower cardinality, upper bound, upper cardinality
##        # of both variables
##        if not self.variables[0].is_determined():
##            proj.extend([UpperProj(self.variables[0], self.varx(UpperSetX, self.variables[1]), self),
##                         UCardProj(self.variables[0], self.varx(UpperCardX, self.variables[1]), self),
##                         LowerProj(self.variables[0], self.varx(LowerSetX, self.variables[1]), self),
##                         LCardProj(self.variables[0], self.varx(LowerCardX, self.variables[1]), self)])
##        if not self.variables[1].is_determined():
##            proj.extend([UpperProj(self.variables[1], self.varx(UpperSetX, self.variables[0]), self),
##                         UCardProj(self.variables[1], self.varx(UpperCardX, self.variables[0]), self),
##                         LowerProj(self.variables[1], self.varx(LowerSetX, self.variables[0]), self),
##                         LCardProj(self.variables[1], self.varx(LowerCardX, self.variables[0]), self)])
##        return proj

class Disjoint(DerivedConstraint):
    """S1 || S2 || S3...: 0 >= S1 ^ S2 and 0 >= S1 ^ S3 and 0 >= S2 ^ S3...
    The variables must not share any elements.
    """

    def init_constraints(self):
        sv3 = EMPTY
        self.constraints = []
        for i, sv1 in enumerate(self.variables):
            for sv2 in self.variables[i+1:]:
                self.constraints.append(SupersetIntersection([sv3, sv1, sv2], problem=self.problem,
                                                             weight=self.weight))

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        for sv1 in self.variables:
##            if not sv1.is_determined():
##                # Elements that must be in any other variable cannot be in sv1
##                lower_union = self.compx(UnionSetX, *[self.varx(LowerSetX, sv2) for sv2 in self.variables if sv2 != sv1])
##                proj.append(UpperProj(sv1,
##                                      ComplementSetX(lower_union),
##                                      self))
##        return proj

# A dict of DetSVars for different values so these don't get recreated each time
# Union is instantiated
DetSVarD = dict([(n, DetSVar('sel' + str(n), set(range(n)))) for n in range(1, 20)])

class Union(DerivedConstraint):
    """S0 = S1 U S2 U ... :
    S0 = U<S1,...,Sn>[0,...n-1]."""

#    def __repr__():
#        ...

    def init_constraints(self):
        nvar = len(self.variables) - 1
        selvar = DetSVarD.get(nvar) or DetSVar('sel', set(range(nvar)))
        self.constraints = [UnionSelection(self.variables[0], selvar, self.variables[1:],
                                           problem=self.problem,
                                           weight=self.weight)]

##    def get_projectors(self, assign_to_var=True):
##        """Constraints from Duchier, Fig. 15."""
##        proj = []
##        nvar = len(self.variables) - 1
##        sel = DetSVarD.get(nvar) or DetSVar('sel', set(range(nvar)))
##        main, seqs = self.variables[0], self.variables[1:]
##        conds2 = [self.compx(UnionSelectX, self.varx(UpperSetX, sel), tuple([self.varx(UpperSetX, s) for s in seqs]), k)\
##                      for k, s in enumerate(seqs)]
##        conds2 = [DiffSetX(self.varx(LowerSetX, main), c) for c in conds2]
##        if not main.is_determined():
##            proj.extend([UpperProj(main, self.compx(UnionSelectX, self.varx(UpperSetX, sel),
##                                                     tuple([self.varx(UpperSetX, s) for s in seqs])),
##                                   self, upd_reexec_trig={Expr.get_event(sel, card=0, end=1)}),
##                         LowerProj(main, self.compx(UnionSelectX, self.varx(LowerSetX, sel),
##                                                     tuple([self.varx(LowerSetX, s) for s in seqs])),
##                                   self, upd_reexec_trig={Expr.get_event(sel, card=0, end=0)}),
##                         # Lower cardinality of main must be at least max of lower cardinalities of
##                         # required sequence variables (not in Duchier!)
##                         LCardProj(main, SetMaxX(self.compx(ListSelectX,
##                                                             self.varx(LowerSetX, sel),
##                                                             tuple([self.varx(LowerCardX, s) for s in seqs]))),
##                                   self, upd_reexec_trig={Expr.get_event(sel, card=0, end=0)})])
##                         
##        # Lower bound of sel var j >= diff of lower bound of main var and union of upper bounds of all seq vars except j
##        # AND (not in Duchier!)
##        # for all seqs in lower bound of sel var, exclude from upper bound all elements not in upper bound of main var
##        for index, (seq, e) in enumerate(zip(seqs, conds2)):
##            if not seq.is_determined():
##                if isinstance(seq, IVar):
##                    proj.append(IntProj(seq,
##                                        MemCondX(self.varx(LowerSetX, sel), index,
##                                                 ComplementSetX(DiffSetX(self.varx(DomainX, seq),
##                                                                         self.varx(UpperSetX, main)))),
##                                        self, recursive=True,
##                                        upd_reexec_trig={Expr.get_event(sel, card=0, end=0)}))
##                else:
##                    proj.extend([LowerProj(seq, e, self, upd_reexec_trig={Expr.get_event(sel, card=0, end=1)}),
##                                 UpperProj(seq,
##                                           MemCondX(self.varx(LowerSetX, sel), index,
##                                                    ComplementSetX(DiffSetX(self.varx(UpperSetX, seq),
##                                                                            self.varx(UpperSetX, main)))),
##                                           self, recursive=True,
##                                           upd_reexec_trig={Expr.get_event(sel, card=0, end=0)})])
##        return proj

class Intersection(DerivedConstraint):
    """S0 = S1 ^ S2 ^ ... :
    S0 = ^<S1,...,Sn>[0,...n-1]."""

    def init_constraints(self):
        nvar = len(self.variables) - 1
        selvar = DetSVarD.get(nvar) or DetSVar('sel', set(range(nvar)))
        self.constraints = [IntersectionSelection(self.variables[0], selvar, self.variables[1:],
                                                  problem=self.problem,
                                                  weight=self.weight)]

#class Complement(DerivedConstraint):
#    """S0 = ~S1:
#    Disjoint([S0, S1])
#    Union(ALL, S0, S1)
#    ALL is the final argument.
#    """
#    
#    def init_constraints(self):
#        s0 = self.variables[0]
#        s1 = self.variables[1]
#        ALL = self.variables[2]
#        self.constraints = Union([ALL, s0, s1], problem=self.problem, weight=self.weight).constraints
#        self.constraints.extend(Disjoint(self.variables[:2], problem=self.problem, weight=self.weight).constraints)

class Partition(DerivedConstraint):
    """S0 = S1 U+ ... U+ Sn:
    S0 = S1 U ... U Sn and S1 || ... || Sn.
    The first variable is the union of the remaining variables, which must not share any elements.
    """

    def init_constraints(self):
        self.constraints = Union(self.variables, problem=self.problem, weight=self.weight).constraints
        self.constraints.extend(Disjoint(self.variables[1:], problem=self.problem, weight=self.weight).constraints)

##    def get_projectors(self, assign_to_var=True):
##        union = Union(self.variables, problem=self.problem, weight=self.weight)
##        disjoint = Disjoint(self.variables[1:], problem=self.problem, weight=self.weight)
##        return union.get_projectors() + disjoint.get_projectors()

#class MultPrecedence(DerivedConstraint):
#    """S0 << S1 << ... Sn."""
#
#    def init_constraints(self):
#        for (var1, var2) in itertools.combinations(self.variables, 2):
#            # For every pair of variables, var1 before var2 in self.variables,
#            # create a SetPrecedence constraint
#            self.constraints.append(SetPrecedence([var1, var2], problem=self.problem,
#                                                  weight=self.weight))
#
#class SetIntEquiv(DerivedConstraint):
#    """S = {I}: I < S and |S| = I' and I' = 1."""
#
#    def init_constraints(self):
#        i1 = ONE
#        svar = self.variables[0]
#        ivar = self.variables[1]
#        self.constraints = [IVMemberSV([ivar, svar], problem=self.problem,
#                                       weight=self.weight),
#                            CardinalityEq([i1, svar], problem=self.problem,
#                                          weight=self.weight)]

## Propagators behaving in various weird ways

class ReifiedMembership(Propagator):
    """Propagator that has variables I, S, and J and binds J to 1 if I is in S, 0 otherwise."""

    def __init__(self, ivar, svar, truthvar, problem=None, principle=None, weight=1):
        Propagator.__init__(self, [ivar, svar, truthvar], problem=problem,
                            principle=principle, weight=weight)
        self.ivar = ivar
        self.svar = svar
        self.truthvar = truthvar
        self.member_constraint = IVMemberSV([ivar, svar], problem=None, pattern=False, propagate=False,
                                            principle=principle, weight=weight)
        self.name = '?{0} c {1}?'.format(self.ivar, self.svar)

##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        ## Ways to update truthvar
##        if not self.truthvar.is_determined():
##            proj.extend([
##                    # If IVMemberSV constraint fails, that is, if intersection of the upperbound
##                    # of svar and the domain of ivar is empty, then make truthvar 0
##                    IntProj(self.truthvar,
##                            EqCondX(self.compx(IntersectionSetX, self.varx(DomainX, self.ivar),
##                                                self.varx(UpperSetX, self.svar)),
##                                    self.constx(ConstantSetX, set()),
##                                    self.constx(ConstantSetX, {0})),
##                            self),
##                    # If IVMemberSV constraint is entailed, that is, if ivar's domain is a subset
##                    # of svar's lower bound (ivar's domain \ svar's lower bound == {}), then make
##                    # truthvar 1
##                    IntProj(self.truthvar,
##                            EqCondX(DiffSetX(self.varx(DomainX, self.ivar),
##                                             self.varx(LowerSetX, self.svar)),
##                                    self.constx(ConstantSetX, set()),
##                                    self.constx(ConstantSetX, {1})),
##                            self)
##                    ])
##        ## Ways to update ivar (though there may be no cases like this)
##        if not self.ivar.is_determined():
##            proj.extend([
##                    # if truthvar is 1, then IVMemberSV constraint must be satisfied, so update
##                    # ivar's domain to be a subset of svar's upper bound
##                    IntProj(self.ivar,
##                            EqCondX(self.varx(DomainX, self.truthvar),
##                                    self.constx(ConstantSetX, {1}),
##                                    self.varx(UpperSetX, self.svar)),
##                            self),
##                    # if truthvar is 0, then IVMemberSV must fail, so update ivar's domain to
##                    # exclude values that must be in svar's (that is, svar's lower bound)
##                    IntProj(self.ivar,
##                            EqCondX(self.varx(DomainX, self.truthvar),
##                                    self.constx(ConstantSetX, {0}),
##                                    DiffSetX(self.constx(ConstantSetX, ALL),
##                                             self.varx(LowerSetX, self.svar))),
##                            self)
##                    ])
##        ## Ways to update svar
##        if not self.svar.is_determined():
##            proj.extend([
##                    # if truthvar is 1, then IVMemberSV constraint must be satisfied,
##                    #
##                    # ...so if
##                    # ivar is determined, update svar's lower bound to include its value
##                    LowerProj(self.svar,
##                              EqCondX(self.varx(DomainX, self.truthvar),
##                                      self.constx(ConstantSetX, {1}),
##                                      EqCondX(self.varx(SetCardX, self.varx(DomainX, self.ivar)),
##                                              self.constx(ConstantIntX, 1),
##                                              self.varx(DomainX, self.ivar))),
##                              self),
##                    # and if the intersection of ivar's domain and svar's lower bound is
##                    # empty, then svar's lower cardinality must be at least >= 1 +
##                    # length of svar's lower bound
##                    LCardProj(self.svar,
##                              EqCondX(self.varx(DomainX, self.truthvar),
##                                      self.constx(ConstantSetX, {1}),
##                                      CondX(self.compx(IntersectionSetX, self.varx(DomainX, self.ivar),
##                                                        self.varx(LowerSetX, self.svar)),
##                                            SumIntX(self.varx(SetCardX, self.varx(LowerSetX, self.svar)),
##                                                    self.constx(ConstantIntX, 1)),
##                                            False)),
##                              self),
##                    # if truthvar is 0, then IVMemberSV constraint must fail,
##                    # so if ivar is determined, discard its value from svar's upper bound
##                    UpperProj(self.svar,
##                              EqCondX(self.varx(DomainX, self.truthvar),
##                                      self.constx(ConstantSetX, {0}),
##                                      EqCondX(self.varx(SetCardX, self.varx(DomainX, self.ivar)),
##                                              self.constx(ConstantIntX, 1),
##                                              DiffSetX(self.constx(ConstantSetX, ALL),
##                                                       self.varx(DomainX, self.ivar)))),
##                              self)
##                              
##                    ])
##        return proj
        
    def fails(self, dstore=None):
        """Fail if the value of truthvar disagrees with the membership constraint."""
        if self.member_constraint.fails(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 1:
                return True
        elif self.member_constraint.is_entailed(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 0:
                return True
        return False

    def is_entailed(self, dstore=None):
        """Succeed if the value of the truthvar agrees with the membership constraint."""
        if self.member_constraint.fails(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 0:
                return True
        elif self.member_constraint.is_entailed(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 1:
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if self.truthvar.determined(dstore=dstore) is not False:
            if self.truthvar.get_value(dstore=dstore) is 1:
                # Treat membership constraint in the normal way, returning the state
                # and changed variables resulting from inference with it
                return self.member_constraint.infer(dstore=dstore, verbosity=verbosity, tracevar=tracevar)
            else:
                # Make membership constraint fail
                changed = set()
                iv = self.ivar
                sv = self.svar
                # Constrain the values of IV to be outside the lower bound of SV
                if iv.discard_upper(sv.get_lower(dstore=dstore), dstore=dstore,
                                    constraint=(verbosity>1 or iv in tracevar) and self):
                    changed.add(iv)
                # If IV is determined, constrain SV to exclude it
                if iv.determined(dstore=dstore, verbosity=verbosity) is not False:
                    if sv.discard_upper(iv.get_domain(dstore=dstore), dstore=dstore,
                                        constraint=(verbosity>1 or sv in tracevar) and self):
                        changed.add(sv)
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return Constraint.sleeping, changed
        elif self.member_constraint.is_entailed(dstore=dstore):
            # Membership constraint succeeds, so determine truth variable at 1
            tv = self.truthvar
            if tv.determine(1, dstore=dstore,
                            constraint=(verbosity>1 or tv in tracevar) and self):
                return Constraint.sleeping, {tv}
        elif self.member_constraint.fails(dstore=dstore):
            # Membership constraint fails, so determine truth variable at 0
            tv = self.truthvar
            if tv.determine(0, dstore=dstore,
                            constraint=(verbosity>1 or tv in tracevar) and self):
                return Constraint.sleeping, {tv}

        return Constraint.sleeping, set()

class ReifiedInclusion(Propagator):
    """Propagator that has variables S1, S2, and J and binds J to 1 if S1 is included in S2 (and S2 is not empty),
    0 if S1 is not included in S2, and makes no commitment about J if S1 = S2 = {}."""

    def __init__(self, svar1, svar2, truthvar, problem=None, principle=None, weight=1):
        Propagator.__init__(self, [svar1, svar2, truthvar], problem=problem,
                            principle=principle, weight=weight)
        self.svar1 = svar1
        self.svar2 = svar2
        self.truthvar = truthvar
        inclusion_constraint = Inclusion([svar1, svar2], problem=None, propagate=False,
                                         principle=principle, weight=weight)
        self.inclusion_constraint = inclusion_constraint.constraints[0]
        self.name = '?{0} c= {1}?'.format(self.svar1, self.svar2)
        
##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        ## Ways to update truthvar
##        if not self.truthvar.is_determined():
##            proj.extend([
##                    # If Inclusion constraint is entailed, that is, if svar1's upper bound is
##                    # within svar2's lower bound, and svar2 is not empty, 
##                    # then make truthvar 1
##                    IntProj(self.truthvar,
##                            EqCondX(DiffSetX(self.varx(UpperSetX, self.svar1),
##                                             self.varx(LowerSetX, self.svar2)),
##                                    self.constx(ConstantSetX, set()),
##                                    EqCondX(self.varx(LowerSetX, self.svar2),
##                                            self.constx(ConstantSetX, set()),
##                                            self.constx(ConstantSetX, {1}),
##                                            False)),
##                            self),
##                    # If Inclusion constraint fails, that is, if svar1's lower bound includes
##                    # elements not in svar2's upper bound, than make truthvar 0
##                    IntProj(self.truthvar,
##                            CondX(DiffSetX(self.varx(LowerSetX, self.svar1),
##                                           self.varx(UpperSetX, self.svar2)),
##                                  self.constx(ConstantSetX, {0})),
##                            self)
##                    ])
##        ## Ways to update svar1 and svar2
##        if not self.svar1.is_determined():
##            proj.extend([
##                    # If truthvar is 1, make svar1's upper bound a subset of svar2's upper bound
##                    # and make svar1's upper cardinality <= svar2's upper cardinality
##                    UpperProj(self.svar1,
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(UpperSetX, self.svar2)),
##                              self),
##                    UCardProj(self.svar1,
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(UpperCardX, self.svar2)),
##                              self)
##                    ])
##        if not self.svar2.is_determined():
##            proj.extend([
##                    # If truthvar is 1, make svar2's lower bound a superset of svar1's upper bound
##                    # and make svar2's lower cardinality >= svar1's lower cardinality
##                    LowerProj(self.svar2,
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(LowerSetX, self.svar1)),
##                              self),
##                    LCardProj(self.svar2,
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(LowerCardX, self.svar1)),
##                              self)
##                    ])
##        return proj

    def fails(self, dstore=None):
        """Fail if the value of truthvar disagrees with the inclusion constraint."""
        if self.inclusion_constraint.fails(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 1:
                return True
        elif self.inclusion_constraint.is_entailed(dstore=dstore) and self.svar2.get_lower(dstore=dstore):
            # We need to make sure that svar2 is not empty, in which case we don't commit
            if self.truthvar.get_value(dstore=dstore) is 0:
                return True
        return False

    def is_entailed(self, dstore=None):
        """Succeed if the value of the truthvar agrees with the inclusion constraint."""
        if self.inclusion_constraint.fails(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 0:
                return True
        elif self.inclusion_constraint.is_entailed(dstore=dstore) and self.svar2.get_lower(dstore=dstore):
            # We need to make sure that svar2 is not empty, in which case we don't commit
            if self.truthvar.get_value(dstore=dstore) is 1:
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if self.truthvar.determined(dstore=dstore) is not False:
            if self.truthvar.get_value(dstore=dstore) is 1:
                # Treat inclusion constraint in the normal way, returning the state
                # and changed variables resulting from inference with it
                return self.inclusion_constraint.infer(dstore=dstore, verbosity=verbosity, tracevar=tracevar)
#            else:
#                # Make inclusion constraint fail or have both sets empty
#                # How??
#                changed = set()
#                svar1 = self.svar1
#                svar2 = self.svar2
#                # If svar2 can't be empty, then force svar1 to be bigger
#                if svar2.get_lower(dstore=dstore):

        elif self.inclusion_constraint.is_entailed(dstore=dstore) and self.svar2.get_lower(dstore=dstore):
            # Inclusion constraint succeeds and svar2 is not empty, so determine truth variable at 1
            tv = self.truthvar
            if tv.determine(1, dstore=dstore,
                            constraint=(verbosity>1 or tv in tracevar) and self):
                return Constraint.sleeping, {tv}

        elif self.inclusion_constraint.fails(dstore=dstore):
            # Inclusion constraint fails, so determine truth variable at 0
            tv = self.truthvar
            if tv.determine(0, dstore=dstore,
                            constraint=(verbosity>1 or tv in tracevar) and self):
                return Constraint.sleeping, {tv}

        return Constraint.sleeping, set()

class ReifiedEquality(Propagator):
    """Propagator that has variables S1, S2, and J and binds J to 1 if S1 is equal to S2,
    and 0 if S1 is not equal to S2."""

    def __init__(self, svar1, svar2, truthvar, problem=None,
                 principle=None, weight=1):
        Propagator.__init__(self, [svar1, svar2, truthvar], problem=problem,
                            principle=principle, weight=weight)
        self.svar1 = svar1
        self.svar2 = svar2
        self.truthvar = truthvar
        equality_constraint = Equality([svar1, svar2], problem=None, propagate=False,
                                       principle=principle, weight=weight)
        self.eq_constraints = equality_constraint.constraints
        self.name = '?{0} = {1}?'.format(self.svar1, self.svar2)
        
##    def get_projectors(self, assign_to_var=True):
##        proj = []
##        ## Ways to update truthvar
##        if not self.truthvar.is_determined():
##            proj.extend([
##                    # If Equality constraint is entailed, that is, if svar1's upper bound is
##                    # within svar2's lower bound and svar2's upper bound is within svar1's
##                    # lower bound, then make truthvar 1
##                    IntProj(self.truthvar,
##                            EqCondX(DiffSetX(self.varx(UpperSetX, self.svar1),
##                                             self.varx(LowerSetX, self.svar2)),
##                                    self.constx(ConstantSetX, set()),
##                                    EqCondX(DiffSetX(self.varx(UpperSetX, self.svar2),
##                                                     self.varx(LowerSetX, self.svar1)),
##                                            self.constx(ConstantSetX, set()),
##                                            self.constx(ConstantSetX, {1}))),
##                            self),
##                    # If Inclusion constraint fails, that is, if svar1's lower bound includes
##                    # elements not in svar2's upper bound or svar2's lower bound includes
##                    # elements not in svar1's upper bound, than make truthvar 0
##                    IntProj(self.truthvar,
##                            CondX(DiffSetX(self.varx(LowerSetX, self.svar1),
##                                           self.varx(UpperSetX, self.svar2)),
##                                  self.constx(ConstantSetX, {0})),
##                            self),
##                    IntProj(self.truthvar,
##                            CondX(DiffSetX(self.varx(LowerSetX, self.svar2),
##                                           self.varx(UpperSetX, self.svar1)),
##                                  self.constx(ConstantSetX, {0})),
##                            self)
##                    ])
##        ## Ways to update svar1 and svar2
##        if not self.svar1.is_determined():
##            proj.extend([
##                    # If truthvar is 1, constrain svar1's bounds and cardinalities 
##                    # by svar2's bounds and cardinalities
##                    UpperProj(self.variables[0],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(UpperSetX, self.variables[1])),
##                              self),
##                    UCardProj(self.variables[0],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(UpperCardX, self.variables[1])),
##                              self),
##                    LowerProj(self.variables[0],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(LowerSetX, self.variables[1])),
##                              self),
##                    LCardProj(self.variables[0],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(LowerCardX, self.variables[1])),
##                              self)
##                    ])
##        if not self.svar2.is_determined():
##            proj.extend([
##                    # If truthvar is 1, constrain svar2's bounds and cardinalities 
##                    # by svar1's bounds and cardinalities
##                    UpperProj(self.variables[1],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(UpperSetX, self.variables[0])),
##                              self),
##                    UCardProj(self.variables[1],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(UpperCardX, self.variables[0])),
##                              self),
##                    LowerProj(self.variables[1],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(LowerSetX, self.variables[0])),
##                              self),
##                    LCardProj(self.variables[1],
##                              EqCondX(self.varx(DomainX, self.truthvar), self.constx(ConstantSetX, {1}),
##                                      self.varx(LowerCardX, self.variables[0])),
##                              self)
##                    ])
##        return proj

    def fails(self, dstore=None):
        """Fail if the value of truthvar disagrees with the equality constraint."""
        if self.eq_constraints[0].fails(dstore=dstore) or self.eq_constraints[1].fails(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 1:
                return True
        elif self.eq_constraints[0].is_entailed(dstore=dstore) and self.eq_constraints[1].is_entailed(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 0:
                return True
        return False

    def is_entailed(self, dstore=None):
        """Succeed if the value of the truthvar agrees with the equality constraint."""
        if self.eq_constraints[0].fails(dstore=dstore) and self.eq_constraints[1].fails(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 0:
                return True
        elif self.eq_constraints[0].is_entailed(dstore=dstore) and self.eq_constraints[1].is_entailed(dstore=dstore):
            if self.truthvar.get_value(dstore=dstore) is 1:
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if self.truthvar.determined(dstore=dstore) is not False:
            if self.truthvar.get_value(dstore=dstore) is 1:
                # Treat equality constraints in the normal way, returning the state
                # and changed variables resulting from inference with them
                state0, changed0 = self.eq_constraints[0].infer(dstore=dstore, verbosity=verbosity, tracevar=tracevar)
                state1, changed1 = self.eq_constraints[1].infer(dstore=dstore, verbosity=verbosity, tracevar=tracevar)
                if state0 == state1:
                    state = state0
                elif state0 == Constraint.failed or state1 == Constraint.failed:
                    state = Constraint.failed
                else:
                    state = Constraint.sleeping
                changed = changed0 | changed1
                return state, changed
            else:
                # Make inclusion constraint fail or have both sets empty
                # How??
                pass

        elif self.eq_constraints[0].is_entailed(dstore=dstore) and self.eq_constraints[1].is_entailed(dstore=dstore):
            # Equality constraint succeeds, so determine truth variable at 1
            tv = self.truthvar
            if tv.determine(1, dstore=dstore,
                            constraint=(verbosity>1 or tv in tracevar) and self):
                return Constraint.sleeping, {tv}

        elif self.eq_constraints[0].fails(dstore=dstore) and self.eq_constraints[1].fails(dstore=dstore):
            # Equality constraint fails, so determine truth variable at 0
            tv = self.truthvar
            if tv.determine(0, dstore=dstore,
                            constraint=(verbosity>1 or tv in tracevar) and self):
                return Constraint.sleeping, {tv}

        return Constraint.sleeping, set()

class LogPropagator(Propagator):
    """'Logical' propagators: implication, equivalence (maybe others?)."""

    def make_true(self, v, dstore=None, verbosity=0, tracevar=None):
        if isinstance(v, IVar):
            # Remove 0 from v's domain
            if v.discard_value(0, dstore=dstore,
                                constraint=(verbosity>1 or v in tracevar) and self):
                return True
        else:
            # Make sure v has at least element in it
            if v.strengthen_lower_card(1, dstore=dstore,
                                        constraint=(verbosity>1 or v in tracevar) and self):
                return True
        return False

    def make_false(self, v, dstore=None, verbosity=0, tracevar=None):
        if isinstance(v, IVar):
            # Determine v at 0
            if v.determine(0, dstore=dstore,
                            constraint=(verbosity>1 or v in tracevar) and self):
                return True
        else:
            # Determine v at set()
            if v.determine(set(), dstore=dstore,
                            constraint=(verbosity>1 or v in tracevar) and self):
                return True
        return False

class LogEquivalence(LogPropagator):
    """Two set or integer variables; true if both or neither are non-empty or non-zero."""

    def __init__(self, vars, problem=None, principle=None, weight=1):
        Propagator.__init__(self, vars, problem=problem, principle=principle, weight=weight)
        self.name = '{0} <-> {1}'.format(self.variables[0], self.variables[1])

##    def get_projectors(self, assign_to_var=True):
##        # Always an IVar
##        v1 = self.variables[0]
##        # Always an SVar
##        v2 = self.variables[1]
##        proj = []
##        if not v1.is_determined():
##            # Boolean integer variable, either 0 or 1
##            proj.extend([
##                    # If v2 is "true", that is, not {}, make v1 1
##                    # v2's lower bound is not set()
##                    IntProj(v1,
##                            CondX(self.varx(LowerSetX, v2), self.constx(ConstantSetX, {1})),
##                            self),
##                    # v2's lower cardinality >= 0
##                    IntProj(v1,
##                            CondX(DiffIntX(self.varx(LowerCardX, v2), self.constx(ConstantIntX, 1)),
##                                  self.constx(ConstantSetX, {1})),
##                            self),
##                    # If v2 is "false", that is, {}, make v1 0
##                    IntProj(v1,
##                            CondX(self.varx(UpperSetX, v2), self.constx(ConstantSetX, {0}), False),
##                            self)
##                    ])
##        if not v2.is_determined():
##            proj.extend([
##                    # If v1 is "true", that is, 1, make lower cardinality of v1 >= 1
##                    LCardProj(v2,
##                              EqCondX(self.varx(DomainX, v1), self.constx(ConstantSetX, {1}),
##                                      self.constx(ConstantIntX, 1)),
##                              self),
##                    # If v1 is "false", that is, 0, make v2 {}
##                    UpperProj(v2,
##                              EqCondX(self.varx(DomainX, v1), self.constx(ConstantSetX, {0}),
##                                      self.constx(ConstantSetX, set())),
##                              self)
##                    ])
##        return proj

    def fails(self, dstore=None):
        """Fail if one variable is 'true' and the other isn't."""
        v0 = self.variables[0]
        v1 = self.variables[1]
        if v0.is_true(dstore=dstore) and v1.is_false(dstore=dstore):
            return True
        elif v0.is_false(dstore=dstore) and v1.is_true(dstore=dstore):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Succeed if both variables are 'true' or 'false'."""
        v0 = self.variables[0]
        v1 = self.variables[1]
        if v0.is_true(dstore=dstore) and v1.is_true(dstore=dstore):
            return True
        elif v0.is_false(dstore=dstore) and v1.is_false(dstore=dstore):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        changed = set()
        v0 = self.variables[0]
        v1 = self.variables[1]

        if v0.is_true(dstore=dstore):
            if self.make_true(v1, dstore=dstore, verbosity=verbosity, tracevar=tracevar):
                return Constraint.sleeping, {v1}
        elif v0.is_false(dstore=dstore):
            if self.make_false(v1, dstore=dstore, verbosity=verbosity, tracevar=tracevar):
                # Both are determined
                return Constraint.entailed, {v1}

        if v1.is_true(dstore=dstore):
            if self.make_true(v0, dstore=dstore, verbosity=verbosity, tracevar=tracevar):
                return Constraint.sleeping, {v0}
        elif v1.is_false(dstore=dstore):
            if self.make_false(v0, dstore=dstore, verbosity=verbosity, tracevar=tracevar):
                # Both are determined
                return Constraint.entailed, {v0}

        return Constraint.sleeping, set()
                
class LogImplication(LogPropagator):
    """Two set or integer variables:
    v0 -> v1
    false if v0 is non-zero or non-empty and v1 is zero or empty; true otherwise."""

    def __init__(self, vars, problem=None, principle=None, weight=1):
        Propagator.__init__(self, vars, problem=problem, principle=principle, weight=weight)
        self.name = '{0} -> {1}'.format(self.variables[0], self.variables[1])

##    def get_projectors(self, assign_to_var=True):
##        # Always an SVar
##        v0 = self.variables[0]
##        # Always an IVar
##        v1 = self.variables[1]
##        proj = []
##        if not v0.is_determined():
##            proj.extend([
##                    # If v1 is "false", that is, 0, make v0 {}
##                    UpperProj(v0,
##                              EqCondX(self.varx(DomainX, v1), self.constx(ConstantSetX, {0}),
##                                      self.constx(ConstantSetX, set())),
##                              self)
##                    ])
##        if not v1.is_determined():
##            # Boolean integer variable, either 0 or 1
##            proj.extend([
##                    # If v0 is "true", that is, not {}, make v1 1
##                    # v0's lower bound is not set()
##                    IntProj(v1,
##                            CondX(self.varx(LowerSetX, v0), self.constx(ConstantSetX, {1})),
##                            self),
##                    # v0's lower cardinality >= 0
##                    IntProj(v1,
##                            CondX(DiffIntX(self.varx(LowerCardX, v0), self.constx(ConstantIntX, 1)),
##                                  self.constx(ConstantSetX, {1})),
##                            self)
##                    ])
##        return proj

    def fails(self, dstore=None):
        """Fail if v0 is 'true' and v1 is 'false'."""
        v0 = self.variables[0]
        v1 = self.variables[1]
        if v0.is_true(dstore=dstore) and v1.is_false(dstore=dstore):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Succeed unless v0 is 'true' and v1 is 'false'."""
        v0 = self.variables[0]
        v1 = self.variables[1]
        if v0.is_false(dstore=dstore):
            return True
        if v0.is_true(dstore=dstore) and v1.is_true(dstore=dstore):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        Constraint.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        changed = set()
        v0 = self.variables[0]
        v1 = self.variables[1]

        # if v0 is true, v1 must be
        if v0.is_true(dstore=dstore):
            if self.make_true(v1, dstore=dstore, verbosity=verbosity, tracevar=tracevar):
                return Constraint.sleeping, {v1}

        # if v1 is false, v0 must be
        if v1.is_false(dstore=dstore):
            if self.make_false(v0, dstore=dstore, verbosity=verbosity, tracevar=tracevar):
                # Both are determined
                return Constraint.entailed, {v0}

        return Constraint.sleeping, set()
