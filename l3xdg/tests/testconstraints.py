#!/usr/bin/env python3

#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010 The HLTDI L^3 Team <gasser@cs.indiana.edu>
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

import unittest
from .. constraint import *

### Variables and constraints for a simple parsing problem
### Mary[0] fell[1] .[2]
###
## Arc labels: root, sb, ob

## Variables
# Node 0 (Mary)
root_in0 = SVar('root_in0', set(), set())
root_out0 = SVar('root_out0', set(), set())
sb_in0 = SVar('sb_in0', set(), {1, 2}, 0, 1)
sb_out0 = SVar('sb_out0', set(), set())
ob_in0 = SVar('ob_in0', set(), {1, 2}, 0, 1)
ob_out0 = SVar('ob_out0', set(), set())
# Node 1 (drank)
root_in1 = SVar('root_in1', set(), {0, 2}, 1, 1)
root_out1 = SVar('root_out1', set(), set())
sb_in1 = SVar('sb_in1', set(), set())
sb_out1 = SVar('sb_out1', set(), {0, 2}, 1, 1)
ob_in1 = SVar('ob_in1', set(), set())
ob_out1 = SVar('ob_out1', set(), set())
# Node 2 (.)
root_in3 = SVar('root_in3', set(), set())
root_out3 = SVar('root_out3', set(), {0, 1}, 1, 1)
sb_in3 = SVar('sb_in3', set(), set())
sb_out3 = SVar('sb_out3', set(), set())
ob_in3 = SVar('ob_in3', set(), set())
ob_out3 = SVar('ob_out3', set(), set())
# Det SVars for nodes
sv0 = DetSVar('sv0', {0})
sv1 = DetSVar('sv1', {1})
sv2 = DetSVar('sv2', {2})

MAXTUP = {(1, 3), (3, 0), (5, 4), (2, 1), (5, 6), (6, 2), (1, 6), (5, 1), (2, 5), (0, 3), (4, 0), (1, 2), (2, 0), (6, 3), (1, 5), (3, 6), (0, 4), (5, 3), (4, 1), (6, 4), (3, 2), (2, 6), (5, 0), (4, 5), (6, 0), (1, 4), (2, 3), (4, 2), (1, 0), (6, 5), (3, 5), (0, 1), (4, 6), (5, 2), (6, 1), (3, 1), (0, 2), (0, 6), (4, 3), (0, 5), (3, 4), (2, 4)}

class TestExpressions(unittest.TestCase):

    def show_vars(self, vars):
        print('Variables')
        for v in vars:
            v.pprint()

    def sprecselx(self):
        s0 = SVar('s0', {1}, {1, 2, 3, 4})
        s1 = SVar('s1', {0, 1}, {0, 1, 2, 3, 4})
        s2 = SVar('s2', {3}, {2, 3, 5})
        s3 = SVar('s3', {4, 5}, {4, 5, 6})
        sel = SVar('sel', {0, 2}, {0, 1, 2, 3})
        vars = [sel, s0, s1, s2, s3]
        self.show_vars(vars)
        x = SimplePrecSelectX((UpperSetX(sel), LowerSetX(sel)),
                              [LowerSetX(s) for s in [s0, s1, s2, s3]],
                              [],
                              0)
        print(x)
        print(x.eval())
        for p in [0, 2]:
            y = SimplePrecSelectX((LowerSetX(sel), None),
                                  [UpperSetX(s) for s in [s0, s1, s2, s3]],
                                  [LowerSetX(s) for s in [s0, s1, s2, s3]],
                                  1,
                                  p)
            print(y)
            print(y.eval())
            z = SimplePrecSelectX((LowerSetX(sel), None),
                                  [UpperSetX(s) for s in [s0, s1, s2, s3]],
                                  [LowerSetX(s) for s in [s0, s1, s2, s3]],
                                  2,
                                  p)
            print(z)
            print(z.eval())

    def unionx(self):
        s0 = SVar('s0', {1}, {1, 2, 3})
        s1 = SVar('s1', {3}, {2, 3, 4})
        s2 = SVar('s2', set(), {2, 3, 5})
        s3 = SVar('s3', {4, 5}, {4, 5, 6})
        vars = [s0, s1, s2, s3]
        self.show_vars(vars)
        x = UnionSetX(*[UpperSetX(s) for s in vars])
        print(x)
        print(x.eval())

    def intersx(self):
        s0 = SVar('s0', {1, 3}, {1, 2, 3})
        s1 = SVar('s1', {3}, {2, 3, 4})
        s2 = SVar('s2', {3, 4}, {2, 3, 5})
        s3 = SVar('s3', {3, 4, 5}, {3, 4, 5, 6})
        vars = [s0, s1, s2, s3]
        self.show_vars(vars)
        x = IntersectionSetX(*[LowerSetX(s) for s in vars])
        print(x)
        print(x.eval())

    def seqcx(self):
        sel = SVar('sel', {(0,0), (1,3)}, {(0,0), (1,3), (2,2), (0,2)})
        m0 = SVar('m0', {1}, {1, 2})
        m1 = SVar('m1', set(), {2, 3, 5})
        m2 = SVar('m2', set(), {1, 4})
        self.show_vars([sel, m0, m1, m2])
        x = ComplementSetX(SimpEqSelectX(LowerSetX(sel), 2))
#        x = EqSelectX(UpperSetX(sel),
#                      [LowerSetX(m0), LowerSetX(m1), LowerSetX(m2)],
#                      [],
#                      True)
        print(x)
        print(x.eval())
#        y = EqSelectX(LowerSetX(sel),
#                      [UpperSetX(m0), UpperSetX(m1), UpperSetX(m2)],
#                      [],
#                      True)
#        print(y)
#        print(y.eval())
#        z = EqSelectCondX(y, (0, 0), True)
#        print(z)
#        print(z.eval())

    def eqcx(self):
        sel = SVar('sel', {(0, 0), (0, 2), (2, 2)}, {(0, 0), (1, 2), (2, 2), (0, 2)})
        m0 = SVar('m0', {0}, {0, 1, 2})
        m1 = SVar('m1', {1, 2}, {1, 2, 4})
        m2 = SVar('m2', {2}, {2, 3})
        s0 = SVar('s0', {1}, {1, 2, 3})
        s1 = SVar('s1', {3}, {2, 3, 4})
        s2 = SVar('s2', set(), {2, 3, 5}, 1)
        self.show_vars([sel, m0, m1, m2, s0, s1, s2])
        x = EqSelectX(UpperSetX(sel),
                      [UpperSetX(m0), UpperSetX(m1), UpperSetX(m2)],
                      [UpperSetX(s0), UpperSetX(s1), UpperSetX(s2)],
                      False)
        print(x)
        print(x.eval())
        y = EqSelectX(LowerSetX(sel),
                      [LowerSetX(m0), LowerSetX(m1), LowerSetX(m2)],
                      [LowerSetX(s0), LowerSetX(s1), LowerSetX(s2)],
                      True)
        print(y)
        print(y.eval())
        z = EqSelectCondX(y, (0, 0))
        print(z)
        print(z.eval())
        w = EqSelectCondX(y, (1, 0))
        print(w)
        print(w.eval())
        j = EqSelectCondX(y, (1, 2))
        print(j)
        print(j.eval())
        k = EqSelectCondX(y, (0, 2))
        print(k)
        print(k.eval())

class TestProjectors(unittest.TestCase):

    def partition(self):
        m = SVar('m', {1, 2}, {0, 1, 2, 3, 4, 5})
        s0 = SVar('s0', {0}, {0, 1})
        s1 = SVar('s1', {1}, {0, 1, 2, 3})
        s2 = SVar('s2', {3}, {3, 4})
        s3 = SVar('s3', {4, 5}, {3, 4, 5})
        vars = [m, s0, s1, s2, s3]
        r = Runner(None, Partition(vars))
        r.run(verbosity=1)

    def union(self):
        m = SVar('m', {1, 2}, {0, 1, 2, 3, 4, 5})
        s0 = SVar('s0', {0}, {0, 1})
        s1 = SVar('s1', {1}, {0, 1, 2, 3})
        s2 = SVar('s2', {3}, {3, 4})
        s3 = SVar('s3', {4, 5}, {3, 4, 5})
        vars = [m, s0, s1, s2, s3]
        r = Runner(None, Union(vars))
        r.run(verbosity=1)

    def intersection(self):
        m = SVar('m', {1}, {0, 1, 2, 3})
        s0 = SVar('s0', {0, 5}, {0, 1, 2, 5})
        s1 = SVar('s1', {1, 5}, {0, 1, 2, 3, 5})
        s2 = SVar('s2', {3, 5}, {1, 2, 3, 4, 5})
        s3 = SVar('s3', {4}, {1, 2, 3, 4, 5})
        vars = [m, s0, s1, s2, s3]
        r = Runner(None, Intersection(vars))
        r.run(verbosity=1)

    def disjoint(self):
        s0 = SVar('s0', {0}, {0, 1, 2})
        s1 = SVar('s1', {1, 2}, {0, 1, 2, 3})
        s2 = SVar('s2', {3}, {2, 3, 4})
        s3 = SVar('s3', {4, 5}, {3, 4, 5})
        vars = [s0, s1, s2, s3]
        r = Runner(None, Disjoint(vars))
        r.run(verbosity=1)

    def logeq(self):
        i = IVar('i', {0})
        s = SVar('s', set(), {1, 2})
        vars = [i, s]
        r = Runner(None, LogEquivalence(vars))
        r.run(verbosity=1)

    def reeq(self):
        s1 = SVar('s1', {2, 3}, {2, 3})
        s2 = SVar('s2', {2, 3}, {2, 3})
        t = IVar('t', {0, 1})
        r = Runner(None, ReifiedEquality(s1, s2, t))
        r.run(verbosity=1)

    def reincl(self):
        s1 = SVar('s1', {2, 3}, {2, 3, 4, 5}, 2, 4)
        s2 = SVar('s2', {2}, {2, 3, 4}, 1, 2)
        t = IVar('t', {1})
        r = Runner(None, ReifiedInclusion(s1, s2, t))
        r.run(verbosity=1)

    def remem(self):
        i = IVar('i', {3})
        s = SVar('s', {1, 2}, {1, 2, 3, 4, 5})
        t = IVar('t', {0})
        r = Runner(None, ReifiedMembership(i, s, t))
        r.run(verbosity=1)

    def cardselect(self):
        main = SVar('main', {2, 4}, {2, 3, 4, 5, 6})
        c0 = DetIVar('c0', 1)
        c1 = DetIVar('c1', 5)
        c2 = DetIVar('c2', 2)
        c3 = DetIVar('c3', 6)
        sel = IVar('sel', {0, 1, 2})
        C0 = DetIVar('C0', 2)
        C1 = DetIVar('C1', 3)
        C2 = DetIVar('C2', 1)
        r = Runner(None, CardSelection(main, sel, [c0, c1, c2, c3],
                                       lower=True),
                   CardSelection(main, sel, [C0, C1, C2],
                                 lower=False))
        r.run(verbosity=1)

    def intselect(self):
        main = SVar('main', {2, 4}, {2, 3, 4})
        sel = IVar('sel', {0, 1, 2, 3})
        s0 = SVar('s0', {1}, {1, 2})
        s1 = SVar('s1', {2, 4}, {1, 2, 4})
        s2 = SVar('s2', {3}, {3, 4})
        r = Runner(None, IntSelection(main, sel, [s0, s1, s2]))
        r.run(verbosity=1)

    def seqselect_int(self):
        sel = SVar('sel', {(0, 0), (2, 2)}, {(0, 0), (1, 2), (2, 2), (0, 2)})
        s0 = IVar('s0', {0, 1, 2})
        s1 = IVar('s1', {1, 4})
        s2 = IVar('s2', {2, 3, 5})
        s2 = SVar('s2', set(), {1, 4})
        r = Runner(None, SimpleEqualitySelection(selvar=sel,
                                                 seqvars=[s0, s1, s2],
                                                 maxset={(0, 0), (1, 2), (2, 2), (0, 2)}))
        r.run(verbosity=1)

    def seqselect_set(self):
        sel = SVar('sel', {(0,(0,)), (1,(3,))}, {(0,(0,)), (1,(3,)), (2,(2,)), (0,(2,))})
        s0 = SVar('s0', {(0,)}, {(1,), (2,)})
        s1 = SVar('s1', set(), {(2,), (3,), (5,)})
        s2 = SVar('s2', {(1,)}, {(1,), (2,), (4,)})
        r = Runner(None, SimpleEqualitySelection(selvar=sel,
                                                 seqvars=[s0, s1, s2],
                                                 maxset={(0,(0,)), (1,(3,)), (2,(2,)), (0,(2,))}))
        r.run(verbosity=0)

    def eqselect(self):
        sel = SVar('sel', {(0, 0), (2, 2)}, {(0, 0), (1, 2), (2, 2), (0, 2)})
        m0 = SVar('m0', {0}, {0, 1, 2, 3})
        m1 = SVar('m1', {1, 2}, {1, 2, 4})
        m2 = SVar('m2', {2}, {2, 3})
        s0 = SVar('s0', {1}, {0, 1, 2, 3})
        s1 = SVar('s1', {3}, {2, 3, 4})
        s2 = SVar('s2', set(), {0, 2, 3, 5}, 1)
        r = Runner(None, EqualitySelection(selvar=sel,
                                           mainvars=[m0, m1, m2],
                                           seqvars=[s0, s1, s2],
                                           maxset={(0, 0), (1, 2), (2, 2), (0, 2)}))
        r.run(verbosity=1)

    def sprecselect(self):
        s0 = SVar('s0', {1}, {1, 2, 3, 4})
        s1 = SVar('s1', {0, 1}, {0, 1, 2, 3, 4})
        s2 = SVar('s2', {3, 4}, {2, 3, 4, 5})
        s3 = SVar('s3', {4, 5}, {1, 4, 5, 6})
        sel = SVar('sel', {0, 3}, {0, 1, 2, 3})
        r = Runner(None, SimplePrecedenceSelection(sel, [s0, s1, s2, s3]))
        r.run(verbosity=1)

    def precselect(self):
        sel = SVar('sel', {(0, 1), (1, 2)}, {(0, 1), (1, 2), (1, 3), (2, 3)})
        s0 = SVar('s0', {1}, {1, 2})
        s1 = SVar('s1', set(), {2, 3, 4, 5}, 1)
        s2 = SVar('s2', set(), {2, 3, 4}, 1)
        s3 = SVar('s3', {3}, {3, 4, 5})
        r = Runner(None, PrecedenceSelection(sel, [s0, s1, s2, s3],
                                             maxset=MAXTUP))
        r.run(verbosity=1)

    def IinS(self):
        i = IVar('i', {1, 3})
        s = SVar('s', {0, 2, 3}, {0, 1, 2, 3, 4})
        vars = [i, s]
        r = Runner(None, IVMemberSV(vars))
        r.run(verbosity=1)

    def LT(self):
        i0 = IVar('i0', {1, 2, 3, 4, 5})
        i1 = IVar('i1', {0, 2, 3, 4})
        r = Runner(None, LessThan([i0, i1]))
        r.run(verbosity=1)

    def LTSet(self):
        s0 = SVar('s0', {1, 2}, {1, 2, 3, 4, 5})
        s1 = SVar('s1', {2, 4}, {0, 2, 3, 4})
        vars = [s0, s1]
        r = Runner(None, SetPrecedence(vars))
        r.run(verbosity=1)

    def unionselect(self):
        main = SVar('main', {2, 4}, {2, 3, 4})
        sel = SVar('sel', set(), {0, 1, 2, 3})
        s0 = SVar('s0', {1}, {1, 2})
        s1 = SVar('s1', {2}, {1, 2})
        s2 = SVar('s2', {3}, {3, 4})
        r = Runner(None, UnionSelection(main, sel, [s0, s1, s2]))
        r.run(verbosity=1)

    def unionselect2(self):
        main = SVar('main', {2, 4}, {2, 3, 4})
        sel = SVar('sel', {0, 1}, {0, 1, 2})
        s0 = SVar('s0', {2}, {1, 2, 5})
        s1 = SVar('s1', {4}, {1, 2, 4, 6})
        s2 = SVar('s2', {3}, {3, 4})
        r = Runner(None, UnionSelection(main, sel, [s0, s1, s2]))
        r.run(verbosity=1)

    def intersselect(self):
        main = SVar('main', {2}, {1, 2, 3})
        sel = SVar('sel', {0, 1, 2}, {0, 1, 2, 3})
        s0 = SVar('s0', {1, 5}, {1, 2, 5})
        s1 = SVar('s1', {1, 2, 5}, {1, 2, 5})
        s2 = SVar('s2', {1, 3}, {1, 2, 3, 4, 5})
        s3 = SVar('s3', {5}, {5, 6})
        r = Runner(None, IntersectionSelection(main, sel, [s0, s1, s2, s3]))
        r.run(verbosity=1)

    def inclusion(self):
        s1 = SVar('s1', {2}, {1, 2, 3})
        s2 = SVar('s2', {1, 4}, {1, 2, 4, 5})
        s3 = SVar('s3', {3}, {2, 3, 7})
        r = Runner(None,
                   Inclusion([s1, s2]),
                   Inclusion([s1, s3]))
        r.run(verbosity=1)

    def mult(self):
        # Example from Müller, 12.4
        s1 = SVar('s1', {2}, {1, 2, 3})
        s2 = SVar('s2', {1, 4}, {1, 2, 4, 5})
        s3 = SVar('s3', {3}, {2, 3, 7})
        vars = [s1, s2, s3]
        r = Runner(None,
                   SupersetIntersection(vars),
                   Inclusion([s1, s2]),
                   Inclusion([s1, s3]))
        r.run(verbosity=1)

    def convexity(self):
        print('\nTesting Convexity')
        var = SVar('s1', {1, 3, 5}, {1, 2, 3, 4, 5, 6, 7, 8})
        r = Runner(None, SetConvexity(var))
        r.run(verbosity=1)

    def superinter(self):
        # Two determined variables
        print('\nTesting SupersetIntersection')
        vars = [DetSVar('s1', {1, 2, 3}),
                DetSVar('s2', {0, 1, 2, 3}),
                SVar('s3', {2, 4}, {0, 2, 3, 4})]
        r = Runner(None, SupersetIntersection(vars))
        r.run(verbosity=1)

    def subunion(self):
        print('\nTesting SubsetUnion')
        vars = [SVar('s1', {1, 2, 4}, {1, 2, 3, 4, 7}),
                SVar('s2', {2, 3}, {0, 1, 2, 3}),
                SVar('s3', {2, 3}, {2, 3, 4, 5})]
        r = Runner(None, SubsetUnion(vars))
        r.run(verbosity=1)

    def member(self):
        print('\nTesting Member')
        r = Runner(None, Member(iv1, {2}))
        r.run(verbosity=1)

    def superset(self):
        print('\nTesting Superset')
        r = Runner(None, Superset(s1, {1, 2, 3}))
        r.run(verbosity=1)

    def subset(self):
        print('\nTesting Subset')
        r = Runner(None, Subset(s1, {1, 2, 3}))
        r.run(verbosity=1)

    def card_geq(self):
        print('\nTesting CardinalityGEQ')
        r = Runner(None, CardinalityGEQ(s2, 10))
        r.run(verbosity=1)

class TestConstraints(unittest.TestCase):

    def supersetintersection(self):
        ssi1 = SupersetIntersection((s0, s2, s3))
        ssi2 = SupersetIntersection((s5, s14, s13))
        ssi3 = SupersetIntersection((s2, s1, s0))
        ssi4 = SupersetIntersection((s17, s18, s19))
        ssi5 = SupersetIntersection((s17, s20, s19))
        ssi6 = SupersetIntersection((s17, s19, s20))

    def unionselection(self):
        ## fails
        us1 = UnionSelection(s3, s4, [s2, s5, s8, s12])
        self.assertTrue(us1.fails())

        ## entailed
        us2 = UnionSelection(s16, s10, [s8, s15, s9])
        # need to fix this; supposed to be entailed?
        ## self.assertTrue(us2.is_entailed())

        ## a good one, results in narrowing of main var
        us3 = UnionSelection(s0, s9, [s12, s13, s14, s15, s16])
        ## a good one, results in narrowing of main and elimination of all
        ## but s15 from the seq vars
        us4 = UnionSelection(s3, s1, [s12, s13, s14, s15, s16])

        S1 = UnionSelection(SVar('main1', {1, 2}, {1, 2, 3, 4, 5}),
                            SVar('sel1', {0, 1}, {0, 1, 2, 3, 4}),
                            [SVar('seq1', {1}, {1, 2}),
                             SVar('seq2', {2}, {1, 2, 3}),
                             SVar('seq3', {3}, {2, 3, 4}),
                             SVar('seq4', {1, 4}, {1, 4, 5}),
                             SVar('seq5', {1, 3, 5}, {1, 2, 3, 5})])

    def cardinality(self):
        # c1 = Cardinality((iv4, sv3))
        c2 = SetPrecedence((sv4, sv5))
        c3 = SetConvexity(sv6)
        c4 = SetConvexity(sv3)

    def intersectionselection(self):
        S1 = IntersectionSelection(SVar('main1', {1}, {1, 2, 3, 4, 5}),
                                   SVar('sel1', {0, 1}, {0, 1, 2, 3, 4}),
                                   [SVar('seq1', {1}, {1, 2}),
                                    SVar('seq2', {1, 2}, {1, 2, 3}),
                                    SVar('seq3', {1, 3}, {1, 2, 3, 4}),
                                    SVar('seq4', {1, 4}, {1, 4, 5}),
                                    SVar('seq5', {1, 3, 5}, {1, 2, 3, 5})])

    def intersection(self):
        S2 = Intersection([SVar('s1', {2}, {1, 2, 3, 4}),
                       SVar('s2', {2, 3}, {2, 3, 4, 5}),
                       SVar('s3', {2, 3, 4}, {2, 3, 4, 5, 6}),
                       SVar('s4', {1, 2, 3}, {1, 2, 3, 4})])

    def childmother(self):
        ### CHILD - MOTHER CONSTRAINT
        C1 = SVar('c1', set(), {2, 3, 4, 5})
        M2 = SVar('m2', set(), {3, 4, 5})
        
        CI = SVar('ci', set(), {1, 2, 3, 4, 5})
        SI = SVar('si', set(), {1, 2, 3, 4, 5})
        
        I1 = Intersection([CI, C1, DetSVar('2d', {2})])
        I2 = Intersection([SI, M2, DetSVar('1d', {1})])

    def union(self):
        U0 = SVar('u0', set(), {1, 2, 3, 4, 5})
        CI = SVar('ci', set(), {1, 2, 3, 4, 5})
        SI = SVar('si', set(), {1, 2, 3, 4, 5})

        U1 = Union([U0, CI, SI])
        V0 = EMPTY
        V1 = DetSVar('1,2', {1, 2})
        ## where'd Choice go?
        # S0 = Choice(U0, [V0, V1])

    def precedenceselection(self):
        # testing PrecedenceSelection
        sv0 = SVar('s0', {0, 1, 2}, {0, 1, 2, 3})
        sv1 = SVar('s1', {2, 3}, {2, 3, 4, 5})
        sv2 = SVar('s2', {0}, {0, 1, 2})
        sv3 = SVar('s3', {3, 4}, {3, 4, 5})
        sel1 = SVar('sel', set(), {(0, 1), (2, 3)})
        p1 = PrecedenceSelection(sel1, [sv0, sv1, sv2, sv3])

    def inequalities(self):
        iv1 = IVar('iv1', {1, 2, 3})
        iv2 = IVar('iv2', {2, 3, 4})
        iv3 = IVar('iv3', {3, 5, 7})
        iv4 = IVar('iv4', {1, 2, 4})
        iv5 = IVar('iv5', {4, 6, 8})
        lt1 = LessThan([iv1, iv2])
        lt2 = LessThan([iv1, iv5])
        lt3 = LessThan([iv5, iv1])
        ie1 = IntEquality([iv1, iv2])
        ie2 = IntEquality([iv1, iv3])

    def setconvexity(self):
        sv0 = SVar('s0', {3, 4}, {2, 3, 4, 5})
        c1 = SetConvexity(sv0)

    def setunionselection_ivar(self):
        ## testing UnionSelection with IVar seq vars
        iv0 = IVar('i0', {(0, 1)})
        iv1 = IVar('i1', {(0, 1), (3, 4), (4, 5)})
        iv2 = IVar('i2', {(3, 5), (0, 1)})
        iv3 = IVar('i3', {(2, 3), (0, 1)})
        sel = SVar('sel', {0, 2}, {0, 1, 2, 3})
        mv = SVar('mv', set(), {(0, 1), (2, 3), (3, 4), (4, 5)}, 1, 1)
        u1 = UnionSelection(mv, sel, [iv0, iv1, iv2, iv3])

    def equalityselection(self):
        ## testing EqualitySelection
        m0 = IVar('m0', {(0, 1), (2, 3), (2, 1)})
        m1 = IVar('m1', {(0, 1), (2, 1)})
        m2 = IVar('m2', {(2, 2), (2, 3)})
        s0 = SVar('s0', set(), {(0, 1), (1, 0)}, 1, 1)
        s1 = SVar('s1', {(2, 4)}, {(2, 4), (2, 1)}, 1, 1)
        sel = SVar('sel', {(0, 0)}, {(0, 0), (2, 1)})
        e1 = EqualitySelection([m0, m1, m2], sel, [s0, s1])

    def simpleprecedence(self):
        # testing SimplePrecedenceSelection
        sv0 = SVar('sv0', {0, 1}, {0, 1, 2})
        sv1 = SVar('sv1', {2, 3}, {2, 3, 4})
        sv2 = SVar('sv2', {4, 5}, {4, 5, 6})
        sv3 = SVar('sv3', {4, 7, 8},  {4, 7, 8, 9})
        sel = SVar('sel', {0, 1, 2}, {0, 1, 2, 3})
        p1 = SimplePrecedenceSelection(sel, [sv0, sv1, sv2, sv3])

    def reifiedmembership(self):
        # testing ReifiedMembership
        i0 = IVar('i0', {0, 1})
        i2 = IVar('i2', {2, 3, 4, 5})
        s0 = SVar('s0', {0, 1}, {0, 1, 2, 3, 4})
        s1 = SVar('s1', {0, 1, 2, 3}, {0, 1, 2, 3, 4})
        s3 = SVar('s3', {2, 3}, {2, 3, 4})
        tt = IVar('tt', {0, 1})
        t0 = IVar('t0', {0})
        t1 = IVar('t1', {1})
        r1 = ReifiedMembership(i0, s0, tt)
        r2 = ReifiedMembership(i0, s3, tt)
        r3 = ReifiedMembership(i0, s3, t0)
        r4 = ReifiedMembership(i0, s3, t1)
        r5 = ReifiedMembership(i2, s3, t0)
        r6 = ReifiedMembership(i2, s1, t1)

    def logequivalence(self):
        # testing LogEquivalence
        i1 = IVar('i1', {0, 1, 2})
        i2 = IVar('i2', {0})
        i4 = IVar('i4', {1, 2})
        s1 = SVar('s1', set(), {0, 1, 2})
        s2 = SVar('s2', {0}, {0, 1, 2})
        s3 = DetSVar('s3', {0})
        s4 = DetSVar('s4', set())
        l1 = LogEquivalence([i1, i2])
        l2 = LogEquivalence([i1, s1])
        l3 = LogEquivalence([i2, s2])
        l4 = LogEquivalence([i4, s3])
        l5 = LogEquivalence([i4, s4])

    def reifiedinclusion(self):
        s0 = SVar('s0', {0, 1}, {0, 1, 2, 3, 4})
        s1 = SVar('s1', {0, 1, 2, 3}, {0, 1, 2, 3, 4})
        s2 = SVar('s2', {2, 3}, {2, 3, 4})
        tt = IVar('tt', {0, 1})
        t0 = IVar('t0', {0})
        t1 = IVar('t1', {1})
        r1 = ReifiedInclusion(s1, s0, tt)
        r2 = ReifiedInclusion(s0, s1, tt)
        r4 = ReifiedInclusion(s2, s0, t0)

    def logimplication(self):
        # testing LogImplication
        i1 = IVar('i1', {0, 1, 2})
        i2 = IVar('i2', {0})
        i4 = IVar('i4', {1, 2})
        s1 = SVar('s1', set(), {0, 1, 2})
        s2 = SVar('s2', {0}, {0, 1, 2})
        s3 = DetSVar('s3', {0})
        s4 = DetSVar('s4', set())
        l1 = LogImplication([i1, i2])
        l2 = LogImplication([i1, s1])
        l3 = LogImplication([i2, s2])
        l4 = LogImplication([i4, s3])
        l5 = LogImplication([i4, s4])

    def reifiedequality(self):
        s1 = SVar('s1', {0, 1, 2, 3}, {0, 1, 2, 3, 4})
        s2 = SVar('s2', {2}, {2, 3})
        s3 = SVar('s3', {2, 3}, {2, 3, 4})
        tt = IVar('tt', {0, 1})
        t0 = IVar('t0', {0})
        t1 = IVar('t1', {1})
        r1 = ReifiedEquality(s1, s2, tt)
        r2 = ReifiedEquality(s2, s3, tt)
        r3 = ReifiedEquality(s1, s3, t0)
        r4 = ReifiedEquality(s2, s3, t1)

