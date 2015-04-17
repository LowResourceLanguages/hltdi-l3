#!/usr/bin/env python3

## 2011.03.10
#  -- Added constraint satisfaction tests

import unittest

### Constraint tests
from l3xdg.tests.testconstraints import *

### Constraint satisfaction tests
from l3xdg.tests.testcs import *

### Load and run particular tests
loader = unittest.defaultTestLoader
runner = unittest.TextTestRunner(verbosity=1)

## Projector tests

# All
def projectors():
    print('Running projector tests')
    suite = loader.loadTestsFromTestCase(TestProjectors)
    runner.run(suite)

# Specific

def sprecselect():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.sprecselect'))

def sprecselx():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestExpressions.sprecselx'))

def partition():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.partition'))

def cardselect():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.cardselect'))

def union():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.union'))

def unionx():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestExpressions.unionx'))

def intersection():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.intersection'))

def intersx():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestExpressions.intersx'))

def seqcx():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestExpressions.seqcx'))

def disj_proj():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.disjoint'))

def logeq_proj():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.logeq'))

def reeq_proj():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.reeq'))

def reincl_proj():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.reincl'))

def remem_proj():
    runner.run(loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.remem'))

def IinS_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.IinS')
    runner.run(suite)

def LTset_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.LTSet')
    runner.run(suite)
    
def superinter_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.superinter')
    runner.run(suite)

def subunion_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.subunion')
    runner.run(suite)

def convexity_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.convexity')
    runner.run(suite)

def mult_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.mult')
    runner.run(suite)

def inclusion_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.inclusion')
    runner.run(suite)

def unionselect_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.unionselect')
    runner.run(suite)

def unionselect_proj2():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.unionselect2')
    runner.run(suite)

def intersselect_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.intersselect')
    runner.run(suite)

def intersselect_proj2():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.intersselect2')
    runner.run(suite)

def intselect_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.intselect')
    runner.run(suite)

def precselect_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.precselect')
    runner.run(suite)

def eqselect_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.eqselect')
    runner.run(suite)

def seqselect_proj():
    suite = loader.loadTestsFromName('l3xdg.tests.testconstraints.TestProjectors.seqselect_set')
    runner.run(suite)

## All parsing tests
def parse():
    print('Running all parsing tests')
    suite = loader.loadTestsFromTestCase(ParseTestCase)
    runner.run(suite)

## All translation tests
def translate():
    print('Running all translation tests')
    suite = loader.loadTestsFromTestCase(TranslateTestCase)
    runner.run(suite)

## Tests with particular languages
def parse_en():
    print('Running parsing tests for English')
    en_suite = loader.loadTestsFromName('l3xdg.tests.testcs.ParseTestCase.english')
    runner.run(en_suite)

def parse_qu():
    print('Running parsing tests for Quechua')
    qu_suite = loader.loadTestsFromName('l3xdg.tests.testcs.ParseTestCase.quechua')
    runner.run(qu_suite)

def parse_am():
    print('Running parsing tests for Amharic')
    am_suite = loader.loadTestsFromName('l3xdg.tests.testcs.ParseTestCase.amharic')
    runner.run(am_suite)

def parse_es():
    print('Running parsing tests for Spanish')
    es_suite = loader.loadTestsFromName('l3xdg.tests.testcs.ParseTestCase.spanish')
    runner.run(es_suite)

def trans_enam():
    print('Running English->Amharic translation tests')
    enam_suite = loader.loadTestsFromName('l3xdg.tests.testcs.TranslateTestCase.enam')
    runner.run(enam_suite)
    
def trans_enqu():
    print('Running English->Quechua translation tests')
    enqu_suite = loader.loadTestsFromName('l3xdg.tests.testcs.TranslateTestCase.enqu')
    runner.run(enqu_suite)

def trans_esqu():
    print('Running Spanish->Quechua translation tests')
    esqu_suite = loader.loadTestsFromName('l3xdg.tests.testcs.TranslateTestCase.esqu')
    runner.run(esqu_suite)

if __name__ == "__main__":
    pass
#    unittest.main()

# TODO(alexr): add some more tests.
