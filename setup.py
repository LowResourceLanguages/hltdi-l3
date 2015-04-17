#!/usr/bin/env python

import sys

from distutils.core import setup

setup(name='L3XDG',
      version='0.9',
      description='L3 implementation of XDG',
      author='Michael Gasser',
      author_email='gasser@cs.indiana.edu',
      url='http://www.cs.indiana.edu/~gasser/Research/software.html',
      license="GPL v3",
      packages=['l3xdg', 'l3xdg.morphology', 'l3xdg.morphology.geez',
                'l3xdg.languages',
                'l3xdg.languages.am',
                'l3xdg.languages.en'],
      package_data = {'l3xdg': ['languages/*.yaml',
                                'languages/en/*.yaml',
                                'languages/am/*.yaml',
                                'languages/am/FST/*.fst',
                                'languages/am/FST/*.lex',
                                'languages/am/FST/*.cas'],
                      'l3xdg.morphology.geez': ['*.txt']
                      }
     )
