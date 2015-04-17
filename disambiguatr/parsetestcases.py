#!/usr/bin/env python3

"""
Code to parse the files in testcases/
"""

import os
import glob

def parse(fn):
    """Returns a list of dictionaries. each entry in the list is of the form
    {'S': spanishtext, 'Q': quechuatext, 'sw': sw, 'qw': qw}
    """
    out = []
    with open(fn, "r") as infile:
        for line in infile:
            line = line.strip()
            if line == 'testcase':
                d = {}
            if ":" in line:
                 splitted = line.split(":", 1)
                 key = splitted[0].strip()
                 value = splitted[1].strip()
                 d[key] = value
            if line == "endtestcase":
                out.append(d)
    return out

def main():
    print(parse("testcases/alto"))

if __name__ == "__main__": main()
