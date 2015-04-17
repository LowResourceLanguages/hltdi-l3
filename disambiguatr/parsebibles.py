#!/usr/bin/env python3

"""Routines for dealing with the file format for the bibles we have."""

def loadbible(fn):
    """Given a fn of a text file where each file name is of the form
    [verse id] sentence ...
    produce a dictionary from verse tuples to verses."""
    out = {}
    with open(fn,"r") as infile:
        for line in infile:
            if line.startswith("-- Warning"):
                continue
            try:
                line = line.strip()
                splitted = line.split("] ")
                if len(splitted) != 2:
                    # print("problematic line: ", line)
                    continue
                verseid = tuple(map(int, (splitted[0][1:]).split(",")))
                verseid = verseid[1:] ## skip language id code.
                text = splitted[1]
                out[verseid] = text
            except:
                print(line)
                return
    return out
