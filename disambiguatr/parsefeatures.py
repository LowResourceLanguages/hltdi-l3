#!/usr/bin/env python3

"""Interface to get the parse features from a given Spanish sentence, using
FreeLing. Requires that the FreeLing binary analyze is on the current PATH."""

import subprocess

def get_parse_lines(sent):
    with open("testsentence.txt", "w") as outfile:
        print(sent, file=outfile)
    cmd = "analyze -f usefreeling/es.cfg --outf dep < testsentence.txt" 
    output = subprocess.getoutput(cmd)
    return output.splitlines()

def mainverbs_and_dobjs(sent):
    mainverbs = []
    dobjs = []
    lines = get_parse_lines(sent)
    for line in lines:
        line = line.strip()
        if line.startswith("grup-verb/top/("):
            splitted = line.split()
            mainverbs.append(splitted[1])
        elif line.startswith("sn/dobj/("):
            splitted = line.split()
            dobjs.append(splitted[1])
    return mainverbs, dobjs

def main():
    print(mainverbs_and_dobjs("El gatito está comiendo pescado."))

if __name__ == "__main__":
    main()
