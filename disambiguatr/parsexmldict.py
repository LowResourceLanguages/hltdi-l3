#!/usr/bin/env python3

## At least on my Ubuntu, to get lxml, I went:
## sudo apt-get install libxml2-dev libxslt1-dev
## sudo easy_install3 lxml
## ... although on very recent Ubuntus, it's available in the regular package
## manager as: python3-lxml
from lxml import etree
from collections import defaultdict

## xpath expression that means: from this entry node, get the citations with
## the language es, and then the quote node underneath that.
xpath_expr = "cit[@{http://www.w3.org/XML/1998/namespace}lang='es']/quote"

def runasimi_xml():
    """Go through the runasimi.de XML dictionary and return two things:
    a set of all of the Quechua "target" adjectives and a
    dictionary from Spanish words to lists of Quechua target adjectives."""

    quechua_targets = set()
    mapping = {}

    tree = etree.parse("dictionaries/runasimi.xml")
    root = tree.getroot()
    poses = root.findall(".//pos")

    adjentries = [pos.getparent().getparent()
                  for pos in poses if pos.text == "adj."]

    es_qu = defaultdict(lambda:set())
    
    for entry in adjentries:
        qw = entry.find("form").find("orth").text
        # skip entries with spaces in them.
        if " " in qw: continue
        spanish = entry.find(xpath_expr).text
        splitted = [word.strip() for word in spanish.split(";")]

        for sw in splitted:
            if " " not in sw:
                if "," in sw:
                    sw = sw.split(",")[0]
                es_qu[sw].add(qw)

    for sw in es_qu.keys():
        ## If there's more than one Quechua word for this Spanish word...
        if len(es_qu[sw]) > 1:
            mapping[sw] = es_qu[sw]
            for qw in es_qu[sw]:
                quechua_targets.add(qw)
    return quechua_targets, mapping
