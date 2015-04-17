#!/usr/bin/env python3

class Instance:
    """One item that we want to classify. Knows its label (the output Quechua
    word), the input Spanish text, and the relevant Spanish word."""

    def __init__(self, d):
        """Input variable d should have the keys "S", "s", and "q". """
        self.text = d['S'] ## text in Spanish
        self.sw = d['s'] ## source Spanish word
        self.qw = d['q'] ## target Quechua word, ie instance label.
        self.inflected_sw = d['inflected_sw']
        self.cl = self.qw ## sloppy, but we also sometimes want to call it .cl
        self.mainverbs = d['mainverbs'].split()
        self.dobjs = d['dobjs'].split() ## just in case there's more than one.
