#!/usr/bin/env python3

class Learner:
    """Abstract class; the other learning algorithms should extend this one."""
    def __init__(self, xs):
        """Takes a list of Instance objects for training."""
        raise NotImplementedError

    def __call__(self, x):
        """Having trained during initialization, return the argument's
        predicted class."""
        raise NotImplementedError

    @staticmethod
    def Initialize():
        pass
