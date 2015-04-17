#   
#   Hiiktuu features (dicts).
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2014, HLTDI <gasser@cs.indiana.edu>
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
# =========================================================================

# 2014.04.19
# -- Created.
# 2014.04.23-24
# -- Unification with one or both values sets.
#    Unification with a list/tuple of feature-value pairs.
#    Copying of agreement features: agree:().
# 2014.05.05
# -- More methods for agreement, needed in AgrSelection constraint.
# 2014.05.18
# -- mutual_agree() makes two Features agree with one another on
#    feature pairs.

import re

class Features(dict):

    def __init__(self, dct):
        dict.__init__(self, dct)

    def __repr__(self):
        l = []
        for f, v in self.items():
            l.append("{}={}".format(f, v))
        return "@{{{0}}}".format(','.join(l))

    def to_list(self):
        """Convert features dict to a sorted list."""
        l = list(self.items())
        l.sort()
        return l

    @staticmethod
    def from_string(string):
        """Convert a string representation of a FeatStruct (from L3Morpho) to
        a Features object."""
        d = PARSER.parse(string)
        return Features(d)

    @staticmethod
    def unify_sets(x, y):
        """If both are sets, their intersection. If one is a set,
        the other if it's a member of the set."""
        if isinstance(x, set):
            if isinstance(y, set):
                return x & y
            elif y in x:
                return y
        elif isinstance(y, set):
            if x in y:
                return x
        return False

    @staticmethod
    def simple_unify(x, y):
        """Unify the values x and y, returning the result or 'fail'."""
        # If they're the same, return one.
        if x == y:
            return x
        # If one or the other is a set, return the intersection
        # (a single value if one is not a set)
        elif isinstance(x, set) or isinstance(y, set):
            u = Features.unify_sets(x, y)
            if u is not False:
                return u
            else:
                return 'fail'
#        # If both are dicts, call unify_dict
#        elif isinstance(x, dict) and isinstance(y, dict):
#            x.unify(y)
        # Otherwise fail
        else:
            return 'fail'

    def unify(self, other):
        """other is a Features object or a dict. Attempt to unify self with other,
        returning the result or 'fail'."""
        result = Features({})
        for k in set(self.keys()) | set(other.keys()):
            # Check all of the keys of self and other
            self_val, other_val = self.get(k, 'nil'), other.get(k, 'nil')
            if self_val != 'nil':
                if other_val != 'nil':
                    # If x and y both have a value for k, try to unify the values
                    u = Features.simple_unify(self_val, other_val)
                    if u == 'fail':
                        return 'fail'
                    else:
                        result[k] = u
                else:
                    # If self has a value for k but other doesn't, use self's value
                    result[k] = self_val
            elif other_val != 'nil':
                # If other has a value for k but self doesn't, use other's value
                result[k] = other_val

        return result

    def agree(self, target, agrs):
        """Make target agree with self on features specified in agrs dict or list of pairs."""
        agr_pairs = agrs.items() if isinstance(agrs, dict) else agrs
        for src_feat, targ_feat in agr_pairs:
            if src_feat in self:
                src_value = self[src_feat]
                if targ_feat in target and target[targ_feat] != src_value:
                    # Clash; fail!
                    return 'fail'
                else:
                    target[targ_feat] = src_value

    def mutual_agree(self, target, agrs):
        """Make target agree with self and self agree with target
        on features specified in agrs dict or list of pairs."""
        agr_pairs = agrs.items() if isinstance(agrs, dict) else agrs
        for src_feat, targ_feat in agr_pairs:
            if src_feat in self:
                src_value = self[src_feat]
                if targ_feat in target and target[targ_feat] != src_value:
                    # Clash; fail!
                    return 'fail'
                else:
                    target[targ_feat] = src_value
            elif targ_feat in target:
                targ_value = target[targ_feat]
                self[src_feat] = targ_value

    def agrees(self, target, agrs):
        """Does target agree with self on features specified in agrs dict or list of pairs?"""
        agr_pairs = agrs.items() if isinstance(agrs, dict) else agrs
        for src_feat, targ_feat in agr_pairs:
#            print('    src feat {}, targ feat {}, self {}, target {}'.format(src_feat, targ_feat, self, target))
            if src_feat in self:
                src_value = self[src_feat]
                if targ_feat in target and target[targ_feat] != src_value:
                    # Clash; fail!
                    return False
        return True

    @staticmethod
    def all_agree(feats1, feats2, agrs):
        """Return all pairs from feats1 and feats2 that agree on agrs features."""
        pairs = []
        for feat1 in feats1:
            for feat2 in feats2:
                if feat1.agrees(feat2, agrs):
                    pairs.append((feat1, feat2))
        return pairs

    @staticmethod
    def n_agree(feats1, feats2, agrs):
        """Return feats1 objects that agree with some feats2 objects and feats2
        objects that agree with some feats1 objects."""
        f1agr = 0
        f2agr = 0
        for feat1 in feats1:
            for feat2 in feats2:
                if feat1.agrees(feat2, agrs):
                    f1agr += 1
                    break
        for feat2 in feats2:
            for feat1 in feats1:
                if feat1.agrees(feat2, agrs):
                    f2agr += 1
                    break
        return f1agr, f2agr

    @staticmethod
    def agree_with_none1(feats1, feats2, agrs):
        """Return all Features objects in feats1 that fail to agree with any objects in feats2
        on agrs features."""
        failures = []
        for feat1 in feats1:
            fails = True
            for feat2 in feats2:
                if feat1.agrees(feat2, agrs):
                    fails = False
                    break
            if fails:
                failures.append(feat1)
        return failures

    @staticmethod
    def agree_with_none2(feats1, feats2, agrs):
        """Return all Features objects in feats1 that fail to agree with any objects in feats2
        on agrs features."""
        failures = []
        for feat2 in feats2:
            fails = True
            for feat1 in feats1:
                if feat1.agrees(feat2, agrs):
                    fails = False
                    break
            if fails:
                failures.append(feat2)
        return failures

    def match_list(self, feat_list):
        """Does this Features object match list or tuple of feature/value pairs?"""
        for feat, val in feat_list:
            if feat in self:
                selfval = self[feat]
                # val could be a set, in which case selfval has to unify
                # with some element in val
                if isinstance(val, set):
                    if all([Features.simple_unify(v, selfval) == 'fail' for v in val]):
                        return False
                elif Features.simple_unify(val, selfval) == 'fail':
                    return False
        return True
        
    @staticmethod
    def unify_all(features_list):
        """Unify all of the Features objects (or None) in the list, if possible."""
        result = Features({})
        for features in features_list:
            if not features:
                continue
            result = result.unify(features)
            if result == 'fail':
                return 'fail'
        return result
        
class DictStringParser:

    def __init__(self):
        self._features = {}
        self._class = dict
        self._prefix_feature = None
        self._slash_feature = None
        self._features_with_defaults = []

    def parse(self, s, fstruct=None):
        s = s.strip()
        value, position = self.partial_parse(s, 0, fstruct)
        if position != len(s):
            self._error(s, 'end of string', position)
        return value

    _START_FSTRUCT_RE = re.compile(r'\s*(?:\((\d+)\)\s*)?(\??[\w-]+)?(\[)')
    _END_FSTRUCT_RE = re.compile(r'\s*]\s*')
    _FEATURE_NAME_RE = re.compile(r'\s*([+-]?)([^\s\(\)"\'\-=\[\],]+)\s*')
    _TARGET_RE = re.compile(r'\s*\((\d+)\)\s*')
    _ASSIGN_RE = re.compile(r'\s*=\s*')
    _COMMA_RE = re.compile(r'\s*,\s*')
    _BARE_PREFIX_RE = re.compile(r'\s*(?:\((\d+)\)\s*)?(\??[\w-]+\s*)()')

    def partial_parse(self, s, position=0, fstruct=None):
        try:
            return self._partial_parse(s, position, fstruct)
        except ValueError as e:
            if len(e.args) != 2: raise
            self._error(s, *e.args)

    def _partial_parse(self, s, position, fstruct=None):
        # Create the new feature structure
        if fstruct is None:
            fstruct = self._class()
        else:
            fstruct.clear()

        # Read up to the open bracket.  
        match = self._START_FSTRUCT_RE.match(s, position)
        if not match:
            match = self._BARE_PREFIX_RE.match(s, position)
            if not match:
                raise ValueError('open bracket or identifier', position)
        position = match.end()

        # If there as an identifier, record it.
        if match.group(1):
            identifier = match.group(1)

        # If there was a prefix feature, record it.
        if match.group(2):
            if self._prefix_feature is None:
                raise ValueError('open bracket or identifier', match.start(2))
            prefixval = match.group(2).strip()
            if prefixval.startswith('?'):
                prefixval = Variable(prefixval)
            fstruct[self._prefix_feature] = prefixval

        # If group 3 is emtpy, then we just have a bare prefix, so
        # we're done.
        if not match.group(3):
            return fstruct, match.end()

        # Build a list of the features defined by the structure.
        # Each feature has one of the three following forms:
        #     name = value
        #     name -> (target)
        #     +name
        #     -name
        while position < len(s):
            # Use these variables to hold info about each feature:
            name = target = value = None

            # Check for the close bracket.
            match = self._END_FSTRUCT_RE.match(s, position)
            if match is not None:
                return fstruct, position + 1
            
            # Get the feature name's name
            match = self._FEATURE_NAME_RE.match(s, position)
            if match is None: raise ValueError('feature name', position)
            name = match.group(2)
            position = match.end()

            # Check if it's a special feature.
            if name[0] == '*' and name[-1] == '*':
                name = self._features.get(name[1:-1])
                if name is None:
                    raise ValueError('known special feature', match.start(2))

            # Check if this feature has a value already.
            if name in fstruct:
                raise ValueError('new name', match.start(2))

            # Boolean value ("+name" or "-name")
            if match.group(1) == '+': value = True
            if match.group(1) == '-': value = False

            # Assignment ("= value").
            if value is None:
                match = self._ASSIGN_RE.match(s, position)
                if match:
                    position = match.end()
                    value, position = (self.parse_value(s, position))
                # None of the above: error.
                else:
                    raise ValueError('equals sign', position)

            # Store the value.
            fstruct[name] = value
            
            # If there's a close bracket, handle it at the top of the loop.
            if self._END_FSTRUCT_RE.match(s, position):
                continue

            # Otherwise, there should be a comma
            match = self._COMMA_RE.match(s, position)
            if match is None: raise ValueError('comma', position)
            position = match.end()

        # We never saw a close bracket.
        raise ValueError('close bracket', position)

    def parse_value(self, s, position):
        for (handler, regexp) in self.VALUE_HANDLERS:
            match = regexp.match(s, position)
            if match:
                handler_func = getattr(self, handler)
                return handler_func(s, position, match)
        raise ValueError('value', position)

    def _error(self, s, expected, position):
        estr = ('Error parsing feature structure\n    ' +
                s + '\n    ' + ' '*position + '^ ' +
                'Expected %s' % expected)
        raise ValueError(estr)

    VALUE_HANDLERS = [
        ('parse_fstruct_value', _START_FSTRUCT_RE),
        # One more digits followed by alphabetic characters
        ('parse_digit_pre_value', re.compile(r'[0-9]+[a-zA-Z_]+')),
        # Digits only
        ('parse_int_value', re.compile(r'-?\d+')),
        # Other string combinations
        ('parse_sym_value', re.compile(r'\w\w*'))
#        ('parse_str_value', re.compile("[uU]?[rR]?(['\"])")),
        ]

    def parse_fstruct_value(self, s, position, match):
        return self.partial_parse(s, position)

    def parse_digit_pre_value(self, s, position, match):
        val, end = match.group(), match.end()
        return val, end

#    def parse_str_value(self, s, position, match):
#        return internals.parse_str(s, position)

    def parse_int_value(self, s, position, match):
        return int(match.group()), match.end()

    _SYM_CONSTS = {'None':None, 'True':True, 'False':False}
    def parse_sym_value(self, s, position, match):
        val, end = match.group(), match.end()
        return self._SYM_CONSTS.get(val, val), end

PARSER = DictStringParser()
