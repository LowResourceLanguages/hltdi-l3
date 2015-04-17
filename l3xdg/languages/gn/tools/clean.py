########################################################################
#
#   This file is part of the HLTDI L^3 project
#       for parsing, generation, and translation within the
#       framework of  Extensible Dependency Grammar.
#
#   Copyright (C) 2010, 2011, 2012, 2013
#   The HLTDI L^3 Team <gasser@cs.indiana.edu>
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
#   --------------------------------------------------------------------
#   Author: Michael Gasser <gasser@indiana.edu>
#
#   Clean up Guarani for further processing.
#
# 2013.08.12
# -- Copied here from LingData/Gn

def clean_file(inf, outf):
    """Clean up Guarani file inf, writing to file outf."""
    with open(inf, encoding='utf8') as i:
        with open(outf, 'w', encoding='utf8') as o:
            for line in i:
                line = clean(line)
                print(line, end='', file=o)

def clean(string):
    """Clean up Guarani string, replacing commonly used alternative characters"""
    # Nasal vowels: replace umlaut and circumflex with tilde
    string = string.replace('î', 'ĩ').replace('â', 'ã').replace('ê', 'ẽ')
    string = string.replace('ô', 'õ').replace('û', 'ũ').replace('ŷ', 'ỹ')
    string = string.replace('Î', 'Ĩ').replace('Â', 'Ã').replace('Ê', 'Ẽ')
    string = string.replace('Ô', 'Õ').replace('Û', 'Ũ').replace('Ŷ', 'Ỹ')
    string = string.replace('ï', 'ĩ').replace('ä', 'ã').replace('ë', 'ẽ')
    string = string.replace('ö', 'õ').replace('ü', 'ũ').replace('ÿ', 'ỹ')
    string = string.replace('Ï', 'Ĩ').replace('Ä', 'Ã').replace('Ë', 'Ẽ')
    string = string.replace('Ö', 'Õ').replace('Ü', 'Ũ').replace('Ÿ', 'Ỹ')
    # Galeano sometimes uses this Vietnamese vowel for some reason
    string = string.replace("ữ", "ũ")
    # Puso: use ordinary single quote
    for c in "’`´°‘":
        string = string.replace(c, "'")
    # Accented vowels; some people use grave instead of acute
    string = string.replace("à", "á").replace("è", "é").replace("ì", "í")
    string = string.replace("ò", "ó").replace("ù", "ú").replace("ỳ", "ý")
    string = string.replace("À", "Á").replace("È", "É").replace("Ì", "Í")
    string = string.replace("Ò", "Ó").replace("Ù", "Ú").replace("Ỳ", "Ý")
    # Nasal g: replace double character with circumflex g
    string = string.replace("g̃", "ĝ").replace("G̃", "Ĝ")
    # Galeano uses this
    string = string.replace("ğ", "ĝ").replace("Ğ", "Ĝ")
    return string

def basic_clean(string):
    """Clean Vikipetã contents."""
    # Simplify nasal g by replacing double character with circumflex g
    string = string.replace("g̃", "ĝ").replace("G̃", "Ĝ")
    # Puso: use ordinary single quote
    for c in "’‘":
        string = string.replace(c, "'")
    return string
