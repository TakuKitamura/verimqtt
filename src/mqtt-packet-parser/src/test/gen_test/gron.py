# python-gron https://github.com/venthur/python-gron

"""
MIT License

Copyright (c) 2018 Bastian Venthur

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""

"""Gron's core functions.
"""

import json
from typing import Any


def walk(node: Any, name: str) -> str:
    """Translate Python element to JSON.
    This method recursively visits each element of a Python object and
    returns the JSON representation.
    Parameters
    ----------
    node
        A python object (e.g. dict, list, int, etc)
    name : str
        The name (i.e. path) of the parent element
    Returns
    -------
    str
        Transformed JSON for this element
    """
    if node is None:
        return "{name} = {value}".format(name=name, value='null')
    elif isinstance(node, bool):
        return "{name} = {value}".format(name=name, value=str(node).lower())
    elif isinstance(node, (str, bytes)):
        return '{name} = "{value}"'.format(name=name, value=node)
    elif isinstance(node, dict):
        res = []
        res.append("{name} = {{}}".format(name=name))
        for k, v in sorted(node.items()):
            res.append(walk(v, name + convert('.' + k)))
        return '\n'.join(sorted(res))
    elif isinstance(node, (list, tuple)):
        res = []
        res.append("{name} = []".format(name=name))
        for i, e in enumerate(node):
            res.append(walk(e, name + convert(str([i]))))
        return '\n'.join(res)

    else:
        return "{name} = {value!r}".format(name=name, value=node)


def convert(name: str) -> str:
    """Convert path name into valid JSON.
    Parameters
    ----------
    name : str
        a path name
    Returns
    -------
    str
        valid JSON path
    """
    if ('-' in name or ' ' in name):
        return '["{}"]'.format(name[1:])
    return name


def gron(input_: str) -> str:
    """Transform JSON into parseable str.
    This method takes a JSON string and transforms it into a grepable
    equivalent form.
    Parameters
    ----------
    input_ : str
        JSON
    Returns
    -------
    str
        Transformed output
    """
    python = json.loads(input_)
    output = walk(python, 'json')
    splited_output = output.split('\n')
    output = []
    for line in splited_output:
        if '{}' not in line:
            output.append(line[5:])
    return output
