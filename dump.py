#! /usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function

import sys

def python_version_supported():
    major, minor = sys.version_info[:2]
    return (major == 2 and minor >= 7) or (major, minor) >= (3, 2)

if not python_version_supported():
    sys.exit("Error: Translator only supports Python >= 2.7 and Python >= 3.2.")


import axiom_rules
import fact_groups
import instantiate
import normalize
import pddl
import pddl_parser

def print_atom(atom, destination=sys.stdout, indent=0, end='\n'):
    print((" " * indent) + "(" + atom.predicate, file=destination, end='')
    for arg in atom.args:
        print(" " + arg, file=destination, end='')
    print(")", file=destination, end=end)

def print_mutex_group(group, destination=sys.stdout, indent=0, end='\n'):
    print((" " * indent) + "(", file=destination, end='')
    for i in range(len(group)):
        if i > 0:
            print(" ", file=destination, end='')
        print_atom(group[i], destination=destination, indent=0, end='')
    print(")", file=destination, end=end)

def dump(task, destination=sys.stdout):

    (goal_relaxed_reachable, atoms, actions, axioms,
     reachable_action_params) = instantiate.explore(task)
    (groups, mutex_groups, tk) = fact_groups.compute_groups(
        task, atoms, reachable_action_params,
        partial_encoding=True)

    print("(:atoms", file=destination)
    for atom in atoms:
        print_atom(atom, destination=destination, indent=2)
    print(" )", file=destination)

    print("(:actions", file=destination)
    for act in actions:
        print("  " + act.name, file=destination);
    print(" )", file=destination)

    print("(:mutex-groups", file=destination)
    for group in mutex_groups:
        if len(group) > 1:
            print_mutex_group(group, destination=destination, indent=2)
    print(" )", file=destination)


if __name__ == '__main__':

    if len(sys.argv) < 3:
        print(sys.argv[0] + " <domain> <problem>")
        sys.exit(0)

    task = pddl_parser.open(task_filename=sys.argv[2],
                            domain_filename=sys.argv[1])

    if len(sys.argv) > 3:
        dumpfile = open(sys.argv[3], "w")
        dump(task, destination=dumpfile)
        dumpfile.close()
    else:
        dump(task)
