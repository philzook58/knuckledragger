"""
A convenience module to import commonly needed other modules as shorthands
"""

import kdrag as kd
import kdrag.smt as smt

from kdrag.smt import *  # noqa: F403
from kdrag import *  # noqa: F403

# import kdrag.theories.real as real
import kdrag.solvers as solvers
import kdrag.theories as thy
import kdrag.rewrite as rw
import kdrag.tele as tele
import kdrag.config as config

import kdrag.theories.option as option
import kdrag.theories.list as list_
import kdrag.theories.set as set_
import kdrag.theories.seq as seq

config.strict_define = False
