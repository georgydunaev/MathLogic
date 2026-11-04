#!/usr/bin/env python3

import unittest
import sys
sys.path.append('/botworkspace/MathLogic')
from Propositional import AtomVars, nat

class TestPropositional(unittest.TestCase):
    def test_atom_vars(self):
        # Test that AtomVars is defined as natural numbers
        self.assertEqual(AtomVars, nat)

if __name__ == '__main__':
    unittest.main()


import unittest

class TestPropositional(unittest.TestCase):
    def test_atom_vars(self):
        # Test that AtomVars is defined as natural numbers
        self.assertEqual(AtomVars, nat)

if __name__ == '__main__':
    unittest.main()
