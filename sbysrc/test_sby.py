import unittest

from sby import *


class TestSby(unittest.TestCase):
    def assertContainsSubsequence(self, sequence, subsequence):
        if len(subsequence) == 0:
            return
        self.assertIn(subsequence[0], sequence)
        i = sequence.index(subsequence[0])
        self.assertSequenceEqual(sequence[i:i+len(subsequence)], subsequence)

    def test_read_sbyconfig(self):
        cfg = '''
[tasks]
a
b

[options]
a:
mode prove
depth 100

b:
mode cover
depth 100

[engines]
smtbmc

[script]
read -formal foo.v
prep -top foo

[files]
foo.v
'''
        sbydata = cfg.split('\n')
        cfgdata, tasklist = read_sbyconfig(sbydata, 'a')

        self.assertContainsSubsequence(cfgdata, ['[engines]', 'smtbmc'])
        # self.assertIn('[engines]', cfgdata)
        # i = cfgdata.index('[engines]')
        # self.assertSequenceEqual(['[engines]', 'smtbmc'], cfgdata[i:i+2])
        # print(cfgdata)
        # print(tasklist)
        