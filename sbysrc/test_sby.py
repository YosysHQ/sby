import unittest

from sby import *


class TestSby(unittest.TestCase):
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

        self.assertIn('[engines]', cfgdata)
        i = cfgdata.index('[engines]')
        self.assertSequenceEqual(['[engines]', 'smtbmc'], cfgdata[index:index+1])
        print(cfgdata)
        print(tasklist)
        