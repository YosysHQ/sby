from setuptools import setup, find_packages
setup(
    name='SymbiYosys', 
    packages=['sby'], 
    version='0.1', 
    description='Front-end for Yosys-based formal verification flows',
    author='Clifford Wolf',
    author_email='clifford@clifford.at',
    install_requires=[],
    py_modules=find_packages())