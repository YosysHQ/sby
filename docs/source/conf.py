#!/usr/bin/env python3
import sys
import os

sys.path.append(os.path.abspath(f"{__file__}/../../../sbysrc"))

project = 'YosysHQ SBY'
author = 'YosysHQ GmbH'
copyright = '2023 YosysHQ GmbH'

# select HTML theme

html_theme = "furo-ys"
html_css_files = ['custom.css']

# These folders are copied to the documentation's HTML output
html_static_path = ['../static']

extensions = ['sphinx.ext.autosectionlabel']
extensions += ['sphinxarg.ext']
