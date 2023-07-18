#!/usr/bin/env python3
import sys
import os

sys.path.append(os.path.abspath(f"{__file__}/../../../sbysrc"))

project = 'YosysHQ SBY'
author = 'YosysHQ GmbH'
copyright = '2023 YosysHQ GmbH'

# select HTML theme

templates_path = ["_templates"]
html_theme = "furo"
html_logo = '../static/logo.png'
html_favicon = '../static/favico.png'
html_css_files = ['custom.css']

# These folders are copied to the documentation's HTML output
html_static_path = ['../static']

# code blocks style
pygments_style = 'colorful'
highlight_language = 'systemverilog'

html_theme_options = {
    "sidebar_hide_name": True,

    "light_css_variables": {
        "color-brand-primary": "#d6368f",
        "color-brand-content": "#4b72b8",
        "color-api-name": "#8857a3",
        "color-api-pre-name": "#4b72b8",
        "color-link": "#8857a3",
    },

    "dark_css_variables": {
        "color-brand-primary": "#e488bb",
        "color-brand-content": "#98bdff",
        "color-api-name": "#8857a3",
        "color-api-pre-name": "#4b72b8",
        "color-link": "#be95d5",
    },
}

extensions = ['sphinx.ext.autosectionlabel']
extensions += ['sphinxarg.ext']
