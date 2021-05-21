#!/usr/bin/env python3
project = 'YosysHQ-AppNote-120'
author = 'YosysHQ Gmbh'
copyright ='2021 YosysHQ Gmbh'

# select HTML theme
html_theme = 'alabaster'

# These folders are copied to the documentation's HTML output
html_static_path = ['_static']

# code blocks style 
pygments_style = 'colorful'
highlight_language = 'systemverilog'

html_theme_options = {
    'extra_nav_links' : { 
        'Documentation Index' : 'https://yosyshq-docs.readthedocs.io' ,
        'YosysHQ Website' : 'https://www.yosyshq.com',
    },
#   'logo' : 'logo.png',
    'fixed_sidebar' : True,
}
