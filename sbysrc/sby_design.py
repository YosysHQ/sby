#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2022  N. Engelhardt <nak@yosyshq.com>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

import json
from enum import Enum, auto
from dataclasses import dataclass, field

@dataclass
class SbyProperty:
    class Type(Enum):
        ASSUME = auto()
        ASSERT = auto()
        COVER = auto()
        LIVE = auto()

        def __repr__(self):
            return self.name

        @classmethod
        def from_cell(c, name):
            if name == "$assume":
                return c.ASSUME
            if name == "$assert":
                return c.ASSERT
            if name == "$cover":
                return c.COVER
            if name == "$live":
                return c.LIVE
            raise ValueError("Unknown property type: " + name)

    name: str
    type: Type
    location: str
    hierarchy: str
    status: str = field(default="UNKNOWN")
    tracefile: str = field(default="")

@dataclass
class SbyModule:
    name: str
    type: str
    submodules: dict = field(default_factory=dict)
    properties: list = field(default_factory=list)

    def get_property_list(self):
        l = list()
        l.extend(self.properties)
        for submod in self.submodules:
            l.extend(submod.get_property_list())
        return l

def design_hierarchy(filename):
    design_json = json.load(filename)
    def make_mod_hier(instance_name, module_name, hierarchy=""):
        # print(instance_name,":", module_name)
        mod = SbyModule(name=instance_name, type=module_name)

        cells = design_json["modules"][module_name]["cells"]
        for cell_name, cell in cells.items():
            if cell["type"][0] != '$':
                mod.submodules[cell_name] = make_mod_hier(cell_name, cell["type"], hierarchy=f"{hierarchy}/{instance_name}")
            if cell["type"] in ["$assume", "$assert", "$cover", "$live"]:
                try:
                    location = cell["attributes"]["src"]
                except KeyError:
                    location = ""
                p = SbyProperty(name=cell_name, type=SbyProperty.Type.from_cell(cell["type"]), location=location, hierarchy=f"{hierarchy}/{instance_name}")
                mod.properties.append(p)
        return mod

    for module_name in design_json["modules"]:
        attrs = design_json["modules"][module_name]["attributes"]
        if "top" in attrs and int(attrs["top"]) == 1:
            hierarchy = make_mod_hier(module_name, module_name)
            return hierarchy
    else:
        raise ValueError("Cannot find top module")

def main():
    import sys
    if len(sys.argv) != 2:
        print(f"""Usage: {sys.argv[0]} design.json""")
    with open(sys.argv[1]) as f:
        print(design_hierarchy(f))

if __name__ == '__main__':
    main()
