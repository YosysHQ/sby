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

        def __str__(self):
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

    def __repr__(self):
        return f"SbyProperty<{self.type} {self.name} at {self.location}: status={self.status}, tracefile=\"{self.tracefile}\""

@dataclass
class SbyModule:
    name: str
    type: str
    submodules: dict = field(default_factory=dict)
    properties: list = field(default_factory=list)

    def __repr__(self):
        return f"SbyModule<{self.name} : {self.type}, submodules={self.submodules}, properties={self.properties}>"

    def __iter__(self):
        for prop in self.properties:
            yield prop
        for submod in self.submodules.values():
            yield from submod.__iter__()

    def get_property_list(self):
        return [p for p in self if p.type != p.Type.ASSUME]

    def find_property(self, hierarchy, location):
        # FIXME: use that RE that works with escaped paths from https://stackoverflow.com/questions/46207665/regex-pattern-to-split-verilog-path-in-different-instances-using-python
        path = hierarchy.split('.')
        mod = path.pop(0)
        if self.name != mod:
            raise ValueError(f"{self.name} is not the first module in hierarchical path {hierarchy}.")
        try:
            mod_hier = self
            while path:
                mod = path.pop(0)
                mod_hier = mod_hier.submodules[mod]
        except KeyError:
            raise KeyError(f"Could not find {hierarchy} in design hierarchy!")
        try:
            prop = next(p for p in mod_hier.properties if location in p.location)
        except StopIteration:
            raise KeyError(f"Could not find assert at {location} in properties list!")
        return prop

    def find_property_by_cellname(self, cell_name):
        for prop in self:
            if prop.name == cell_name:
                return prop
        raise KeyError(f"No such property: {cell_name}")

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
        d = design_hierarchy(f)
        print("Design Hierarchy:", d)
        for p in d.get_property_list():
            print("Property:", p)

if __name__ == '__main__':
    main()
