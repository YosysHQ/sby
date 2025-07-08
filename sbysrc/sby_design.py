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

import json, re
from enum import Enum, auto
from dataclasses import dataclass, field
from typing import Optional, Tuple


addr_re = re.compile(r'\\\[[0-9]+\]$')
public_name_re = re.compile(r"\\([a-zA-Z_][a-zA-Z0-9_]*(\[[0-9]+\])?|\[[0-9]+\])$")

def pretty_name(id):
    if public_name_re.match(id):
        return id.lstrip("\\")
    else:
        return id

def pretty_path(path):
    out = ""
    for name in path:
        name = pretty_name(name)
        if name.startswith("["):
            out += name
            continue
        if out:
            out += "."
        if name.startswith("\\") or name.startswith("$"):
            out += name + " "
        else:
            out += name

    return out


@dataclass
class SbyProperty:
    class Type(Enum):
        ASSUME = auto()
        ASSERT = auto()
        COVER = auto()
        LIVE = auto()
        FAIR = auto()

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
            if name == "$fair":
                return c.FAIR
            raise ValueError("Unknown property type: " + name)

        @classmethod
        def from_flavor(c, name):
            if name == "assume":
                return c.ASSUME
            if name == "assert":
                return c.ASSERT
            if name == "cover":
                return c.COVER
            if name == "live":
                return c.LIVE
            if name == "fair":
                return c.FAIR
            raise ValueError("Unknown property type: " + name)

        @property
        def assume_like(self):
            return self in [self.ASSUME, self.FAIR]

    name: str
    path: Tuple[str, ...]
    type: Type
    location: str
    hierarchy: str
    status: str = field(default="UNKNOWN")
    tracefiles: str = field(default_factory=list)

    @property
    def tracefile(self):
        if self.tracefiles:
            return self.tracefiles[0]
        else:
            return ""

    @property
    def celltype(self):
        return f"${str(self.type).lower()}"

    @property
    def kind(self):
        return str(self.type)

    @property
    def hdlname(self):
        return pretty_path(self.path).rstrip()


    def __repr__(self):
        return f"SbyProperty<{self.type} {self.name} {self.path} at {self.location}: status={self.status}, tracefile=\"{self.tracefile}\">"

@dataclass
class SbyModule:
    name: str
    path: Tuple[str, ...]
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

    def find_property(self, path, cell_name, trans_dict=dict()):
        # backends may need to mangle names irreversibly, so allow applying
        # the same transformation here
        trans = str.maketrans(trans_dict)
        path_iter = iter(path)

        mod = next(path_iter).translate(trans)
        if self.name.translate(trans) != mod:
            raise ValueError(f"{self.name} is not the first module in hierarchical path {pretty_path(path)}.")

        mod_hier = self
        for mod in path_iter:
            mod_hier = next((v for k, v in mod_hier.submodules.items() if mod.translate(trans) == k.translate(trans)), None)
            if not mod_hier:
                raise KeyError(f"Could not find {pretty_path(path)} in design hierarchy!")

        prop = next((p for p in mod_hier.properties if cell_name == p.name.translate(trans)), None)
        if not prop:
            raise KeyError(f"Could not find property {cell_name} at location {pretty_print(path)} in properties list!")
        return prop


@dataclass
class SbyDesign:
    hierarchy: SbyModule = None
    memory_bits: int = 0
    forall: bool = False
    properties_by_path: dict = field(default_factory=dict)

    def pass_unknown_asserts(self):
        updated = []
        for prop in self.hierarchy:
            if prop.type == prop.Type.ASSERT and prop.status == "UNKNOWN":
                prop.status = "PASS"
                updated.append(prop)
        return updated


def cell_path(cell):
    path = cell["attributes"].get("hdlname")
    if path is None:
        if cell["name"].startswith('$'):
            return (cell["name"],)
        else:
            return ("\\" + cell["name"],)
    else:
        return tuple(f"\\{segment}" for segment in path.split())


def design_hierarchy(filename):
    design = SbyDesign(hierarchy=None)
    design_json = json.load(filename)
    def make_mod_hier(instance_name, module_name, hierarchy="", path=()):
        # print(instance_name,":", module_name)
        sub_hierarchy=f"{hierarchy}/{instance_name}" if hierarchy else instance_name
        mod = SbyModule(name=instance_name, path=path, type=module_name)

        for m in design_json["modules"]:
            if m["name"] == module_name:
                cell_sorts = m["cell_sorts"]
                break
        else:
            raise ValueError(f"Cannot find module {module_name}")

        for sort in cell_sorts:
            if sort["type"] in ["$assume", "$assert", "$cover", "$live", "$fair"]:
                for cell in sort["cells"]:
                    try:
                        location = cell["attributes"]["src"]
                    except KeyError:
                        location = ""
                    p = SbyProperty(
                        name=cell["name"],
                        path=(*path, *cell_path(cell)),
                        type=SbyProperty.Type.from_cell(sort["type"]),
                        location=location,
                        hierarchy=sub_hierarchy)
                    mod.properties.append(p)
            if sort["type"] == "$check":
                for cell in sort["cells"]:
                    try:
                        location = cell["attributes"]["src"]
                    except KeyError:
                        location = ""
                    p = SbyProperty(
                        name=cell["name"],
                        path=(*path, *cell_path(cell)),
                        type=SbyProperty.Type.from_flavor(cell["parameters"]["FLAVOR"]),
                        location=location,
                        hierarchy=sub_hierarchy)
                    mod.properties.append(p)

            if sort["type"][0] != '$' or sort["type"].startswith("$paramod"):
                for cell in sort["cells"]:
                    mod.submodules[cell["name"]] = make_mod_hier(
                        cell["name"], sort["type"], sub_hierarchy, (*path, *cell_path(cell)))
            if sort["type"] in ["$mem", "$mem_v2"]:
                for cell in sort["cells"]:
                    design.memory_bits += int(cell["parameters"]["WIDTH"], 2) * int(cell["parameters"]["SIZE"], 2)
            if sort["type"] in ["$allconst", "$allseq"]:
                design.forall = True

        return mod

    for m in design_json["modules"]:
        attrs = m["attributes"]
        if "top" in attrs and int(attrs["top"]) == 1:
            design.hierarchy = make_mod_hier(m["name"], m["name"], "", (m["name"],))

            for prop in design.hierarchy:
                design.properties_by_path[prop.path[1:]] = prop
            return design
    else:
        raise ValueError("Cannot find top module")

def main():
    import sys
    if len(sys.argv) != 2:
        print(f"""Usage: {sys.argv[0]} design.json""")
    with open(sys.argv[1]) as f:
        design = design_hierarchy(f)
        print("Design Hierarchy:", design.hierarchy)
        for p in design.hierarchy.get_property_list():
            print("Property:", p)
        print("Memory Bits:", design.memory_bits)

if __name__ == '__main__':
    main()
