#!/usr/bin/env python3
"""Checks that logic's TLSF programs are the compiler's: compares
tlsf_push_code and tlsf_pop_code, as logic/__snapshot__/theory.md prints
them in WebAssembly text, with Memory::push and Memory::pop of the
allocator the MoonBit compiler embeds (lib/xml/wasm_linear/tlsf-mbt.wat in
its repository), flattened by wasm-tools:

    python3 tools/tlsf_wat_check.py PATH/TO/tlsf-mbt.wat

The programs take the linked value of DATA_SECTION_END as the constant d,
so a call of moonbit.GET_DATA_SECTION_END matches `i32.const d`. Constants
are compared as 32-bit words, an empty `else` is no else, and loads and
stores have their default offset and alignment. Exits 1 if one differs.
"""

import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROGRAMS = [
    ("tlsf_push_code", "$_M0MP211moonbitlang6malloc6Memory4push"),
    ("tlsf_pop_code", "$_M0MP211moonbitlang6malloc6Memory3pop"),
]


def listed(md, name):
    """The program's text in the listing."""
    i = md.index("program `%s`" % name)
    j = md.index("```", i)
    k = md.index("```", j + 3)
    return md[j + 3:k]


def flattened(path):
    """The module at path (fields without a module around them), as
    wasm-tools prints it."""
    with open(path) as f:
        fields = f.read()
    with tempfile.TemporaryDirectory() as d:
        wat = os.path.join(d, "m.wat")
        wasm = os.path.join(d, "m.wasm")
        with open(wat, "w") as f:
            f.write("(module\n" + fields + "\n)\n")
        subprocess.run(["wasm-tools", "parse", wat, "-o", wasm], check=True)
        return subprocess.run(["wasm-tools", "print", wasm], check=True,
                              capture_output=True, text=True).stdout


def function(wat, name):
    """The body of the function `name`."""
    i = wat.index("(func " + name + " ")
    return wat[i:wat.index("\n  )", i)]


def word(n):
    return str(int(n) % 2**32)


def instructions(text):
    out = []
    for line in text.splitlines():
        line = re.sub(r";;.*", "", line)
        line = re.sub(r"\(;\d+;\)", "", line).strip()
        if (not line or line.startswith("(func") or line.startswith("(local")
                or line.endswith("==")):
            continue
        line = re.sub(r'\$"#local(\d+) #local\d+"', r"\1", line)
        line = re.sub(r' \$"#label\d+ #label\d+" \(@name "#label\d+"\)', "", line)
        line = re.sub(r"call \S*GET_DATA_SECTION_END", "i32.const d", line)
        line = re.sub(r"i32\.const (-?\d+)$", lambda m: "i32.const " + word(m.group(1)), line)
        line = line.replace(" offset=0 align=2**2", "")
        if line == "end" and out and out[-1] == "else":
            out.pop()
        out.append(line)
    return out


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    with open(os.path.join(ROOT, "logic", "__snapshot__", "theory.md")) as f:
        md = f.read()
    wat = flattened(sys.argv[1])
    ok = True
    for prog, name in PROGRAMS:
        ours = instructions(listed(md, prog))
        theirs = instructions(function(wat, name))
        if ours == theirs:
            print("%s: the same %d instructions as %s" % (prog, len(ours), name))
            continue
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs from %s at instruction %d:" % (prog, name, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
