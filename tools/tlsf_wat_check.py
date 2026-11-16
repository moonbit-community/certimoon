#!/usr/bin/env python3
"""Checks that the TLSF programs are the compiler's: compares
tlsf_push_code, tlsf_pop_code, tlsf_find_code, tlsf_split_code and
tlsf_take_code, tlsf_ensure_code, tlsf_free_code, tlsf_initialize_code and
tlsf_page_allocate_code and tlsf_block_free_code, as
tlsf/__snapshot__/theory.md prints them in WebAssembly text, with
Memory::push, Memory::pop, the initial search block and the split suffix of
Memory::take, the complete Memory::take, Memory::ensure, Memory::free,
initialize_memory, Page::allocate and the inline Block::free branch in the
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
FIND_PARENT = "$_M0MP211moonbitlang6malloc6Memory4take"
PUSH_NAME = "$_M0MP211moonbitlang6malloc6Memory4push"
POP_NAME = "$_M0MP211moonbitlang6malloc6Memory3pop"
ENSURE_NAME = "$_M0MP211moonbitlang6malloc6Memory6ensure"
FREE_NAME = "$_M0MP211moonbitlang6malloc6Memory4free"
PUBLIC_FREE_NAME = "$moonbit.free"
PAGE_ALLOCATE_NAME = "$_M0MP211moonbitlang6malloc4Page8allocate"
INITIALIZE_NAME = "$_M0FP211moonbitlang6malloc18initialize__memory"


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
    labels = []
    for line in text.splitlines():
        line = re.sub(r";;.*", "", line)
        line = re.sub(r"\(;\d+;\)", "", line).strip()
        if (not line or line.startswith("(func") or line.startswith("(local")
                or line.endswith("==")):
            continue
        line = re.sub(r'\$"#local(\d+) #local\d+"', r"\1", line)
        label = re.search(r'(\$"[^"]+"|\$[^\s()]+)(?: \(@name "[^"]*"\))?', line)
        op = line.split()[0]
        if op in ("block", "loop", "if"):
            labels.append(label.group(1) if label else None)
            if label:
                line = line[:label.start()] + line[label.end():]
                line = " ".join(line.split())
        elif op in ("br", "br_if") and label:
            target = label.group(1)
            if target not in labels:
                raise ValueError("unknown branch label: " + target)
            line = op + " " + str(labels[::-1].index(target))
        elif op == "end":
            if not labels:
                raise ValueError("unbalanced end")
            labels.pop()
        line = re.sub(r"call \S*GET_DATA_SECTION_END", "i32.const d", line)
        line = re.sub(r"i32\.const (-?\d+)$", lambda m: "i32.const " + word(m.group(1)), line)
        line = line.replace(" offset=0 align=2**2", "")
        if line == "end" and out and out[-1] == "else":
            out.pop()
        out.append(line)
    return out


def check_signature(body, name, nresults, nlocals, nparams=1):
    """The native closure type and zero-initialised locals used by the call proof."""
    # wasm-tools prints the function declarations before its first instruction.
    # A block's (result ...) is a block type, not a function result.
    declarations = []
    for line in body.splitlines():
        if not line.strip():
            continue
        if not line.lstrip().startswith(('(func ', '(type ', '(param ', '(result ', '(local ')):
            break
        declarations.append(line)
    body = '\n'.join(declarations)
    body = re.sub(r'\(@name "[^"]*"\)', '', body)
    body = re.sub(r'\$"[^"]*"|\$[^\s()]+', '', body)
    signature = []
    for kind, fields in re.findall(r'\((param|result|local)\s+([^()]*)\)', body):
        types = [field for field in fields.split() if not field.startswith('$')]
        signature.append((kind, types))
    params = [t for k, ts in signature if k == 'param' for t in ts]
    results = [t for k, ts in signature if k == 'result' for t in ts]
    locals_ = [t for k, ts in signature if k == 'local' for t in ts]
    if params != ['i32'] * nparams or results != ['i32'] * nresults or locals_ != ['i32'] * nlocals:
        raise ValueError("Memory::%s signature or locals changed" % name)


def check_push_signature(body):
    check_signature(body, 'push', 1, 3)


def check_pop_signature(body):
    check_signature(body, 'pop', 0, 4)


def check_take_signature(body):
    check_signature(body, 'take', 1, 5)


def check_ensure_signature(body):
    check_signature(body, 'ensure', 1, 1)


def check_free_signature(body):
    check_signature(body, 'free', 1, 2)


def check_initialize_signature(body):
    check_signature(body, 'initialize_memory', 0, 3, nparams=0)


def check_page_allocate_signature(body):
    check_signature(body, "Page::allocate", 1, 5)


def block_free_branch(body):
    """The exact then arm implementing inlined Block::free and Page::free."""
    marker = ['i32.const 4', 'i32.and', 'if (result i32)']
    starts = [i for i in range(len(body) - 2) if body[i:i+3] == marker]
    if len(starts) != 1:
        raise ValueError('changed small-block dispatch boundary')
    start = starts[0] + 3
    depth = 1
    for end in range(start, len(body)):
        op = body[end].split()[0]
        if op in ('block', 'loop', 'if'):
            depth += 1
        elif op == 'end':
            depth -= 1
        elif op == 'else' and depth == 1:
            result = body[start:end]
            call = 'call ' + FREE_NAME
            if result.count(call) != 1:
                raise ValueError('Block::free must contain exactly one ' + call)
            return ['call free_idx' if line == call else line for line in result]
        if depth == 0:
            break
    raise ValueError('missing small-block dispatch else boundary')


def full_page_allocate(body):
    call = "call " + FIND_PARENT
    if body.count(call) != 1:
        raise ValueError("Page::allocate must contain exactly one " + call)
    return ["call take_idx" if line == call else line for line in body]


def full_initialize(body):
    """Keep the entire initializer, including both deliberate aborts."""
    call = 'call ' + PUSH_NAME
    if body.count(call) != 1:
        raise ValueError("initialize_memory must contain exactly one " + call)
    return ['call push' if line == call else line for line in body]


def full_free(body):
    """Both optional coalescing pops and the final push, without erasing stores."""
    calls = {'call ' + POP_NAME: ('call pop', 2),
             'call ' + PUSH_NAME: ('call push', 1)}
    for call, (_, count) in calls.items():
        if body.count(call) != count:
            raise ValueError("Memory::free helper call count changed: " + call)
    return [calls[line][0] if line in calls else line for line in body]


def full_ensure(body):
    """The entire ensure body, with both growth paths and linked helpers."""
    calls = {'call ' + POP_NAME: ('call pop', 1),
             'call ' + PUSH_NAME: ('call push', 2)}
    for call, (_, count) in calls.items():
        if body.count(call) != count:
            raise ValueError("Memory::ensure helper call count changed: " + call)
    return [calls[line][0] if line in calls else line for line in body]


def full_take(body):
    """Keep the entire take body, linking both real helper calls."""
    calls = {'call ' + POP_NAME: 'call pop', 'call ' + PUSH_NAME: 'call push'}
    for call in calls:
        if body.count(call) != 1:
            raise ValueError("Memory::take must contain exactly one " + call)
    return [calls.get(line, line) for line in body]


def find_prefix(body):
    """The exact read-only search block in the shipped Memory::take."""
    if not body or body[0] != "block (result i32)":
        raise ValueError("Memory::take no longer starts with the search block")
    depth = 0
    for i, line in enumerate(body):
        if line.split()[0] in ("block", "loop", "if"):
            depth += 1
        elif line == "end":
            depth -= 1
            if depth == 0:
                return body[:i + 1]
    raise ValueError("unterminated search block")


def split_suffix(body):
    """The guard, split, and final mark-used after pop in Memory::take.

    Keep the real push call, with its linked function index named push in
    the proof. Do not include take's return or its enclosing conditional.
    """
    pop = "call " + POP_NAME
    push = "call " + PUSH_NAME
    if body.count(pop) != 1:
        raise ValueError("Memory::take must call pop exactly once")
    start = body.index(pop) + 1
    try:
        ret = body.index("return", start)
    except ValueError:
        raise ValueError("Memory::take has no successful return") from None
    if body[ret - 1:ret + 3] != ["local.get 0", "return", "end", "local.get 0"]:
        raise ValueError("Memory::take successful return boundary changed")
    result = body[start:ret - 1]
    if (not result or result[0:2] != ["local.get 0", "i32.load"]
            or result[-1] != "i32.store" or result.count(push) != 1):
        raise ValueError("Memory::take split boundaries changed")
    depth = 0
    for line in result:
        if line.split()[0] in ("block", "loop", "if"):
            depth += 1
        elif line == "end":
            depth -= 1
        if depth < 0:
            raise ValueError("split exits its fragment")
    if depth:
        raise ValueError("unterminated split fragment")
    return ["call push" if line == push else line for line in result]


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    with open(os.path.join(ROOT, "tlsf", "__snapshot__", "theory.md")) as f:
        md = f.read()
    wat = flattened(sys.argv[1])
    check_push_signature(function(wat, PUSH_NAME))
    check_pop_signature(function(wat, POP_NAME))
    check_take_signature(function(wat, FIND_PARENT))
    check_ensure_signature(function(wat, ENSURE_NAME))
    check_free_signature(function(wat, FREE_NAME))
    check_initialize_signature(function(wat, INITIALIZE_NAME))
    check_page_allocate_signature(function(wat, PAGE_ALLOCATE_NAME))
    check_signature(function(wat, PUBLIC_FREE_NAME), "public free", 0, 2)
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
    prog = "tlsf_find_code"
    ours = instructions(listed(md, prog))
    theirs = find_prefix(instructions(function(wat, FIND_PARENT)))
    if ours == theirs:
        print("%s: the same %d instructions as the search block in %s" %
              (prog, len(ours), FIND_PARENT))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    prog = "tlsf_split_code"
    ours = instructions(listed(md, prog))
    theirs = split_suffix(instructions(function(wat, FIND_PARENT)))
    if ours == theirs:
        print("%s: the same %d instructions as the split fragment in %s" %
              (prog, len(ours), FIND_PARENT))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    prog = "tlsf_take_code"
    ours = instructions(listed(md, prog))
    theirs = full_take(instructions(function(wat, FIND_PARENT)))
    if ours == theirs:
        print("%s: the same %d instructions as the complete %s" %
              (prog, len(ours), FIND_PARENT))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    prog = "tlsf_ensure_code"
    ours = instructions(listed(md, prog))
    theirs = full_ensure(instructions(function(wat, ENSURE_NAME)))
    if ours == theirs:
        print("%s: the same %d instructions as the complete %s" %
              (prog, len(ours), ENSURE_NAME))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    prog = "tlsf_free_code"
    ours = instructions(listed(md, prog))
    theirs = full_free(instructions(function(wat, FREE_NAME)))
    if ours == theirs:
        print("%s: the same %d instructions as the complete %s" %
              (prog, len(ours), FREE_NAME))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    prog = "tlsf_initialize_code"
    ours = instructions(listed(md, prog))
    theirs = full_initialize(instructions(function(wat, INITIALIZE_NAME)))
    if ours == theirs:
        print("%s: the same %d instructions as the complete %s" %
              (prog, len(ours), INITIALIZE_NAME))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    prog = "tlsf_page_allocate_code"
    ours = instructions(listed(md, prog))
    theirs = full_page_allocate(instructions(function(wat, PAGE_ALLOCATE_NAME)))
    if ours == theirs:
        print("%s: the same %d instructions as the complete %s" %
              (prog, len(ours), PAGE_ALLOCATE_NAME))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    prog = "tlsf_block_free_code"
    ours = instructions(listed(md, prog))
    theirs = block_free_branch(instructions(function(wat, PUBLIC_FREE_NAME)))
    if ours == theirs:
        print("%s: the same %d instructions as the Block::free branch of %s" %
              (prog, len(ours), PUBLIC_FREE_NAME))
    else:
        ok = False
        n = next((k for k, (a, b) in enumerate(zip(ours, theirs)) if a != b),
                 min(len(ours), len(theirs)))
        print("%s differs at instruction %d:" % (prog, n))
        print("  ours:     %s" % (ours[n] if n < len(ours) else "(end)"))
        print("  compiled: %s" % (theirs[n] if n < len(theirs) else "(end)"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
