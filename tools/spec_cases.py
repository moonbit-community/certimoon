#!/usr/bin/env python3
"""Writes wasm/spec_cases_test.mbt: the integer assertions of the WebAssembly
spec testsuite's i32.wast and i64.wast, the in-range integer loads of
address.wast, and the integer assertions of the control-flow files, as
cases for wasm/spec_test.mbt.

    python3 tools/spec_cases.py <testsuite commit> i32.wast i64.wast address.wast \
      block.wast loop.wast br.wast br_if.wast br_table.wast call.wast return.wast \
      call_indirect.wast > wasm/spec_cases_test.mbt

Each exported function of i32.wast and i64.wast applies one operator to its
parameters; a case is (operator, operands, result), or a trap.

address.wast's integer modules load from a page whose first bytes are
"abcdefghijklmnopqrstuvwxyz". The evaluator computes on memory byte by
byte, so the cases run in a memory of those bytes and 14 zeros (as far as
any of the loads reach), and only the assertions at address 0 are kept:
the others test the end of the 64 KiB page.

The control-flow files (any other file named) are read as modules: each
module's functions are translated to the builder's instructions (`Func`),
and a case calls an exported function with constant arguments in a store
of the module's functions, globals and memory. A module's assertions run
in order, each in the store the one before left, as the file runs them.

A module's tables of functions are written out as its element segments
leave them, and call_indirect calls through them.

What the builder cannot write is left out, and the comment before each
file's cases counts it (why each assertion is left out goes to stderr):
a function that uses floats, references, the table instructions, a table
that does not hold functions, or memory.size and memory.grow (a module's
memory is a few zero bytes, MEMORY or MEMORY_OF, not a page), or a
br_table of more than 1000 labels (br_table.wast has one of 16148: too
long a list to write out as a term), is replaced by `unreachable`, and
an assertion is kept only if its arguments and results are integers and
its function and every function it can call were translated. For an
assertion of a result, "can call" means directly: a function it reaches
only through a table may be one left out, since running into its
`unreachable`, or calling it with its type changed, traps and so fails
the case rather than passing it. For an assertion of a trap, it includes
every function of the tables it can reach. An assertion left out does not run,
so the next one sees the store without its changes. `assert_exhaustion`
is left out (the evaluator stops after a number of steps, not at a stack
depth). The assertions in SLOW take too long to prove one step at a time;
they are marked slow, and only the skipped test runs them (`moon test
--include-skipped`).
"""

import re
import sys

BINOPS = {
    "add": "Add", "sub": "Sub", "mul": "Mul",
    "div_s": "Div(Signed)", "div_u": "Div(Unsigned)",
    "rem_s": "Rem(Signed)", "rem_u": "Rem(Unsigned)",
    "and": "And", "or": "Or", "xor": "Xor", "shl": "Shl",
    "shr_s": "Shr(Signed)", "shr_u": "Shr(Unsigned)",
    "rotl": "Rotl", "rotr": "Rotr",
}
UNOPS = {"clz": "Clz", "ctz": "Ctz", "popcnt": "Popcnt"}
RELOPS = {
    "eq": "Equal", "ne": "NotEqual",
    "lt_s": "Less(Signed)", "lt_u": "Less(Unsigned)",
    "gt_s": "Greater(Signed)", "gt_u": "Greater(Unsigned)",
    "le_s": "LessEq(Signed)", "le_u": "LessEq(Unsigned)",
    "ge_s": "GreaterEq(Signed)", "ge_u": "GreaterEq(Unsigned)",
}

CONST = r"\((i32|i64)\.const\s+([-+0-9a-fA-Fx_]+)\)"
RETURN = re.compile(r'\(assert_return\s+\(invoke\s+"([a-z0-9_]+)"((?:\s*' + CONST + r')*)\s*\)\s*(?:' + CONST + r')\s*\)')
TRAP = re.compile(r'\(assert_trap\s+\(invoke\s+"([a-z0-9_]+)"((?:\s*' + CONST + r')*)\s*\)\s*"([^"]*)"\s*\)')


def bits(ty, text):
    n = int(text.replace("_", ""), 0)
    return n % (1 << (32 if ty == "i32" else 64))


EXTENDS = {"extend8_s": "P8", "extend16_s": "P16", "extend32_s": "P32"}


def instr(ty, op):
    t = ty.upper()
    if op in EXTENDS:
        return f"ExtendS({t}, {EXTENDS[op]})"
    if op in BINOPS:
        return f"Binop({t}, {BINOPS[op]})"
    if op in UNOPS:
        return f"Unop({t}, {UNOPS[op]})"
    if op in RELOPS:
        return f"Relop({t}, {RELOPS[op]})"
    if op == "eqz":
        return f"Eqz({t})"
    return None


def const(ty, n):
    return f"I32Const({n})" if ty == "i32" else f"I64Const({n}UL)"


def value(ty, n):
    return f"I32Val({n})" if ty == "i32" else f"I64Val({n}UL)"


def cases(path):
    ty = "i32" if "i32" in path else "i64"
    text = open(path).read()
    out = []
    for m in RETURN.finditer(text):
        op, args = m.group(1), m.group(2)
        ins = instr(ty, op)
        if ins is None:
            continue
        operands = [const(t, bits(t, v)) for t, v in re.findall(CONST, args)]
        rty, r = m.group(m.lastindex - 1), m.group(m.lastindex)
        out.append(f'  ("{ty}.{op}", [{", ".join(operands + [ins])}], Some({value(rty, bits(rty, r))})),')
    for m in TRAP.finditer(text):
        op, args = m.group(1), m.group(2)
        ins = instr(ty, op)
        if ins is None:
            continue
        operands = [const(t, bits(t, v)) for t, v in re.findall(CONST, args)]
        out.append(f'  ("{ty}.{op}", [{", ".join(operands + [ins])}], None),')
    return out


LOAD = re.compile(r'\(func \(export "([0-9a-z_]+)"\) \(param \$i i32\) \(result (i32|i64)\)\s*\((i32|i64)\.load(8|16|32)?(?:_([su]))?((?:\s+(?:offset|align)=\d+)*)\s+\(local\.get \$i\)\)')
PACKED = {"8": "P8", "16": "P16", "32": "P32"}


def load_cases(path):
    out = []
    # the modules of address.wast, each with its functions and assertions
    for module in re.split(r"\n\(module", open(path).read())[1:]:
        funcs = {}
        for m in LOAD.finditer(module):
            name, _, ty, width, sx, attrs = m.groups()
            off = re.search(r"offset=(\d+)", attrs)
            off = int(off.group(1)) if off else 0
            t = ty.upper()
            if width is None:
                funcs[name] = (ty, f"Load({t}, {off})")
            else:
                s = "Signed" if sx == "s" else "Unsigned"
                funcs[name] = (ty, f"LoadPacked({t}, {PACKED[width]}, {s}, {off})")
        for m in RETURN.finditer(module):
            name, args = m.group(1), m.group(2)
            if name not in funcs:
                continue
            operands = re.findall(CONST, args)
            if operands != [("i32", "0")]:
                continue
            ty, ins = funcs[name]
            rty, r = m.group(m.lastindex - 1), m.group(m.lastindex)
            out.append(f'  ("{ty}.{name}", [I32Const(0), {ins}], Some({value(rty, bits(rty, r))})),')
    return out


# The control-flow files: a reader for the text format's s-expressions and
# a translation of the modules' functions to the builder's instructions.

# the bytes of memory a module gets (zeros), if it has a memory: as far as
# its loads and stores reach
MEMORY = 64
MEMORY_OF = {"call.wast": 320, "call_indirect.wast": 320}  # they load and store at 0x132

# assertions whose runs take too many steps to prove one by one, run only
# by the skipped test: (file, function, its first argument). A step's
# proof is rebuilt through every frame around it, so a run of recursion
# depth d costs about d^2: fac 25 takes a minute, even 100 over half an
# hour, and fib 20 (about 22000 calls) far longer. The same functions'
# small cases run in the usual test.
SLOW = {
    ("call.wast", "fac", "25"), ("call.wast", "fac-acc", "25"),
    ("call.wast", "fib", "20"),
    ("call.wast", "even", "100"), ("call.wast", "even", "77"),
    ("call.wast", "odd", "200"), ("call.wast", "odd", "77"),
    ("call_indirect.wast", "fac-i64", "25"),
    ("call_indirect.wast", "fib-i64", "20"), ("call_indirect.wast", "fib-i32", "20"),
    ("call_indirect.wast", "even", "100"), ("call_indirect.wast", "even", "77"),
    ("call_indirect.wast", "odd", "200"), ("call_indirect.wast", "odd", "77"),
    # fib 9, through the table
    ("call_indirect.wast", "dispatch-structural-i64", "13"),
    ("call_indirect.wast", "dispatch-structural-i32", "26"),
}


class Unsupported(Exception):
    pass


def sexprs(text):
    """The top-level s-expressions of `text`: a list is a Python list, an
    atom a string (a string literal keeps its quotes)."""
    text = re.sub(r"\(;.*?;\)", " ", text, flags=re.S)
    tokens = re.findall(r'"(?:[^"\\]|\\.)*"|;;[^\n]*|[()]|[^\s()";]+', text)
    stack = [[]]
    for tok in tokens:
        if tok.startswith(";;"):
            continue
        if tok == "(":
            stack.append([])
        elif tok == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0]


def is_list(x, head=None):
    return isinstance(x, list) and (head is None or (x and x[0] == head))


NUMTYPES = {"i32": "I32", "i64": "I64"}


def numtype(t):
    if not isinstance(t, str) or t not in NUMTYPES:
        raise Unsupported(t)
    return NUMTYPES[t]


def type_list(items, head):
    """The types of the `(head ...)` lists among `items` (params, results,
    locals), with their names: [(name or None, type)]."""
    out = []
    for x in items:
        if is_list(x, head):
            rest = x[1:]
            if rest and isinstance(rest[0], str) and rest[0].startswith("$"):
                out.append((rest[0], rest[1]))
            else:
                out.extend((None, t) for t in rest)
    return out


def literal(ty, text):
    if ty not in ("i32", "i64"):
        raise Unsupported(ty + ".const")
    return bits(ty, text)


SIMPLE = {
    "nop": "Nop", "unreachable": "Unreachable", "drop": "Drop",
    "select": "Select", "return": "Return",
    "i32.wrap_i64": "I32WrapI64",
    "i64.extend_i32_s": "I64ExtendI32(Signed)",
    "i64.extend_i32_u": "I64ExtendI32(Unsigned)",
}
LOADS = {
    "i32.load": "Load(I32, {})", "i64.load": "Load(I64, {})",
    "i32.load8_s": "LoadPacked(I32, P8, Signed, {})",
    "i32.load8_u": "LoadPacked(I32, P8, Unsigned, {})",
    "i32.load16_s": "LoadPacked(I32, P16, Signed, {})",
    "i32.load16_u": "LoadPacked(I32, P16, Unsigned, {})",
    "i64.load8_s": "LoadPacked(I64, P8, Signed, {})",
    "i64.load8_u": "LoadPacked(I64, P8, Unsigned, {})",
    "i64.load16_s": "LoadPacked(I64, P16, Signed, {})",
    "i64.load16_u": "LoadPacked(I64, P16, Unsigned, {})",
    "i64.load32_s": "LoadPacked(I64, P32, Signed, {})",
    "i64.load32_u": "LoadPacked(I64, P32, Unsigned, {})",
    "i32.store": "Store(I32, {})", "i64.store": "Store(I64, {})",
    "i32.store8": "StorePacked(I32, P8, {})",
    "i32.store16": "StorePacked(I32, P16, {})",
    "i64.store8": "StorePacked(I64, P8, {})",
    "i64.store16": "StorePacked(I64, P16, {})",
    "i64.store32": "StorePacked(I64, P32, {})",
}


def is_index(a):
    return isinstance(a, str) and (a.startswith("$") or a.isdigit())


class Module:
    def __init__(self, items):
        self.types = {}      # type name or index -> (params, results)
        self.funcs = []      # (name, params, results, locals, body items)
        self.exports = {}    # export name -> function index
        self.globals = []    # (name, type, value)
        self.memory = False
        self.block_types = []
        self.tables = []     # (name, entries: function refs or None) or (name, None)
        segments = []        # (table ref, offset, function refs)
        ntypes = 0
        for x in items:
            if is_list(x, "type"):
                rest = x[1:]
                name = rest[0] if isinstance(rest[0], str) else None
                f = rest[-1]
                sig = ([t for _, t in type_list(f[1:], "param")],
                       [t for _, t in type_list(f[1:], "result")])
                self.types[str(ntypes)] = sig
                if name:
                    self.types[name] = sig
                ntypes += 1
            elif is_list(x, "import"):
                raise Unsupported("import")
            elif is_list(x, "memory"):
                if any(is_list(y, "data") for y in x):
                    raise Unsupported("data")
                self.memory = True
            elif is_list(x, "data"):
                raise Unsupported("data")
            elif is_list(x, "global"):
                rest = x[1:]
                name = rest[0] if isinstance(rest[0], str) and rest[0].startswith("$") else None
                if name:
                    rest = rest[1:]
                ty = rest[0]
                if is_list(ty, "mut"):
                    ty = ty[1]
                init = rest[1]
                if ty not in NUMTYPES or not is_list(init) or init[0] != ty + ".const":
                    self.globals.append((name, None, None))
                else:
                    self.globals.append((name, ty, literal(ty, init[1])))
            elif is_list(x, "table"):
                self.add_table(x[1:])
            elif is_list(x, "elem"):
                seg = self.elem_segment(x[1:])
                if seg is not None:
                    segments.append(seg)
            elif is_list(x, "func"):
                self.add_func(x[1:])
            elif is_list(x, "export"):
                if is_list(x[2], "func"):
                    self.exports[x[1][1:-1]] = self.func_index(x[2][1])
        # the tables' entries, as functions' indices, after the segments
        self.table_entries = []
        for name, entries in self.tables:
            self.table_entries.append(
                None if entries is None
                else [None if e is None else self.func_index(e) for e in entries])
        for t, off, refs in segments:
            k = self.table_index(t)
            entries = self.table_entries[k]
            if entries is None or off + len(refs) > len(entries):
                raise Unsupported("elem")
            for i, r in enumerate(refs):
                entries[off + i] = self.func_index(r)

    def add_table(self, rest):
        name = None
        if rest and isinstance(rest[0], str) and rest[0].startswith("$"):
            name, rest = rest[0], rest[1:]
        while rest and is_list(rest[0], "export"):
            rest = rest[1:]
        if rest and is_list(rest[0], "import"):
            raise Unsupported("import")
        if "funcref" not in rest:
            # a table of other references: a call through it is left out
            self.tables.append((name, None))
            return
        k = rest.index("funcref")
        if k + 1 < len(rest) and is_list(rest[k + 1], "elem"):
            refs = [self.elem_ref(r) for r in rest[k + 1][1:]]
            self.tables.append((name, refs))
        else:
            self.tables.append((name, [None] * int(rest[0], 0)))

    def elem_ref(self, r):
        if isinstance(r, str):
            return r
        if is_list(r, "ref.func"):
            return r[1]
        if is_list(r, "item") and len(r) == 2 and is_list(r[1], "ref.func"):
            return r[1][1]
        raise Unsupported("elem")

    def elem_segment(self, rest):
        """An active segment as (table, offset, function refs); None for a
        passive or declared one."""
        if rest and isinstance(rest[0], str) and rest[0].startswith("$"):
            rest = rest[1:]
        table = "0"
        if rest and is_list(rest[0], "table"):
            table, rest = rest[0][1], rest[1:]
        if not rest or not is_list(rest[0]):
            return None
        off = rest[0]
        if is_list(off, "offset"):
            off = off[1]
        if not is_list(off, "i32.const"):
            raise Unsupported("elem")
        rest = rest[1:]
        if rest and rest[0] == "func":
            rest = rest[1:]
        elif rest and rest[0] == "funcref":
            rest = rest[1:]
        return table, int(off[1], 0), [self.elem_ref(r) for r in rest]

    def table_index(self, ref):
        if ref.isdigit():
            k = int(ref)
        else:
            names = [t[0] for t in self.tables]
            if ref not in names:
                raise Unsupported("table " + ref)
            k = names.index(ref)
        if k >= len(self.tables):
            raise Unsupported("table " + ref)
        return k

    def add_func(self, rest):
        name = None
        if rest and isinstance(rest[0], str) and rest[0].startswith("$"):
            name, rest = rest[0], rest[1:]
        index = len(self.funcs)
        while rest and is_list(rest[0], "export"):
            self.exports[rest[0][1][1:-1]] = index
            rest = rest[1:]
        if rest and is_list(rest[0], "import"):
            raise Unsupported("import")
        params = type_list(rest, "param")
        results = [t for _, t in type_list(rest, "result")]
        if rest and is_list(rest[0], "type") and not params and not results:
            ps, results = self.types[rest[0][1]]
            params = [(None, t) for t in ps]
        locals_ = type_list(rest, "local")
        body = [x for x in rest
                if not (is_list(x, "type") or is_list(x, "param")
                        or is_list(x, "result") or is_list(x, "local"))]
        self.funcs.append((name, params, results, locals_, body))

    def func_index(self, ref):
        if ref.isdigit():
            return int(ref)
        for i, f in enumerate(self.funcs):
            if f[0] == ref:
                return i
        raise Unsupported("function " + ref)

    def global_index(self, ref):
        if ref.isdigit():
            i = int(ref)
        else:
            i = [g[0] for g in self.globals].index(ref)
        if self.globals[i][1] is None:
            raise Unsupported("global")
        return i

    def block_type(self, items):
        """The block type at the head of `items` (a label already taken),
        and the rest of `items`."""
        ref, params, results = None, [], []
        while items and (is_list(items[0], "type") or is_list(items[0], "param")
                         or is_list(items[0], "result")):
            x = items[0]
            if x[0] == "type":
                ref = x[1]
            elif x[0] == "param":
                params += [t for _, t in type_list([x], "param")]
            else:
                results += x[1:]
            items = items[1:]
        if ref is not None and not params and not results:
            params, results = self.types[ref]
        for t in params + results:
            numtype(t)
        if not params and len(results) <= 1:
            return ("NoResult" if not results else f"Result({numtype(results[0])})"), items
        sig = (tuple(params), tuple(results))
        if sig not in self.block_types:
            self.block_types.append(sig)
        k = self.block_types.index(sig)
        return f"TypeIndex({len(self.funcs) + k})", items

    def translate(self, index):
        name, params, results, locals_, body = self.funcs[index]
        self.locals = [n for n, _ in params + locals_]
        for _, t in params + locals_:
            numtype(t)
        for t in results:
            numtype(t)
        self.calls = set()
        self.tables_used = set()
        code, rest = self.seq(body, 0, [], ())
        assert not rest, rest
        return code

    def local(self, ref):
        if ref.isdigit():
            return int(ref)
        if ref not in self.locals:
            raise Unsupported("local " + ref)
        return self.locals.index(ref)

    def label(self, ref, labels):
        if ref.isdigit():
            return int(ref)
        return len(labels) - 1 - labels.index(ref)

    def seq(self, items, i, labels, stops):
        """Instructions from items[i:], flat or folded, up to a word in
        `stops` (`end`, `else`): (code, the rest of items)."""
        code = []
        items = items[i:]
        while items:
            x = items[0]
            if isinstance(x, str) and x in stops:
                return code, items
            if is_list(x):
                code += self.folded(x, labels)
                items = items[1:]
            else:
                c, items = self.flat(items, labels)
                code += c
        return code, items

    def take_label(self, items):
        if items and isinstance(items[0], str) and items[0].startswith("$"):
            return items[0], items[1:]
        return None, items

    def flat(self, items, labels):
        op, items = items[0], items[1:]
        if op in ("block", "loop", "if"):
            lab, items = self.take_label(items)
            bt, items = self.block_type(items)
            inner = labels + [lab]
            body, items = self.seq(items, 0, inner, ("end", "else"))
            else_ = []
            if items and items[0] == "else":
                items = items[1:]
                if items and items[0] == lab:
                    items = items[1:]
                else_, items = self.seq(items, 0, inner, ("end",))
            if op != "if" and else_:
                raise Unsupported("else")
            items = items[1:]  # end
            if items and lab is not None and items[0] == lab:
                items = items[1:]
            return [self.block(op, bt, body, else_)], items
        if op == "call_indirect":
            ins, items = self.call_indirect(items)
            return [ins], items
        imms = []
        while items and isinstance(items[0], str) and (
            is_index(items[0]) or items[0].startswith("offset=")
            or items[0].startswith("align=") or re.match(r"^[-+0-9]", items[0])
        ):
            imms.append(items[0])
            items = items[1:]
            if op not in ("br_table",) and not op.endswith(("load", "store")) and \
                    not re.search(r"load|store", op):
                break
        if op == "select" and items and is_list(items[0], "result"):
            items = items[1:]
        return [self.plain(op, imms, labels)], items

    def block(self, op, bt, body, else_):
        b = "[" + ", ".join(body) + "]"
        if op == "block":
            return f"Block({bt}, {b})"
        if op == "loop":
            return f"Loop({bt}, {b})"
        return f"If({bt}, {b}, [" + ", ".join(else_) + "])"

    def folded(self, x, labels):
        op, rest = x[0], x[1:]
        if op == "call_indirect":
            ins, rest = self.call_indirect(rest)
            code = []
            for y in rest:
                code += self.folded(y, labels)
            return code + [ins]
        if op in ("block", "loop"):
            lab, rest = self.take_label(rest)
            bt, rest = self.block_type(rest)
            body, left = self.seq(rest, 0, labels + [lab], ())
            return [self.block(op, bt, body, [])]
        if op == "if":
            lab, rest = self.take_label(rest)
            bt, rest = self.block_type(rest)
            cond = []
            while rest and not (is_list(rest[0], "then") or is_list(rest[0], "else")):
                cond += self.folded(rest[0], labels)
                rest = rest[1:]
            inner = labels + [lab]
            then_, else_ = [], []
            for y in rest:
                if is_list(y, "then"):
                    then_, _ = self.seq(y[1:], 0, inner, ())
                elif is_list(y, "else"):
                    else_, _ = self.seq(y[1:], 0, inner, ())
            return cond + [self.block("if", bt, then_, else_)]
        imms = []
        while rest and isinstance(rest[0], str):
            imms.append(rest[0])
            rest = rest[1:]
        if op == "select" and rest and is_list(rest[0], "result"):
            rest = rest[1:]
        code = []
        for y in rest:
            code += self.folded(y, labels)
        return code + [self.plain(op, imms, labels)]

    def call_indirect(self, items):
        """call_indirect's table and type use at the head of `items`: (the
        instruction, the rest of items). Its type is an instance type after
        the functions' types, as a block type's."""
        table = "0"
        if items and isinstance(items[0], str) and is_index(items[0]):
            table, items = items[0], items[1:]
        ref, params, results = None, [], []
        while items and (is_list(items[0], "type") or is_list(items[0], "param")
                         or is_list(items[0], "result")):
            x = items[0]
            if x[0] == "type":
                ref = x[1]
            elif x[0] == "param":
                params += [t for _, t in type_list([x], "param")]
            else:
                results += x[1:]
            items = items[1:]
        if ref is not None:
            params, results = self.types[ref]
        for t in params + results:
            numtype(t)
        k = self.table_index(table)
        if self.table_entries[k] is None:
            raise Unsupported("a table of references")
        self.tables_used.add(k)
        sig = (tuple(params), tuple(results))
        if sig not in self.block_types:
            self.block_types.append(sig)
        j = len(self.funcs) + self.block_types.index(sig)
        return f"CallIndirect({k}, {j})", items

    def plain(self, op, imms, labels):
        if op in SIMPLE:
            return SIMPLE[op]
        if op in ("i32.const", "i64.const"):
            ty = op[:3]
            return const(ty, literal(ty, imms[0]))
        if op in ("local.get", "local.set", "local.tee"):
            k = {"local.get": "LocalGet", "local.set": "LocalSet", "local.tee": "LocalTee"}[op]
            return f"{k}({self.local(imms[0])})"
        if op in ("global.get", "global.set"):
            k = "GlobalGet" if op == "global.get" else "GlobalSet"
            return f"{k}({self.global_index(imms[0])})"
        if op == "br":
            return f"Br({self.label(imms[0], labels)})"
        if op == "br_if":
            return f"BrIf({self.label(imms[0], labels)})"
        if op == "br_table":
            if len(imms) > 1000:
                # too long a list to write out as a term
                raise Unsupported(f"a br_table of {len(imms)} labels")
            ls = [self.label(a, labels) for a in imms]
            return f"BrTable([{', '.join(map(str, ls[:-1]))}], {ls[-1]})"
        if op == "call":
            j = self.func_index(imms[0])
            self.calls.add(j)
            return f"Call({j})"
        if op in LOADS:
            if not self.memory:
                raise Unsupported("memory")
            off = 0
            for a in imms:
                if a.startswith("offset="):
                    off = int(a[len("offset="):], 0)
            return LOADS[op].format(off)
        if op in ("memory.fill", "memory.copy"):
            return {"memory.fill": "MemoryFill", "memory.copy": "MemoryCopy"}[op]
        m = re.match(r"^(i32|i64)\.([a-z0-9_]+)$", op)
        if m:
            ins = instr(m.group(1), m.group(2))
            if ins is not None:
                return ins
        raise Unsupported(op)


def value_of(x):
    if not is_list(x) or x[0] not in ("i32.const", "i64.const") or len(x) != 2:
        raise Unsupported("value")
    ty = x[0][:3]
    return value(ty, literal(ty, x[1]))


def control_cases(path):
    """The modules of `path` and the assertions on them: (modules, cases,
    counts of what was left out)."""
    file = path.split("/")[-1]
    modules, cases = [], []
    left = {"functions": 0, "assertions": 0, "slow": 0}
    current = None
    for top in sexprs(open(path).read()):
        if not is_list(top):
            continue
        if top[0] == "module":
            current = None
            if len(top) > 1 and top[1] in ("binary", "quote"):
                continue
            try:
                mod = Module(top[1:])
            except Unsupported as e:
                # its assertions are left out, and counted
                current = ("module", str(e))
                continue
            funcs, ok, deps, tdeps, why = [], [], [], [], {}
            for j, f in enumerate(mod.funcs):
                try:
                    code = mod.translate(j)
                    ps = [numtype(t) for _, t in f[1]]
                    rs = [numtype(t) for t in f[2]]
                    ls = [numtype(t) for _, t in f[3]]
                    funcs.append(f"{{ params: [{', '.join(ps)}], results: [{', '.join(rs)}], "
                                 f"locals: [{', '.join(ls)}], body: [{', '.join(code)}] }}")
                    ok.append(True)
                    deps.append(set(mod.calls))
                    tdeps.append(set(mod.tables_used))
                except Unsupported as e:
                    why[j] = str(e)
                    funcs.append("{ params: [], results: [], locals: [], body: [Unreachable] }")
                    ok.append(False)
                    deps.append(set())
                    tdeps.append(set())
                    left["functions"] += 1
            # why a function cannot run: a function it can call directly (for
            # a result), or through tables too (for a trap), was not translated
            def left_out(j, tables):
                seen, todo, bad = set(), [j], []
                while todo:
                    k = todo.pop()
                    if k in seen:
                        continue
                    seen.add(k)
                    if not ok[k]:
                        bad.append(why[k])
                    todo += list(deps[k])
                    if tables:
                        for t in tdeps[k]:
                            todo += [e for e in mod.table_entries[t] if e is not None]
                return bad
            runs = [(left_out(j, False), left_out(j, True)) for j in range(len(mod.funcs))]
            # a global the builder cannot write keeps its index, as a 0 that
            # nothing reads (global_index refuses it)
            globs = [value(t, v) if t is not None else "I32Val(0)" for _, t, v in mod.globals]
            types = [f"([{', '.join(numtype(t) for t in ps)}], [{', '.join(numtype(t) for t in rs)}])"
                     for ps, rs in mod.block_types]
            current = (len(modules), mod, runs, why)
            mem = f"Some({MEMORY_OF.get(file, MEMORY)})" if mod.memory else "None"
            tables = ", ".join(
                "[" + ", ".join("None" if e is None else f"Some({e})" for e in (es or [])) + "]"
                for es in mod.table_entries)
            modules.append(
                f'  {{ funcs: [  // {file}\n    ' + ",\n    ".join(funcs) +
                f'\n  ], types: [{", ".join(types)}], tables: [{tables}], '
                f'globals: [{", ".join(globs)}], memory: {mem} }},')
            continue
        if top[0] not in ("assert_return", "assert_trap"):
            continue
        action = top[1]
        if not is_list(action, "invoke") or current is None:
            continue
        name = action[1][1:-1]
        if current[0] == "module":
            left["assertions"] += 1
            print(f"{file}: left out {name}: its module uses {current[1]}", file=sys.stderr)
            continue
        index, mod, runs, why = current
        try:
            j = mod.exports[name]
            args = [value_of(a) for a in action[2:]]
            if top[0] == "assert_return":
                expected = "Some([" + ", ".join(value_of(r) for r in top[2:]) + "])"
            else:
                expected = "None"
            bad = runs[j][0] if top[0] == "assert_return" else runs[j][1]
            if bad:
                raise Unsupported("uses " + ", ".join(sorted(set(bad))))
        except (Unsupported, KeyError) as e:
            left["assertions"] += 1
            print(f"{file}: left out {name}: {e}", file=sys.stderr)
            continue
        first = action[2][1] if len(action) > 2 and is_list(action[2]) else None
        slow = (file, name, first) in SLOW
        if slow:
            left["slow"] += 1
        cases.append(f'  ({index}, "{file} {name}", {j}, [{", ".join(args)}], {expected}, '
                     f'{"true" if slow else "false"}),')
    return modules, cases, left


def main():
    commit, paths = sys.argv[1], sys.argv[2:]
    named = paths
    loads = [p for p in paths if "address" in p]
    numeric = [p for p in paths if re.search(r"(^|/)i(32|64)\.wast$", p)]
    control = [p for p in paths if p not in loads and p not in numeric]
    paths = numeric
    print("// Generated by tools/spec_cases.py from the WebAssembly spec testsuite")
    print(f"// (github.com/WebAssembly/testsuite @ {commit}): {', '.join(p.split('/')[-1] for p in named)}.")
    print("// Do not edit; rerun the script.")
    print()
    print("///|")
    print("/// (operator, instructions, result or None for a trap)")
    print("let spec_cases : Array[(String, Array[@wasm.Instr], @wasm.Value?)] = [")
    for p in paths:
        for line in cases(p):
            print(line)
    print("]")
    print()
    print("///|")
    print("/// address.wast's loads at address 0: (function, instructions, result),")
    print("/// in a memory of 'a'..'z' then zeros")
    print("let spec_load_cases : Array[(String, Array[@wasm.Instr], @wasm.Value?)] = [")
    for p in loads:
        for line in load_cases(p):
            print(line)
    print("]")
    modules, calls = [], []
    for p in control:
        ms, cs, left = control_cases(p)
        base = len(modules)
        modules += ms
        calls.append(f"  // {p.split('/')[-1]}: {len(cs)} assertions, {left['slow']} of them slow; "
                     f"left out: {left['assertions']} (functions the builder cannot write, "
                     f"or arguments or results that are not integers)")
        for c in cs:
            # module indices count from the first file's
            k = int(c.split(",")[0].strip()[1:])
            calls.append(f"  ({base + k}," + c.split(",", 1)[1])
    print()
    print("///|")
    print("/// The control-flow files' modules, written out")
    print("let spec_modules : Array[SpecModule] = [")
    for m in modules:
        print(m)
    print("]")
    print()
    print("///|")
    print("/// (module, assertion, function, arguments, results or None for a trap,")
    print("/// whether only the skipped test runs it)")
    print("let spec_call_cases : Array[(Int, String, Int, Array[@wasm.Value], Array[@wasm.Value]?, Bool)] = [")
    for c in calls:
        print(c)
    print("]")


main()
