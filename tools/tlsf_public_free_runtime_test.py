"""Byte checks for the complete shipped public free on consistent allocator heaps."""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SHIPPED = ROOT.parent / 'ideas/lib/xml/wasm_linear/tlsf-mbt.wat'


@unittest.skipUnless(SHIPPED.exists() and shutil.which('wasm-tools') and shutil.which('node'),
                     'requires sibling compiler WAT, wasm-tools and Node')
class PublicFreeRuntimeTest(unittest.TestCase):
    def run_case(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            wat = Path(tmp) / 'public-free.wat'
            binary = Path(tmp) / 'public-free.wasm'
            wat.write_text('(module\n' + SHIPPED.read_text() +
                           '\n(export "memory" (memory $0)))')
            subprocess.run(['wasm-tools', 'parse', str(wat), '-o', str(binary)],
                           check=True, capture_output=True)
            script = r'''
              const fs = require('fs');
              const e = new WebAssembly.Instance(new WebAssembly.Module(
                fs.readFileSync(process.argv[1])), {
                  moonbit: {DATA_SECTION_END: () => 0}
                }).exports;
              const mode = process.argv[2];
              const bytes = new Uint8Array(e.memory.buffer);
              for (let i = 0; i < bytes.length; i++) bytes[i] = (i * 37 + 11) & 255;
              bytes.fill(0, 0, 2176); // all bin and small-page heads initially empty
              const words = new DataView(bytes.buffer);
              const put = (a, x) => words.setUint32(a, x, true);
              function bin(m, size) {
                const f = 31 - Math.clz32(size) - 4, j = (size >>> f) & 15;
                put(0, words.getUint32(0, true) | (1 << f));
                put(4 + 68 * f, words.getUint32(4 + 68 * f, true) | (1 << j));
                put(8 + 68 * f + 4 * j, m);
                put(m + 8, 0); put(m + 12, 0);
              }
              let pointer, updates, survivor;
              if (mode === 'large') {
                // A live client, a free neighbour, another live client, then top.
                const m = 2176, r = m + 24, n = r + 24, top = n + 24;
                put(m, 17); put(m + 4, 0);
                put(r, 16); put(r + 4, m);
                put(n, 17); put(n + 4, r);
                const cap = bytes.length - top - 8;
                put(top, cap | 2); put(top + 4, n); put(1908, top);
                bin(r, 16); bin(top, cap);
                pointer = m + 8; survivor = [n + 8, 16];
                const oldFl = words.getUint32(0, true);
                updates = [[m, 40], [n + 4, m], [m + 8, 0], [m + 12, 0],
                           [0, (oldFl & ~1) | 2], [4, 0], [8, 0], [72, 16], [92, m]];
              } else {
                const p = 2176, top = p + 8 + 1080, b = p + 32;
                put(p, 1081); put(p + 4, 0);
                const cap = bytes.length - top - 8;
                put(top, cap | 2); put(top + 4, p); put(1908, top); bin(top, cap);
                put(p + 8, 8); put(p + 12, 66); put(p + 16, 2); put(p + 20, b + 32);
                put(p + 24, 0); put(p + 28, 0); put(1916 + 8, p);
                for (let i = 0; i < 66; i++) {
                  const slot = b + 16 * i;
                  put(slot, 4); put(slot + 4, p);
                  if (i >= 2) put(slot + 8, i === 65 ? 0 : slot + 16);
                }
                pointer = b + 8; survivor = [b + 16 + 8, 8];
                updates = [[b + 8, b + 32], [p + 20, b], [p + 16, 1]];
              }
              const old = bytes.slice(), expected = old.slice();
              const expectedWords = new DataView(expected.buffer);
              for (const [a, x] of updates) expectedWords.setUint32(a, x, true);
              const result = e.free(pointer);
              if (result !== undefined) throw Error('public free returned a value');
              if (e.memory.buffer.byteLength !== old.length) throw Error('changed memory length');
              for (let i = 0; i < old.length; i++) {
                if (bytes[i] !== expected[i]) throw Error(mode + ': wrong byte at ' + i);
              }
              for (let i = survivor[0]; i < survivor[0] + survivor[1]; i++) {
                if (bytes[i] !== old[i]) throw Error('surviving client changed');
              }
              console.log(JSON.stringify({bytes: bytes.length, unit: true}));
            '''
            run = subprocess.run(['node', '-e', script, str(binary), mode],
                                 check=True, capture_output=True, text=True)
            return json.loads(run.stdout)

    def test_large_coalescing_preserves_other_client_and_unwritten_bytes(self):
        self.assertEqual(self.run_case('large'), {'bytes': 65536, 'unit': True})

    def test_small_release_preserves_other_client_and_unwritten_bytes(self):
        self.assertEqual(self.run_case('small'), {'bytes': 65536, 'unit': True})


if __name__ == '__main__':
    unittest.main()
