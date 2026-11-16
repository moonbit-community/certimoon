"""Execute the transcribed initializer and push in a real WebAssembly engine.

These byte-for-byte checks complement the HOL proofs. They require wasm-tools
and Node; no compiler checkout or network access is needed.
"""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tlsf_wat_check import instructions, listed

ROOT = Path(__file__).resolve().parent.parent


@unittest.skipUnless(shutil.which('wasm-tools') and shutil.which('node'),
                     'requires wasm-tools and Node')
class InitializeRuntimeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Execute exactly the programs printed in the kernel-replayed listing.
        md = (ROOT / 'tlsf/__snapshot__/theory.md').read_text()
        cls.initialize = '\n'.join(instructions(listed(md, 'tlsf_initialize_code')))
        cls.push = '\n'.join(instructions(listed(md, 'tlsf_push_code')))

    def run_initializer(self, data_end, initial, maximum, *, failure=False):
        def linked(code):
            return code.replace('i32.const d', f'i32.const {data_end}').replace(
                'call push', 'call $push')
        wat = f'''(module
          (memory (export "memory") {initial} {maximum})
          (func $push (param i32) (result i32) (local i32 i32 i32)
            {linked(self.push)})
          (func (export "initialize") (local i32 i32 i32)
            {linked(self.initialize)}))'''
        with tempfile.TemporaryDirectory() as tmp:
            module = Path(tmp) / 'initialize.wat'
            binary = Path(tmp) / 'initialize.wasm'
            module.write_text(wat)
            subprocess.run(['wasm-tools', 'parse', str(module), '-o', str(binary)],
                           check=True, capture_output=True)
            runner = r'''
              const fs = require('fs');
              const [path, d, failure] = process.argv.slice(1);
              const dataEnd = Number(d), base = Math.ceil(dataEnd / 16) * 16;
              const {exports: e} = new WebAssembly.Instance(
                new WebAssembly.Module(fs.readFileSync(path)));
              let memory = new Uint8Array(e.memory.buffer);
              for (let i = 0; i < base; i++) memory[i] = (i * 19 + 7) & 255;
              const old = memory.slice();
              let trapped = false;
              try { e.initialize(); }
              catch (err) {
                if (!(err instanceof WebAssembly.RuntimeError)) throw err;
                trapped = true;
              }
              memory = new Uint8Array(e.memory.buffer);
              const wantFailure = failure === 'true';
              if (trapped !== wantFailure) throw Error('unexpected trap outcome');
              let expected;
              if (wantFailure) {
                expected = old;
              } else {
                const pages = Math.floor(base / 65536) +
                  Math.floor(((base % 65536) + 67743) / 65536);
                const size = Math.max(old.length, pages * 65536);
                if (memory.length !== size) throw Error('wrong memory length');
                expected = new Uint8Array(size);
                expected.set(old.subarray(0, base));
                const words = new DataView(expected.buffer);
                const m = base + 2176, capacity = size - m - 8;
                const f = 31 - Math.clz32(capacity) - 4;
                const j = (capacity >>> f) & 15;
                words.setUint32(base, 1 << f, true);
                words.setUint32(base + 4 + 68 * f, 1 << j, true);
                words.setUint32(base + 8 + 68 * f + 4 * j, m, true);
                words.setUint32(base + 1908, m, true);
                words.setUint32(m, capacity | 2, true);
              }
              if (memory.length !== expected.length) throw Error('changed size');
              for (let i = 0; i < expected.length; i++) {
                if (memory[i] !== expected[i]) throw Error('wrong byte at ' + i);
              }
              console.log(JSON.stringify({trapped, bytes: memory.length}));
            '''
            result = subprocess.run(
                ['node', '-e', runner, str(binary), str(data_end),
                 str(failure).lower()], check=True, capture_output=True, text=True)
            return json.loads(result.stdout)

    def test_existing_page_preserves_clients_and_all_unwritten_bytes(self):
        self.assertEqual(self.run_initializer(123, 1, 4),
                         {'trapped': False, 'bytes': 65536})

    def test_exact_page_boundary_needs_no_growth(self):
        self.assertEqual(self.run_initializer(63328, 1, 4),
                         {'trapped': False, 'bytes': 65536})

    def test_alignment_crosses_page_boundary_and_grows(self):
        self.assertEqual(self.run_initializer(63329, 1, 4),
                         {'trapped': False, 'bytes': 131072})

    def test_metadata_entirely_in_new_page(self):
        self.assertEqual(self.run_initializer(65536, 1, 4),
                         {'trapped': False, 'bytes': 131072})

    def test_growth_failure_traps_before_any_write(self):
        self.assertEqual(self.run_initializer(63329, 1, 1, failure=True),
                         {'trapped': True, 'bytes': 65536})

    def test_empty_initial_memory_can_grow(self):
        self.assertEqual(self.run_initializer(0, 0, 1),
                         {'trapped': False, 'bytes': 65536})


if __name__ == '__main__':
    unittest.main()
