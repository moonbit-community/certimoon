"""Lazy startup, growth and failure against the compiler's allocator WAT."""

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
class MallocStartupRuntimeTest(unittest.TestCase):
    def run_case(self, data_end, initial, maximum, request, *, full=False, outcome='success'):
        fields = SHIPPED.read_text().replace('(memory $0 1)',
                                             f'(memory $0 {initial} {maximum})')
        with tempfile.TemporaryDirectory() as tmp:
            wat, wasm = Path(tmp) / 'start.wat', Path(tmp) / 'start.wasm'
            wat.write_text('(module\n' + fields + '\n(export "memory" (memory $0)))')
            subprocess.run(['wasm-tools', 'parse', str(wat), '-o', str(wasm)],
                           check=True, capture_output=True)
            script = r'''
              const fs = require('fs');
              const [path, d, size, full, outcome] = process.argv.slice(1);
              const base = Math.ceil(Number(d) / 16) * 16, request = Number(size);
              const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path)), {
                moonbit: {DATA_SECTION_END: () => Number(d)}
              }).exports;
              const insist = (p, why) => { if (!p) throw Error(why); };
              let bytes = new Uint8Array(e.memory.buffer);
              for (let i = 0; i < Math.min(base, bytes.length); i++) bytes[i] = (i * 29 + 13) & 255;
              const before = bytes.slice(), clients = [];
              const allocate = full === 'true' ? e.full_malloc : e.malloc_no_grow;
              let trapped = false, ptr;
              try { ptr = allocate(request) >>> 0; }
              catch (error) {
                if (!(error instanceof WebAssembly.RuntimeError)) throw error;
                trapped = true;
              }
              bytes = new Uint8Array(e.memory.buffer);
              insist(trapped === outcome.startsWith('trap'), 'trap outcome');
              for (let i = 0; i < Math.min(base, before.length); i++) {
                insist(bytes[i] === before[i], 'static/client byte changed: ' + i);
              }
              if (request === 0 || outcome === 'trap-initialize') {
                insist(bytes.length === before.length, 'early exit grew');
                insist(Buffer.from(bytes).equals(Buffer.from(before)), 'early exit changed heap');
                if (!trapped) insist(ptr === 0, 'zero result');
              } else {
                if (!trapped && outcome === 'no-fit') insist(ptr === 0xFFFFFFFF, 'no-fit sentinel');
                function check() {
                  bytes = new Uint8Array(e.memory.buffer);
                  const words = new DataView(e.memory.buffer);
                  const word = a => words.getUint32(a, true);
                  const free = new Set(), used = new Set(), listed = new Set();
                  let m = base + 2176, prev = 0, previousFree = false;
                  for (;;) {
                    const hdr = word(m), cap = (hdr & ~3) >>> 0;
                    insist(cap >= 16 && cap % 8 === 0 && m + 8 + cap <= bytes.length, 'physical size');
                    insist(word(m + 4) === prev, 'physical predecessor');
                    if (hdr & 1) { used.add(m); previousFree = false; }
                    else { insist(!previousFree, 'uncoalesced chain'); free.add(m); previousFree = true; }
                    if (hdr & 2) {
                      insist(m === word(base + 1908) && m + 8 + cap === bytes.length, 'top');
                      break;
                    }
                    prev = m; m += cap + 8;
                  }
                  let fl = 0;
                  for (let f = 0; f < 28; f++) {
                    let sl = 0;
                    for (let j = 0; j < 16; j++) {
                      let m = word(base + 8 + 68 * f + 4 * j), prev = 0;
                      if (m) sl |= 1 << j;
                      while (m) {
                        insist(free.has(m) && !listed.has(m), 'free memory membership'); listed.add(m);
                        const cap = (word(m) & ~3) >>> 0;
                        insist(31 - Math.clz32(cap) - 4 === f && ((cap >>> f) & 15) === j, 'bin class');
                        insist(word(m + 8) === prev, 'free predecessor'); prev = m; m = word(m + 12);
                      }
                    }
                    insist(word(base + 4 + 68 * f) === sl, 'second bitmap'); if (sl) fl |= 1 << f;
                  }
                  insist(word(base) === fl && free.size === listed.size, 'complete bins');
                  for (const [p, n, pattern] of clients) {
                    insist(p !== 0 && p !== 0xFFFFFFFF && p + n <= bytes.length, 'client bounds');
                    const m = n > 256 ? p - 8 : word(p - 4);
                    insist(used.has(m), 'client backing is not in use');
                    if (n <= 256) {
                      insist(word(p - 8) === 4 && word(m + 8) >= n, 'small client capacity');
                      insist((p - 8 - m - 32) % (8 + word(m + 8)) === 0, 'small client slot');
                    } else insist(((word(m) & ~3) >>> 0) >= n, 'large client capacity');
                    for (let i = 0; i < n; i++) insist(bytes[p + i] === pattern, 'live client byte changed');
                  }
                  for (let i = 0; i < Math.min(base, before.length); i++) insist(bytes[i] === before[i], 'client frame');
                }
                if (!trapped && outcome === 'success') {
                  insist(ptr !== 0 && ptr !== 0xFFFFFFFF && ptr + request <= bytes.length, 'allocated bounds');
                  bytes.fill(71, ptr, ptr + request); clients.push([ptr, request, 71]); check();
                  // The next call must see published metadata and retain the first client.
                  const p2 = e.full_malloc(8) >>> 0;
                  bytes = new Uint8Array(e.memory.buffer);
                  insist(p2 + 8 <= ptr || ptr + request <= p2, 'overlapping allocations');
                  bytes.fill(93, p2, p2 + 8); clients.push([p2, 8, 93]); check();
                  e.free(ptr); clients.shift(); check(); e.free(p2); clients.shift(); check();
                } else check();
              }
              console.log(JSON.stringify({trapped, bytes: e.memory.buffer.byteLength, ptr}));
            '''
            result = subprocess.run(['node', '-e', script, str(wasm), str(data_end),
                                     str(request), str(full).lower(), outcome],
                                    check=True, capture_output=True, text=True)
            return json.loads(result.stdout)

    def test_zero_never_initializes_or_grows(self):
        for full in (False, True):
            for d, initial in ((123, 1), (65536, 1), (0, 0)):
                with self.subTest(full=full, d=d):
                    self.assertEqual(self.run_case(d, initial, initial, 0, full=full)['ptr'], 0)

    def test_existing_memory_small_and_large(self):
        for full in (False, True):
            for request in (1, 8, 255, 256, 257, 1080, 8192):
                with self.subTest(full=full, request=request):
                    self.assertFalse(self.run_case(123, 1, 4, request, full=full)['trapped'])

    def test_guard_skips_out_of_bounds_load_then_initializes(self):
        for full in (False, True):
            for d, initial in ((65536, 1), (65520, 1), (0, 0)):
                with self.subTest(full=full, d=d):
                    self.assertGreater(self.run_case(d, initial, 4, 8, full=full)['bytes'], initial * 65536)

    def test_initial_growth_failure_preserves_entire_heap(self):
        for full in (False, True):
            self.assertTrue(self.run_case(0, 0, 0, 8, full=full,
                                          outcome='trap-initialize')['trapped'])
            for d in (63329, 65520, 65536):
                with self.subTest(full=full, d=d):
                    self.assertTrue(self.run_case(d, 1, 1, 8, full=full, outcome='trap-initialize')['trapped'])

    def test_try_no_fit_keeps_initialized_allocator(self):
        self.assertEqual(self.run_case(63328, 1, 1, 8, outcome='no-fit')['bytes'], 65536)
        self.assertEqual(self.run_case(123, 1, 1, 100000, outcome='no-fit')['ptr'], 0xFFFFFFFF)
        self.assertEqual(self.run_case(123, 1, 1, 4160749568, outcome='no-fit')['ptr'], 0xFFFFFFFF)

    def test_full_initialization_then_growth_and_retry(self):
        for d, request in ((63328, 8), (63328, 257), (123, 100000), (65536, 200000)):
            with self.subTest(d=d, request=request):
                self.assertGreater(self.run_case(d, 1, 8, request, full=True)['bytes'], 65536)

    def test_full_growth_failure_after_successful_initialization(self):
        for d, request, maximum in ((63328, 8, 1), (123, 100000, 1),
                                    (123, 4160749568, 1), (65536, 200000, 2)):
            with self.subTest(d=d):
                result = self.run_case(d, 1, maximum, request, full=True, outcome='trap-ensure')
                self.assertTrue(result['trapped'])
                self.assertEqual(result['bytes'], maximum * 65536)


if __name__ == '__main__':
    unittest.main()
