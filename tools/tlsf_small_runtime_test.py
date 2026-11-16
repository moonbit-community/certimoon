"""Exercise the small-page invariant against the compiler's actual allocator.

The optional integration fixture is the sibling compiler checkout used by the
WAT transcription checker. Kernel proofs and MoonBit tests do not require it.
"""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SHIPPED = ROOT.parent / 'ideas/lib/xml/wasm_linear/tlsf-mbt.wat'


@unittest.skipUnless(SHIPPED.exists() and shutil.which('wasm-tools') and shutil.which('node'),
                     'requires the sibling compiler WAT, wasm-tools and Node')
class SmallPageRuntimeTest(unittest.TestCase):
    def run_trace(self, mode):
        with tempfile.TemporaryDirectory() as directory:
            wat = Path(directory) / 'allocator.wat'
            binary = Path(directory) / 'allocator.wasm'
            wat.write_text('(module\n' + SHIPPED.read_text() +
                           '\n(export "memory" (memory $0)))')
            subprocess.run(['wasm-tools', 'parse', str(wat), '-o', str(binary)],
                           check=True, capture_output=True)
            runner = r'''
              const fs = require('fs');
              const moduleBytes = fs.readFileSync(process.argv[1]);
              const mode = process.argv[2];
              const e = new WebAssembly.Instance(new WebAssembly.Module(moduleBytes), {
                moonbit: { DATA_SECTION_END: () => 123 }
              }).exports;
              const base = 128, table = base + 1912;
              const live = new Map();
              let operations = 0, witnessedPartial = false, witnessedPinned = false;
              function insist(test, message) { if (!test) throw Error(message); }
              function check() {
                const bytes = new Uint8Array(e.memory.buffer);
                const data = new DataView(e.memory.buffer);
                const word = a => data.getUint32(a, true);
                const freeMemories = new Set(), usedMemories = new Set();
                let m = base + 2176, prev = 0, previousFree = false;
                for (;;) {
                  const header = word(m), size = (header & ~3) >>> 0;
                  insist(size >= 16 && size % 8 === 0, 'physical size');
                  insist(word(m + 4) === prev, 'physical previous');
                  insist(m + 8 + size <= bytes.length, 'physical bounds');
                  if (header & 1) { usedMemories.add(m); previousFree = false; }
                  else {
                    insist(!previousFree, 'uncoalesced memories');
                    freeMemories.add(m); previousFree = true;
                  }
                  if (header & 2) {
                    insist(m === word(base + 1908), 'top pointer');
                    insist(m + 8 + size === bytes.length, 'last endpoint');
                    break;
                  }
                  prev = m; m += 8 + size;
                }
                const listedMemories = new Set();
                let fl = 0;
                for (let f = 0; f < 28; f++) {
                  let sl = 0;
                  for (let j = 0; j < 16; j++) {
                    let m = word(base + 8 + 68 * f + 4 * j), prev = 0;
                    if (m) sl |= 1 << j;
                    while (m) {
                      insist(!listedMemories.has(m), 'duplicate TLSF memory');
                      listedMemories.add(m);
                      insist(freeMemories.has(m), 'TLSF lists used memory');
                      const size = (word(m) & ~3) >>> 0;
                      const level = 31 - Math.clz32(size) - 4;
                      insist(level === f && ((size >>> f) & 15) === j, 'TLSF class');
                      insist(word(m + 8) === prev, 'TLSF back link');
                      prev = m; m = word(m + 12);
                    }
                  }
                  insist(word(base + 4 + 68 * f) === sl, 'second bitmap');
                  if (sl) fl |= 1 << f;
                }
                insist(word(base) === fl, 'first bitmap');
                insist(listedMemories.size === freeMemories.size, 'missing TLSF memory');
                const pages = new Set(), seen = new Set(), partial = new Set();
                const liveCounts = new Map(), cachedCounts = new Map(), largeClients = new Set();
                const increment = (map, p) => map.set(p, (map.get(p) || 0) + 1);
                function slot(b, expectedClass) {
                  insist(!seen.has(b), 'duplicate small slot'); seen.add(b);
                  insist(word(b) === 4, 'small tag');
                  const p = word(b + 4), size = word(p + 8), total = word(p + 12);
                  insist(usedMemories.has(p), 'page is not a used TLSF memory');
                  insist(size >= 8 && size <= 256 && size % 8 === 0, 'page size');
                  if (expectedClass !== undefined) insist(size === expectedClass * 8, 'small class');
                  const offset = b - p - 32;
                  insist(offset >= 0 && offset % (8 + size) === 0, 'slot alignment');
                  insist(offset / (8 + size) < total, 'slot outside page');
                  pages.add(p); return p;
                }
                for (const [ptr, item] of live) {
                  if (item.size > 256) {
                    const m = ptr - 8;
                    insist(usedMemories.has(m), 'large client is not used');
                    insist(ptr + item.size <= m + 8 + ((word(m) & ~3) >>> 0), 'large client bounds');
                    largeClients.add(m);
                  } else {
                    const p = slot(ptr - 8); increment(liveCounts, p);
                    insist(ptr + item.size <= p + 8 + ((word(p) & ~3) >>> 0), 'client bounds');
                  }
                  for (let i = 0; i < item.size; i++) {
                    insist(bytes[ptr + i] === item.pattern, 'client byte changed');
                  }
                }
                for (let j = 0; j < 33; j++) {
                  let b = word(table + 8 * j);
                  while (b) { const p = slot(b,j); increment(cachedCounts,p); b = word(b + 8); }
                  let p = word(table + 8 * j + 4), prev = 0;
                  while (p) {
                    insist(!partial.has(p), 'duplicate partial page'); partial.add(p); pages.add(p);
                    insist(word(p + 8) === j * 8, 'partial class');
                    insist(word(p + 24) === prev, 'partial back link');
                    prev = p; p = word(p + 28);
                  }
                }
                for (const p of pages) {
                  insist(usedMemories.has(p), 'partial page not used');
                  const size = word(p + 8), total = word(p + 12), used = word(p + 16);
                  insist(((word(p) & ~3) >>> 0) >= 1080, 'page capacity');
                  insist(total === Math.floor(1056 / (8 + size)), 'page total');
                  insist(used > 0 && used <= total, 'stable used count');
                  insist(partial.has(p) === (used < total), 'partial iff non-full');
                  if (partial.has(p)) witnessedPartial = true;
                  let local = 0, b = word(p + 20);
                  while (b) { insist(slot(b) === p, 'local owner'); local++; b = word(b + 8); }
                  insist(used === (liveCounts.get(p) || 0) + (cachedCounts.get(p) || 0), 'used accounting');
                  insist(total === used + local, 'local accounting');
                  if (!liveCounts.get(p) && cachedCounts.get(p)) witnessedPinned = true;
                }
                insist(pages.size + largeClients.size === usedMemories.size, 'missing used allocation');
                for (let i = 0; i < base; i++) insist(bytes[i] === 0xA7, 'static/client prefix');
                operations++;
              }
              new Uint8Array(e.memory.buffer).fill(0xA7,0,base);
              let serial = 0;
              function allocate(size) {
                const ptr = e.malloc(size) >>> 0;
                insist(ptr !== 0 && ptr !== 0xFFFFFFFF, 'allocation failed');
                for (const [other,item] of live) {
                  insist(ptr + size <= other || other + item.size <= ptr, 'overlapping clients');
                }
                const pattern = (++serial % 254) + 1;
                new Uint8Array(e.memory.buffer).fill(pattern,ptr,ptr + size);
                live.set(ptr,{size,pattern}); check(); return ptr;
              }
              function release(ptr) { e.free(ptr); live.delete(ptr); check(); }
              if (mode === 'block_free') {
                const guardian = allocate(8), largeGuardian = allocate(600);
                for (const order of [[2,0,1,4,3],[0,1,2,3,4]]) {
                  const groups = Array.from({length:5},()=>Array.from({length:4},()=>allocate(256)));
                  const owners = groups.map(g=>new DataView(e.memory.buffer).getUint32(g[0]-4,true));
                  groups.forEach(g=>release(g.shift())); // full -> partial, nonempty insertion
                  for (const j of order) {
                    const p = owners[j];
                    groups[j].forEach(release);
                    // Reclamation must remove the page from the physical chain's used set.
                    const data = new DataView(e.memory.buffer);
                    let m=base+2176;
                    for (;;) {
                      const h=data.getUint32(m,true), size=(h&~3)>>>0;
                      insist(m!==p || !(h&1),'empty page still used');
                      if (h&2) break;
                      m+=8+size;
                    }
                  }
                }
                release(largeGuardian);
                release(guardian);
              } else if (mode === 'transitions') {
                const first = allocate(256); release(first); // cached slots pin this page
                const all = Array.from({length:4},() => allocate(256));
                release(all.pop()); all.push(allocate(256)); // partial-page transfer
                all.forEach(release);
                for (let j = 1; j < 33; j++) { const p = allocate(j * 8); release(p); }
              } else {
                let state = 0xC0FFEE;
                for (let i = 0; i < 180; i++) {
                  state = (Math.imul(state,1664525) + 1013904223) >>> 0;
                  if (live.size && (state & 3) === 0) {
                    release(Array.from(live.keys())[state % live.size]);
                  } else { allocate(1 + state % 256); }
                }
                Array.from(live.keys()).forEach(release);
              }
              console.log(JSON.stringify({operations,witnessedPartial,witnessedPinned}));
            '''
            result = subprocess.run(['node', '-e', runner, str(binary), mode],
                                    check=True, capture_output=True, text=True)
            return json.loads(result.stdout)

    def test_cached_partial_full_and_reclaimed_page_transitions(self):
        result = self.run_trace('transitions')
        self.assertTrue(result['witnessedPartial'])
        self.assertTrue(result['witnessedPinned'])
        self.assertGreater(result['operations'], 70)

    def test_block_free_all_partial_positions_reclaim_and_coalesce(self):
        self.assertGreater(self.run_trace('block_free')['operations'], 80)

    def test_mixed_trace_preserves_client_bytes_and_exact_slot_ownership(self):
        self.assertGreater(self.run_trace('mixed')['operations'], 200)


if __name__ == '__main__':
    unittest.main()
