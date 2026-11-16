"""Run the compiler's full Page::allocate, including dirty recycled payloads."""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tlsf_wat_check import PAGE_ALLOCATE_NAME, FIND_PARENT, FREE_NAME

ROOT = Path(__file__).resolve().parent.parent
SHIPPED = ROOT.parent / 'ideas/lib/xml/wasm_linear/tlsf-mbt.wat'


@unittest.skipUnless(SHIPPED.exists() and shutil.which('wasm-tools') and shutil.which('node'),
                     'requires the sibling compiler WAT, wasm-tools and Node')
class PageAllocateRuntimeTest(unittest.TestCase):
    def run_trace(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            wat, binary = Path(tmp) / 'page.wat', Path(tmp) / 'page.wasm'
            wat.write_text('(module\n' + SHIPPED.read_text() + f'''
              (export "memory" (memory $0))
              (export "page" (func {PAGE_ALLOCATE_NAME}))
              (export "take" (func {FIND_PARENT}))
              (export "release" (func {FREE_NAME})))''')
            subprocess.run(['wasm-tools', 'parse', str(wat), '-o', str(binary)],
                           check=True, capture_output=True)
            runner = r'''
              const fs = require('fs');
              const e = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(process.argv[1])),
                {moonbit:{DATA_SECTION_END:()=>123}}).exports;
              const insist = (x,m) => { if (!x) throw Error(m); };
              const bytes = () => new Uint8Array(e.memory.buffer);
              const word = a => new DataView(e.memory.buffer).getUint32(a,true);
              const client = e.malloc(248) >>> 0;
              bytes().fill(0xA9,client,client+248);
              bytes().fill(0x73,0,128);
              const protectedBytes = () => {
                insist(bytes().subarray(client,client+248).every(x=>x===0xA9),'old client');
                insist(bytes().subarray(0,128).every(x=>x===0x73),'static client');
              };
              let pages=0, dirty=0;
              if (process.argv[2] === 'failure') {
                while (e.take(1080)) {}
                const before=bytes().slice(), p=e.page(16) >>> 0;
                insist(p===0,'failure pointer');
                insist(Buffer.from(before).equals(Buffer.from(bytes())),'failure changed heap');
              } else {
                for (let s=8;s<=256;s+=8) {
                  const recycled=e.take(1080) >>> 0;
                  insist(recycled!==0,'fixture take');
                  const capacity=(word(recycled)&~3)>>>0;
                  bytes().fill(0xD7,recycled+8,recycled+8+capacity);
                  e.release(recycled);
                  const p=e.page(s) >>> 0;
                  insist(p===recycled,'fixture must recycle dirty block');
                  const cap=(word(p)&~3)>>>0, total=Math.floor(1056/(8+s));
                  insist((word(p)&1)!==0 && cap>=1080,'used backing');
                  insist(word(p+8)===s && word(p+12)===total,'page geometry');
                  insist(word(p+16)===0xD7D7D7D7 && word(p+24)===0xD7D7D7D7,
                    'unpublished used/prev must be preserved');
                  insist(word(p+28)===0,'next page');
                  let b=word(p+20), count=0;
                  for (let i=total-1;i>=0;i--) {
                    insist(b===p+32+(8+s)*i,'reversed local list');
                    insist(word(b)===4 && word(b+4)===p,'slot tag/owner');
                    const next=word(b+8);
                    insist(next===(i===0?0:p+32+(8+s)*(i-1)),'slot next');
                    insist(bytes().subarray(b+12,b+8+s).every(x=>x===0xD7),'slot spare');
                    b=next;count++;
                  }
                  insist(b===0 && count===total,'exact slot coverage');
                  insist(bytes().subarray(p+32+(8+s)*total,p+8+cap).every(x=>x===0xD7),
                    'untouched suffix');
                  protectedBytes(); pages++; dirty++;
                }
              }
              protectedBytes(); console.log(JSON.stringify({pages,dirty}));
            '''
            result = subprocess.run(['node', '-e', runner, str(binary), mode],
                                    check=True, capture_output=True, text=True)
            return json.loads(result.stdout)

    def test_every_size_class_initializes_exactly_the_slots_on_dirty_memory(self):
        self.assertEqual(self.run_trace('success'), {'pages': 32, 'dirty': 32})

    def test_failed_take_returns_zero_without_changing_any_heap_byte(self):
        self.assertEqual(self.run_trace('failure')['pages'], 0)


if __name__ == '__main__':
    unittest.main()
