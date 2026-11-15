"""Regression checks for the compiler-to-proof transcription checker."""

import unittest

from tlsf_wat_check import POP_NAME, PUSH_NAME, check_push_signature, check_pop_signature, check_take_signature, check_ensure_signature, check_free_signature, full_free, full_take, full_ensure, find_prefix, instructions, split_suffix


class InstructionsTest(unittest.TestCase):
    def test_resolves_nested_labels_and_preserves_branch_depth(self):
        self.assertEqual(
            instructions('''
                block $"#label0 #label0" (@name "#label0") (result i32)
                  if $"#label1 #label1" (@name "#label1")
                    block
                      br $"#label0 #label0" (@name "#label0")
                      br_if $"#label1 #label1" (@name "#label1")
                    end
                  end
                end
            '''),
            ["block (result i32)", "if", "block", "br 2", "br_if 1",
             "end", "end", "end"],
        )

    def test_numeric_branches_are_not_erased(self):
        self.assertEqual(instructions("br 2\nbr_if 4"), ["br 2", "br_if 4"])

    def test_unsigned_constants_default_loads_and_linker_constant(self):
        self.assertEqual(
            instructions('''
                i32.const -1
                i32.load offset=0 align=2**2
                call $moonbit.GET_DATA_SECTION_END
            '''),
            ["i32.const 4294967295", "i32.load", "i32.const d"],
        )

    def test_unknown_labels_fail(self):
        with self.assertRaisesRegex(ValueError, "unknown branch"):
            instructions("br $missing")

    def test_find_prefix_stops_before_mutation(self):
        body = instructions('''
            block $search (result i32)
              if
                i32.const 123
                br $search
              end
              i32.const 0
            end
            i32.store
        ''')
        self.assertEqual(find_prefix(body), body[:-1])
        self.assertEqual(find_prefix(body)[3], "br 1")

    def test_find_prefix_rejects_changed_boundary(self):
        for body in ([], ["i32.const 0"], ["block (result i32)", "if", "end"]):
            with self.assertRaises(ValueError):
                find_prefix(body)

    def test_push_signature_includes_native_locals(self):
        check_push_signature('(func $push (param $m i32) (result i32) (local i32 i32 i32))')
        check_push_signature('(func $push (param i32) (result i32) (local $x i32) (local $y i32) (local $z i32))')
        check_push_signature('(func $push (param $"#local0 #local0" (@name "#local0") i32) (result i32) (local i32 i32 i32))')
        for body in (
            '(func $push (param i64) (result i32) (local i32 i32 i32))',
            '(func $push (param i32) (result i32) (local i32 i32))',
            '(func $push (param i32) (result i64) (local i32 i32 i32))',
        ):
            with self.assertRaisesRegex(ValueError, "signature or locals"):
                check_push_signature(body)

    def test_split_keeps_real_push_and_stops_before_return(self):
        body = [
            "call " + POP_NAME, "local.get 0", "i32.load",
            "if", "call " + PUSH_NAME, "drop", "end",
            "i32.store", "local.get 0", "return", "end", "local.get 0",
        ]
        self.assertEqual(
            split_suffix(body),
            ["local.get 0", "i32.load", "if", "call push", "drop", "end",
             "i32.store"],
        )

    def test_split_rejects_changed_call_or_return_boundaries(self):
        body = [
            "call " + POP_NAME, "local.get 0", "i32.load", "call " + PUSH_NAME,
            "i32.store", "local.get 0", "return", "end", "local.get 0",
        ]
        for changed in (
            body[1:],
            body + ["call " + POP_NAME],
            [line for line in body if line != "call " + PUSH_NAME],
            [line for line in body if line != "return"],
            body[:-1],
            body[:2] + ["if"] + body[2:],
        ):
            with self.assertRaises(ValueError):
                split_suffix(changed)

    def test_block_results_are_not_function_results(self):
        check_pop_signature('''
            (func $pop (param i32)
              (local i32 i32 i32 i32)
              if (result i32)
                i32.const 1
              else
                i32.const 0
              end
              drop
            )
        ''')
        check_take_signature('''
            (func $take (param i32) (result i32)
              (local i32 i32 i32 i32 i32)
              block (result i32)
                i32.const 0
              end
            )
        ''')

    def test_full_free_preserves_coalescing_and_stores(self):
        body = ['i32.store', 'if', 'call ' + POP_NAME, 'i32.store', 'end',
                'if', 'call ' + POP_NAME, 'i32.store', 'end', 'call ' + PUSH_NAME]
        self.assertEqual(full_free(body),
                         ['i32.store', 'if', 'call pop', 'i32.store', 'end',
                          'if', 'call pop', 'i32.store', 'end', 'call push'])
        for changed in (body[:2] + body[3:], body + ['call ' + PUSH_NAME],
                        body[:-1], body + ['call ' + POP_NAME]):
            with self.assertRaisesRegex(ValueError, 'call count'):
                full_free(changed)

    def test_free_native_signature(self):
        check_free_signature('(func $free (param i32) (result i32) (local i32 i32))')
        for changed in (
            '(func $free (param i32) (result i32) (local i32))',
            '(func $free (param i32) (result i32) (local i32 i32 i32))',
            '(func $free (param i64) (result i32) (local i32 i32))',
            '(func $free (param i32) (local i32 i32))',
        ):
            with self.assertRaisesRegex(ValueError, 'signature or locals'):
                check_free_signature(changed)

    def test_full_ensure_preserves_growth_and_both_push_calls(self):
        body = ["memory.size", "if", "memory.grow", "call " + PUSH_NAME,
                "else", "memory.grow", "call " + POP_NAME,
                "call " + PUSH_NAME, "end", "i32.const 1"]
        expected = body.copy()
        expected[3] = expected[7] = "call push"
        expected[6] = "call pop"
        self.assertEqual(full_ensure(body), expected)
        for changed in (body[:3] + body[4:], body + ["call " + POP_NAME]):
            with self.assertRaisesRegex(ValueError, "call count"):
                full_ensure(changed)

    def test_ensure_native_signature(self):
        check_ensure_signature('(func $ensure (param i32) (result i32) (local i32))')
        for changed in (
            '(func $ensure (param i32) (result i32))',
            '(func $ensure (param i32) (result i32) (local i32 i32))',
            '(func $ensure (param i32) (local i32))',
        ):
            with self.assertRaisesRegex(ValueError, "signature or locals"):
                check_ensure_signature(changed)

    def test_full_take_links_both_helpers_and_preserves_return(self):
        body = ['block (result i32)', 'i32.const 0', 'end', 'local.tee 0',
                'if', 'local.get 0', 'call ' + POP_NAME, 'call ' + PUSH_NAME,
                'local.get 0', 'return', 'end', 'local.get 0']
        expected = body.copy()
        expected[6:8] = ['call pop', 'call push']
        self.assertEqual(full_take(body), expected)
        for changed in (body[:6] + body[7:], body + ['call ' + PUSH_NAME],
                        [line for line in body if line != 'call ' + PUSH_NAME]):
            with self.assertRaisesRegex(ValueError, 'exactly one'):
                full_take(changed)

    def test_take_and_pop_native_signatures(self):
        for check, results, nlocals in ((check_pop_signature, '', 4),
                                        (check_take_signature, '(result i32)', 5)):
            locals_ = '(local ' + ' '.join(['i32'] * nlocals) + ')'
            check('(func $f (param i32) ' + results + locals_ + ')')
            check('(func $f (param $"#local0 #local0" (@name "#local0") i32) '
                  + results + locals_ + ')')
            for changed in (
                '(func $f (param i64) ' + results + locals_ + ')',
                '(func $f (param i32) ' + results + '(local i32))',
                '(func $f (param i32) (result i32 i32)' + locals_ + ')',
            ):
                with self.assertRaisesRegex(ValueError, 'signature or locals'):
                    check(changed)


if __name__ == "__main__":
    unittest.main()
