"""Checks for the catalog's text index. These do not prove C semantics."""
import unittest
from split_catalog import mask_comments_strings, c_functions, assignment_lvalues


class CatalogIndexTests(unittest.TestCase):
    def test_comments_and_strings_do_not_become_writers(self):
        source = '/* m->pos[0] = 1;\n */\nvoid f(void) { puts("m->pos"); }'
        masked = mask_comments_strings(source)
        self.assertNotIn('m->pos', masked)
        self.assertEqual(masked.count('\n'), source.count('\n'))
        self.assertEqual([(n, line) for n, line, _, _ in c_functions(source)], [('f', 3)])

    def test_macro_return_type_is_not_omitted(self):
        source = 'static BAD_RETURN(u32) update_water_pitch(struct MarioState *m) {\n m->pos[1] += 1;\n}\n'
        spans = list(c_functions(source))
        self.assertEqual([s[0] for s in spans], ['update_water_pitch'])
        self.assertIn('m->pos[1]', spans[0][2])

    def test_preprocessor_alternative_signatures_remain_visible(self):
        source = '#if A\nfloat f(void) {\n#else\nint f(void) {\n#endif\n return 0;\n}\nvoid g(void) {}'
        spans = list(c_functions(source))
        self.assertEqual([s[0] for s in spans], ['f', 'f', 'g'])
        self.assertIn('return 0;', spans[1][2])

    def test_assignment_destination_is_separated_from_position_read(self):
        body = 'Sassign (Efield (Etempvar _m t) _vel t) (Efield x _pos t) Sassign (Ederef (Ebinop Oadd (Efield x _pos t) y t) t) z'
        lhs = list(assignment_lvalues(body))
        self.assertEqual(len(lhs), 2)
        self.assertNotIn('_pos', lhs[0])
        self.assertIn('_pos', lhs[1])

    def test_unbalanced_generated_assignment_fails_closed(self):
        with self.assertRaises(ValueError):
            list(assignment_lvalues('Sassign (Efield x _pos t'))


if __name__ == '__main__':
    unittest.main()
