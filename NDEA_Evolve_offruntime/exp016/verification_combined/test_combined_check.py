"""Generator tests do not establish Lean proof acceptance."""
import unittest
from combined_check import generate, transform, code_only

class GeneratorTests(unittest.TestCase):
    def source(self, name='a'):
        return 'import Mathlib\nnoncomputable section\nnamespace Example\ntheorem '+name+' : True := by trivial\nend Example\n'
    def test_qualified_catalog(self):
        source,data=generate([('A',self.source())])
        self.assertEqual(data['public_theorems'],['Example.a'])
        self.assertEqual(data['sources'][0]['implicit_eof_sections'],1)
        self.assertIn('theorem a : True := by trivial',source)
    def test_module_tactic_not_module_command(self):
        source=self.source().replace('by trivial','by\n  module')
        self.assertIn('  module',generate([('A',source)])[0])
    def test_real_module_command_rejected(self):
        with self.assertRaisesRegex(ValueError,'Unsupported import/module'):
            generate([('A','module\n'+self.source())])
    def test_import_order(self):
        b=self.source('b').replace('import Mathlib','import A')
        source,data=generate([('A',self.source()),('B',b)])
        self.assertEqual(data['public_theorems'],['Example.a','Example.b'])
        self.assertNotIn('\nimport A\n',source)
    def test_missing_import_rejected(self):
        with self.assertRaisesRegex(ValueError,'out-of-order'):
            generate([('A',self.source().replace('Mathlib','Missing'))])
    def test_comments_not_declarations(self):
        source='/- namespace Bogus /- axiom evil : False -/ theorem fake : False -/\n'+self.source()
        self.assertEqual(generate([('A',source)])[1]['public_theorems'],['Example.a'])
    def test_strings_masked(self):
        self.assertNotIn('sorry',code_only('#check "sorry"\n'))
    def test_private_theorem_not_public_catalog(self):
        source=self.source().replace('theorem a','private theorem hidden')+self.source('b')
        self.assertEqual(generate([('A',source)])[1]['public_theorems'],['Example.b'])
    def test_duplicate_public_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate public'):
            generate([('A',self.source()),('B',self.source())])
    def test_unclosed_namespace_rejected(self):
        with self.assertRaisesRegex(ValueError,'Unclosed named'):
            generate([('A',self.source().replace('end Example',''))])
    def test_mismatched_end_rejected(self):
        with self.assertRaisesRegex(ValueError,'Mismatched named'):
            generate([('A',self.source().replace('end Example','end Wrong'))])
    def test_proof_escape_rejected(self):
        for token in ['sorry','admit','native_decide']:
            with self.subTest(token=token),self.assertRaisesRegex(ValueError,'proof escape'):
                generate([('A',self.source().replace('trivial',token))])
    def test_exact_body_preservation(self):
        original=self.source()+'#print axioms Example.a\n'
        source,_,_,record=transform(original,'A',set())
        self.assertIn(original.split('noncomputable section',1)[1].split('#print')[0],source)
        self.assertEqual([x['kind'] for x in record['removed_directives']],['import','diagnostic'])
    def test_deterministic(self):
        self.assertEqual(generate([('A',self.source())]),generate([('A',self.source())]))
    def test_unterminated_comment(self):
        with self.assertRaisesRegex(ValueError,'Unterminated comment'):code_only('/- bad')
    def test_unsupported_multiline_diagnostic(self):
        with self.assertRaisesRegex(ValueError,'Unsupported diagnostic'):
            generate([('A',self.source()+'#eval 1 + 1\n')])

if __name__=='__main__':unittest.main()
