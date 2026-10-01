#!/usr/bin/env python3
"""Check generator def-use and reserved encodings before kernel site validation."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / 'syi'))
import alu_classes as alu
from disasm_to_sites import classify
from disasm_to_segment import Instr, DraftBuilder


def word(op, f3, top, rd=21, rs1=21, rs2=23):
    return op | rd << 7 | f3 << 12 | rs1 << 15 | rs2 << 20 | top << 25


class AluClasses(unittest.TestCase):
    def test_shift_high_bit_and_reserved(self):
        for f3, top, name in [(1, 0, 'slli'), (5, 0, 'srli'), (5, 32, 'srai')]:
            w = word(0x13, f3, top | 1, rs2=31)
            cls, fields = alu.classify(w)
            self.assertEqual((cls, fields), (name, [21, 21, '3f']))
            self.assertIsNone(alu.classify(word(0x13, f3, top | 2)))
        self.assertIsNone(alu.classify(word(0x13, 1, 32)))

    def test_word_shift_width(self):
        for f3, top, name in [(1, 0, 'slliw'), (5, 0, 'srliw'), (5, 32, 'sraiw')]:
            self.assertEqual(alu.classify(word(0x1b, f3, top, rs2=31)),
                             (name, [21, 21, '1f']))
            self.assertIsNone(alu.classify(word(0x1b, f3, top | 1)))
        self.assertIsNone(alu.classify(word(0x1b, 1, 32)))

    def test_x0_and_duplicate_sources(self):
        self.assertIsNone(alu.classify(word(0x3b, 0, 0, rd=0)))
        self.assertEqual(alu.reads('addw', ['21', '21', '21']), [21])
        self.assertEqual(alu.reads('addw', ['21', '0', '21']), [21])
        self.assertEqual(alu.reads('slli', ['21', '0', '3f']), [])
        self.assertEqual(alu.reads('andi', ['21', '21', 'fff']), [21])

    def test_upper_immediate_pc_and_sources(self):
        for opcode, name in [(0x17, 'auipc'), (0x37, 'lui')]:
            w = (0x80001 << 12) | (21 << 7) | opcode
            cls, fields = alu.classify(w)
            self.assertEqual((cls, fields), (name, [21, '80001']))
            self.assertEqual(alu.reads(cls, fields), [])
            row, = classify(0x80002000, w, '', {})
            ins = Instr(row.addr, row.word, row.cls, list(map(str, row.ops)), '')
            self.assertEqual(ins.reads(), [])
            self.assertEqual(ins.writes(), 21)
            self.assertIn('0x80001#20', ins.raw_val())
            if name == 'auipc':
                self.assertIn('0x80002000#64', ins.raw_val())
                with self.assertRaises(ValueError):
                    alu.value(cls, fields)
            self.assertIsNone(alu.classify(w & ~(31 << 7)))

    def test_rewrite_tracking(self):
        words = [word(0x13, 1, 0, rs2=1), word(0x13, 7, 0, rs2=2)]
        instrs = []
        for i, w in enumerate(words):
            row, = classify(0x80000000 + 4*i, w, '', {})
            instrs.append(Instr(row.addr, row.word, row.cls, list(map(str, row.ops)), ''))
        draft = DraftBuilder(instrs, '', 'Pins').build('test', [])
        self.assertEqual([p['reg'] for p in draft['pins']], ['x21'])
        for step in draft['steps']:
            self.assertEqual(step['class'], 'alu')
            self.assertIn('$pin:x21', step['call'])
            self.assertEqual(step['rd'], 'x21')
        self.assertIn('shift_bits_left', draft['steps'][0]['raw_val'])
        self.assertIn('&&&', draft['steps'][1]['raw_val'])


if __name__ == '__main__':
    unittest.main()
