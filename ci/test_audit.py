#!/usr/bin/env python3
"""Exercise audit failure modes without invoking Lean."""

from pathlib import Path
import re
import unittest

from check_axioms import AuditError, expected_names, verify_log
from check_sources import SourceError, scan_text, scan_tree


ROOT = Path(__file__).resolve().parents[1]


class AxiomAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (ROOT / "CatalanAnchor/Audit.lean").read_text(encoding="utf-8")
        cls.expected = expected_names(cls.source)
        candidates = [ROOT / "AXIOM_AUDIT.txt", *sorted((ROOT / "docs").rglob("AXIOM_AUDIT.txt"))]
        cls.log = next(path for path in candidates if path.is_file()).read_text(encoding="utf-8")
        cls.first = "'" + cls.expected[0] + "' depends on axioms: [propext, Classical.choice, Quot.sound]"

    def test_historical_log_has_all_88_records(self):
        self.assertEqual(len(verify_log(self.log, self.expected)), 88)

    def test_missing_record_rejected(self):
        with self.assertRaisesRegex(AuditError, "missing"):
            verify_log(self.log.replace(self.first, "", 1), self.expected)

    def test_empty_log_rejected(self):
        with self.assertRaisesRegex(AuditError, "missing"):
            verify_log("", self.expected)

    def test_duplicate_record_rejected(self):
        with self.assertRaisesRegex(AuditError, "duplicate"):
            verify_log(self.log + "\n" + self.first, self.expected)

    def test_unexpected_record_rejected(self):
        with self.assertRaisesRegex(AuditError, "unexpected"):
            verify_log(self.log + "\n'Unexpected.theorem' depends on axioms: [propext]\n", self.expected)

    def test_all_unapproved_axioms_rejected(self):
        for axiom in ("sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Custom.axiom"):
            with self.subTest(axiom=axiom), self.assertRaisesRegex(AuditError, "forbidden"):
                verify_log(self.log.replace("[propext, Classical.choice, Quot.sound]", f"[{axiom}]", 1), self.expected)

    def test_malformed_record_rejected(self):
        for replacement in (self.first[:-1], self.first + " trailing text", self.first.replace("propext,", "propext,,")):
            with self.subTest(replacement=replacement), self.assertRaisesRegex(AuditError, "malformed"):
                verify_log(self.log.replace(self.first, replacement, 1), self.expected)

    def test_no_axioms_is_valid(self):
        replacement = "'" + self.expected[0] + "' does not depend on any axioms"
        result = verify_log(self.log.replace(self.first, replacement, 1), self.expected)
        self.assertEqual(result[self.expected[0]], frozenset())

    def test_multiline_list_is_valid(self):
        changed = self.log.replace("[propext, Classical.choice, Quot.sound]", "[propext,\n Classical.choice,\n Quot.sound]", 1)
        self.assertEqual(len(verify_log(changed, self.expected)), 88)

    def test_duplicate_source_directive_rejected(self):
        with self.assertRaisesRegex(AuditError, "duplicate"):
            expected_names(self.source + "\n#print axioms " + self.expected[0])

    def test_missing_source_directive_rejected(self):
        changed = self.source.replace("#print axioms " + self.expected[0], "-- removed", 1)
        with self.assertRaisesRegex(AuditError, "expected 88"):
            expected_names(changed)

    def test_error_diagnostic_rejected(self):
        with self.assertRaisesRegex(AuditError, "error diagnostic"):
            verify_log(self.log + "\nAudit.lean:1:0: error: failed\n", self.expected)


class SourceScanTests(unittest.TestCase):
    def test_current_project_passes(self):
        self.assertGreaterEqual(scan_tree(ROOT), 24)

    def test_forbidden_code_rejected(self):
        for token in ("sorry", "admit", "axiom", "constant", "native_decide", "unsafe", "sorryAx", "Lean.ofReduceBool"):
            with self.subTest(token=token), self.assertRaises(SourceError):
                scan_text("theorem example : True := by " + token)

    def test_comments_and_strings_do_not_trigger(self):
        scan_text('/- outer /- sorry -/ constant -/\n-- admit\ndef msg := "unsafe \\" sorry"\ntheorem ok : True := by trivial')

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(SourceError):
            scan_text("/- unclosed")

    def test_unterminated_string_rejected(self):
        with self.assertRaises(SourceError):
            scan_text('def msg := "unclosed')


if __name__ == "__main__":
    unittest.main()
