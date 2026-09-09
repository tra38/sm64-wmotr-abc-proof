"""Regression tests for audit verdicts, not substitutes for the real Coq run."""
from contextlib import redirect_stdout
import io
import json
import shutil
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import discipline_audit as audit


class AssumptionReports(unittest.TestCase):
    def test_closed_context(self):
        self.assertEqual(audit.validate_assumptions("Closed under the global context\n"), [])

    def test_existing_foundations_with_wrapped_types(self):
        output = "Axioms:\nAxioms.proof_irr : ClassicalFacts.proof_irrelevance\n" \
                 "Events.external_functions_sem\n  : String.string -> AST.signature -> Events.extcall_sem\n"
        self.assertEqual(audit.validate_assumptions(output),
                         ["Axioms.proof_irr", "Events.external_functions_sem"])

    def test_failed_or_missing_reports_are_not_empty_successes(self):
        for output in ("", "opam switch not found\n", "Axioms:\n", "Axioms:\n  : Prop\n",
                       "Closed under the global context\nError: absent theorem\n",
                       "Closed under the global context\nAxioms:\nAxioms.proof_irr : True\n"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                audit.validate_assumptions(output)

    def test_unknown_axioms_in_any_namespace_fail(self):
        for name in ("LessThanOneAPress.Proofs.Fake.assumed", "OtherLibrary.assumed", "local_assumption"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                audit.validate_assumptions("Axioms:\n" + name + " : True\n")

    def test_duplicate_and_malformed_declarations_fail(self):
        for output in ("Axioms:\nAxioms.proof_irr : True\nAxioms.proof_irr : True\n",
                       "Axioms:\nAxioms.proof_irr : True\nnot an axiom declaration\n"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                audit.validate_assumptions(output)

    def test_pairs_validate_namespace_and_count(self):
        self.assertEqual(len(audit.parse_pairs([])), 3)
        for args in ([audit.MAIN], ["SM64.Proofs.Old", "theorem"],
                     [audit.MAIN, "not a theorem"], [audit.NAMESPACE + "Odd'Name", "x"],
                     [audit.MAIN, "x", audit.MAIN, "x"]):
            with self.subTest(args=args), self.assertRaises(ValueError):
                audit.parse_pairs(args)


class ProjectFixture(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="ssl-audit-test-")
        self.root = Path(self.temporary.name)
        self.sources = ["proofs/MainTheorem.v", "proofs/Helper.v", "generated/us_dummy.v"]
        for source in self.sources:
            self.write(source, "Definition sample : Prop := True.\n")
        self.write("_CoqProject", "\n".join(self.sources) + "\n")
        self.write("Makefile", "check:\n\tbash pipeline/assumptions.sh " + audit.MAIN + " sample\n")
        self.write("pipeline/discipline-kept.json", "{}")
        self.write(".CoqMakefile.d", "proofs/MainTheorem.vo proofs/MainTheorem.glob: proofs/MainTheorem.v proofs/Helper.vo\n"
                   "proofs/Helper.vo: proofs/Helper.v\n")

    def tearDown(self):
        self.temporary.cleanup()

    def write(self, path, content):
        destination = self.root / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(content, encoding="utf-8")

    def structure(self):
        return audit.check_structure(self.root, self.sources, [(audit.MAIN, "sample")])

    def add_source(self, source, dependencies=""):
        self.sources.append(source)
        self.write(source, "Definition sample : Prop := True.\n")
        self.write("_CoqProject", "\n".join(self.sources) + "\n")
        path = self.root / ".CoqMakefile.d"
        self.write(".CoqMakefile.d", path.read_text() + f"{source}o: {source} {dependencies}\n")

    def test_inventory_sees_untracked_unlisted_sources(self):
        self.write("proofs/NotInManifest.v", "Definition sample : Prop := True.\n")
        sources, problems = audit.source_inventory(self.root)
        self.assertIn("proofs/NotInManifest.v", sources)
        self.assertTrue(any("unlisted" in problem for problem in problems))

    def test_inventory_rejects_missing_and_duplicate_entries(self):
        self.write("_CoqProject", "\n".join(self.sources + [self.sources[0], "proofs/Missing.v"]))
        _, problems = audit.source_inventory(self.root)
        self.assertEqual(len(problems), 2)

    def test_main_closure(self):
        result = self.structure()
        self.assertEqual(len(result["main_import_closure"]), 2)
        self.assertEqual(result["standalone_only"], [])
        self.assertEqual(result["problems"], [])

    def test_orphan_is_not_automatically_registered(self):
        self.add_source("proofs/Orphan.v")
        self.assertTrue(any("orphan" in problem for problem in self.structure()["problems"]))

    def test_registered_result_stays_separate_from_main(self):
        self.add_source("proofs/Standalone.v")
        self.write("pipeline/discipline-kept.json", json.dumps({audit.NAMESPACE + "Standalone": "Documented example only."}))
        result = self.structure()
        self.assertEqual(result["standalone_only"], ["proofs/Standalone.v"])
        self.assertEqual(result["problems"], [])

    def test_registry_requires_real_module_and_reason(self):
        for registry in ({audit.MAIN: ""}, {audit.NAMESPACE + "Missing": "old entry"}, []):
            self.write("pipeline/discipline-kept.json", json.dumps(registry))
            with self.subTest(registry=registry), self.assertRaises(ValueError):
                self.structure()

    def test_multiline_makefile_recipe_registers_standalone(self):
        self.add_source("proofs/Standalone.v")
        self.write("Makefile", "check:\n\tbash pipeline/assumptions.sh \\\n\t  "
                   + audit.NAMESPACE + "Standalone \\\n\t  sample\n")
        self.assertEqual(self.structure()["standalone_only"], ["proofs/Standalone.v"])

    def test_comment_in_makefile_does_not_register_a_root(self):
        self.add_source("proofs/Orphan.v")
        self.write("Makefile", "# bash pipeline/assumptions.sh " + audit.NAMESPACE + "Orphan sample\n")
        self.assertTrue(self.structure()["problems"])

    def test_unwired_crossing_fails(self):
        self.add_source("proofs/Unwired/Draft.v")
        dependency = self.root / ".CoqMakefile.d"
        self.write(".CoqMakefile.d", dependency.read_text().replace(
            "proofs/Helper.vo: proofs/Helper.v", "proofs/Helper.vo: proofs/Helper.v proofs/Unwired/Draft.vo"))
        self.assertTrue(any("Unwired boundary crossed" in problem for problem in self.structure()["problems"]))

    def test_unreferenced_unwired_is_staged_not_main(self):
        self.add_source("proofs/Unwired/Draft.v")
        result = self.structure()
        self.assertEqual(result["staged_unwired"], ["proofs/Unwired/Draft.v"])
        self.assertEqual(result["problems"], [])

    def test_full_paths_allow_duplicate_basenames(self):
        self.add_source("proofs/Sub/Helper.v")
        self.write("pipeline/discipline-kept.json", json.dumps({audit.NAMESPACE + "Sub.Helper": "Independent helper."}))
        self.assertEqual(self.structure()["problems"], [])

    def test_missing_dependency_rules_fail(self):
        self.write(".CoqMakefile.d", "")
        with self.assertRaises(ValueError):
            self.structure()

    def simulated_audit(self, build_rc=0, assumption_rc=0, assumption_output="Closed under the global context\n", full_build=False):
        commands = []

        def runner(root, command, log, timeout):
            commands.append(command)
            is_assumption = command[1] == "pipeline/assumptions.sh"
            log.write_text(assumption_output if is_assumption else "test command output\n")
            return assumption_rc if is_assumption else (build_rc if command[1] == "pipeline/build.sh" else 0)

        with patch.object(audit, "run_command", runner), redirect_stdout(io.StringIO()):
            rc, output = audit.audit(self.root, [(audit.MAIN, "sample")], full_build, 10, 10)
        return rc, json.loads((output / "report.json").read_text()), commands

    def test_passing_run_reports_limited_scope(self):
        rc, report, _ = self.simulated_audit()
        self.assertEqual(rc, 0)
        self.assertTrue(report["passed"])
        self.assertIn("requested module dependencies", report["scope"])
        self.assertIn("Explicit hypotheses", report["caution"])

    def test_full_build_uses_all_registered_modules(self):
        rc, report, commands = self.simulated_audit(full_build=True)
        self.assertEqual(rc, 0)
        self.assertEqual(commands[0], ["bash", "pipeline/build.sh", "proofs"])
        self.assertEqual(report["scope"], "all _CoqProject modules")

    def test_build_failure_skips_stale_assumption_objects(self):
        rc, report, commands = self.simulated_audit(build_rc=1)
        self.assertEqual(rc, 1)
        self.assertFalse(any(command[1] == "pipeline/assumptions.sh" for command in commands))
        self.assertEqual(next(check["status"] for check in report["checks"] if check["name"] == "assumptions"), "SKIP")

    def test_nonzero_assumption_command_cannot_pass_even_with_good_text(self):
        rc, report, _ = self.simulated_audit(assumption_rc=1)
        self.assertEqual(rc, 1)
        self.assertTrue(any(check["status"] == "FAIL" and check["name"].startswith("assumptions ")
                            for check in report["checks"]))

    def test_zero_command_without_report_cannot_pass(self):
        rc, _, _ = self.simulated_audit(assumption_output="compiler did not run\n")
        self.assertEqual(rc, 1)

    def test_missing_requested_module_cannot_pass(self):
        self.write("_CoqProject", "generated/us_dummy.v\n")
        rc, report, commands = self.simulated_audit()
        self.assertEqual(rc, 1)
        self.assertEqual(report["checks"][0]["status"], "FAIL")
        self.assertFalse(any(command[1] == "pipeline/assumptions.sh" for command in commands))

    @unittest.skipUnless(shutil.which("bash"), "Bash source-checker test")
    def test_real_source_checker_rejects_an_untracked_proof_hole(self):
        checker = Path(audit.__file__).with_name("check-no-admitted.sh")
        self.write("pipeline/check-no-admitted.sh", checker.read_text())
        self.write("proofs/Untracked.v", "Axiom unfinished : True.\n")
        rc = audit.run_command(self.root, ["bash", "pipeline/check-no-admitted.sh"], self.root / "holes.log", 10)
        self.assertEqual(rc, 1)
        self.assertIn("Untracked.v", (self.root / "holes.log").read_text())

    @unittest.skipUnless(hasattr(__import__("os"), "killpg"), "POSIX process-group test")
    def test_real_command_timeout_is_failure(self):
        log = self.root / "timeout.log"
        rc = audit.run_command(self.root, [sys.executable, "-c", "import time; time.sleep(10)"], log, 0.1)
        self.assertEqual(rc, 124)
        self.assertIn("TIMEOUT", log.read_text())


if __name__ == "__main__":
    unittest.main()
