import tempfile
import unittest
from pathlib import Path

from replay import AUDITS, CHECK, ENDPOINTS, RANK_ENDPOINTS, TARGETS, check_archive_imports, comparison_checkpoints, comparison_stage, digest, direct_imports, ordered_sources, rank_plan, rank_stage, unit_stage


class ArchiveImports(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        self.archives = [root / "first", root / "second"]
        self.library = root / "library"
        self.manifest = root / "imports.sha256"
        local = root / "Local.lean"
        local.write_text("")
        source = root / "Main.lean"
        source.write_text("import Local\npublic import Lean.Util\nimport Tower.Bound\nimport Other\n")
        self.sources = {"Local": (root, local), "Main": (root, source)}
        self.put(self.library, "Lean/Util.olean")
        self.bound = self.put(self.archives[0], "Tower/Bound.olean")
        self.other = self.put(self.archives[1], "Other.olean")
        self.rows = [digest(self.bound) + "  Tower/Bound.olean", digest(self.other) + "  Other.olean"]
        self.manifest.write_text("\n".join(self.rows) + "\n")

    def put(self, root, name):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(name.encode())
        return path

    def check(self):
        check_archive_imports(self.sources, self.archives, [self.library], self.manifest)

    def test_local_library_and_split_archive(self):
        self.check()

    def test_missing_hash(self):
        self.manifest.write_text(self.rows[1] + "\n")
        with self.assertRaisesRegex(ValueError, "Missing archive hash: Tower/Bound"):
            self.check()

    def test_duplicate_hash(self):
        self.manifest.write_text("\n".join([*self.rows, self.rows[0]]))
        with self.assertRaisesRegex(ValueError, "duplicate archive hash"):
            self.check()

    def test_first_archive_copy_wins(self):
        self.put(self.archives[1], "Tower/Bound.olean")
        self.bound.write_bytes(b"different")
        with self.assertRaisesRegex(ValueError, "Archive object differs: Tower/Bound"):
            self.check()

    def test_first_package_root_wins(self):
        self.bound.unlink()
        self.put(self.archives[1], "Tower/Bound.olean")
        with self.assertRaisesRegex(ValueError, "Missing imported object: Tower/Bound"):
            self.check()

    def test_archive_shadows_library(self):
        self.put(self.archives[0], "Lean/Util.olean")
        with self.assertRaisesRegex(ValueError, "Missing archive hash: Lean/Util"):
            self.check()

    def test_library_cannot_replace_pinned_object(self):
        self.other.unlink()
        self.put(self.library, "Other.olean")
        with self.assertRaisesRegex(ValueError, "Expected an archive object: Other"):
            self.check()

    def test_unknown_import(self):
        self.other.unlink()
        self.manifest.write_text(self.rows[0] + "\n")
        with self.assertRaisesRegex(ValueError, "Missing imported object: Other"):
            self.check()


class ComparisonStages(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.objects = Path(temp.name)
        self.sources = ordered_sources(TARGETS["compare"])

    def phase(self, stage):
        return comparison_stage(stage, self.sources, self.objects)

    def object(self, name):
        path = self.objects.joinpath(*name.split(".")).with_suffix(".olean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch()
        return path

    def test_all_builds_kernels_and_audits(self):
        common, kernels, audits = self.phase("common")
        self.assertEqual((len(common), kernels, audits), (74, (), set()))
        for name in common:
            self.object(name)
        compiled, checked, audited = set(common), [], []
        for endpoint, (terminal, _) in ENDPOINTS.items():
            if terminal:
                names, groups, reports = self.phase("build-" + endpoint)
                self.assertEqual((names, groups, reports), ({terminal}, (), set()))
                self.assertNotIn(terminal, compiled)
                compiled.update(names)
                obj = self.object(terminal)
                names, groups, reports = self.phase("kernel-" + endpoint)
                self.assertFalse(names or reports)
                checked.extend(groups)
            names, groups, reports = self.phase("audit-" + endpoint)
            self.assertFalse(names or groups)
            audited.extend(reports)
            if terminal:
                obj.unlink()
        self.assertEqual(compiled, self.sources.keys() - AUDITS.keys())
        self.assertCountEqual(checked, [CHECK["proof"], ("SingleInertiaRH",), ("CheckAlpogePrincipalArchivedGeometryRH",)])
        self.assertCountEqual(audited, self.sources.keys() & AUDITS.keys())

    def test_missing_or_wrong_checkpoint(self):
        with self.assertRaisesRegex(ValueError, "different modules"):
            self.phase("kernel-published")
        common, _, _ = self.phase("common")
        for name in common | {"SecondSeedRH"}:
            self.object(name)
        with self.assertRaisesRegex(ValueError, "different modules"):
            self.phase("audit-previous")
        with self.assertRaisesRegex(ValueError, "empty object directory"):
            self.phase("common")

    def test_comparison_checkpoints_cover_the_common_objects_once(self):
        plan = comparison_checkpoints(self.sources)
        original, _, _ = self.phase("common")
        compiled = []
        for stage, (required, builds) in plan.items():
            with self.subTest(stage=stage):
                for name in required:
                    self.object(name)
                self.assertEqual(self.phase(stage), (builds, (), set()))
                self.assertTrue(required.isdisjoint(builds))
                for name in builds:
                    imports = set(direct_imports(self.sources[name][1])) & self.sources.keys()
                    self.assertTrue(imports <= (required | builds), name)
                for path in self.objects.rglob("*.olean"):
                    path.unlink()
                compiled.extend(builds)
        self.assertCountEqual(compiled, original)
        window = set.union(*plan["build-single-window"])
        frame = set.union(*plan["build-frame"])
        self.assertEqual(window & frame, plan["build-basis"][1])
        self.assertEqual(window | frame, original)

    def test_comparison_checkpoints_reject_missing_and_extra_modules(self):
        with self.assertRaisesRegex(ValueError, "different modules"):
            self.phase("build-counts")
        self.object("Unrelated")
        with self.assertRaisesRegex(ValueError, "different modules"):
            self.phase("build-basis")

    def test_rank_stages_cover_the_full_replay(self):
        sources = ordered_sources(TARGETS["mizusawa"])
        plan = rank_plan(sources)
        objects = sources.keys() - AUDITS.keys()
        compiled, checked, audited = [], [], []
        for required, builds, kernels, audits in plan.values():
            for name in builds:
                imports = set(direct_imports(sources[name][1])) & objects
                self.assertTrue(imports <= (required | builds), name)
            self.assertTrue(required.isdisjoint(builds))
            compiled.extend(builds)
            checked.extend(name for group in kernels for name in group)
            audited.extend(audits)
        self.assertCountEqual(compiled, objects)
        self.assertCountEqual(checked, CHECK["mizusawa"])
        self.assertCountEqual(audited, sources.keys() & AUDITS.keys())
        window_inputs, window_builds, _, _ = plan["build-window"]
        frame_inputs, frame_builds, _, _ = plan["build-frame"]
        window, frame = window_inputs | window_builds, frame_inputs | frame_builds
        self.assertEqual(window & frame, plan["build-basis"][1])
        for endpoint in RANK_ENDPOINTS:
            self.assertEqual(plan["build-" + endpoint][0], window | frame)

    def test_rank_rejects_incomplete_and_foreign_objects(self):
        sources = ordered_sources(TARGETS["mizusawa"])
        with self.assertRaisesRegex(ValueError, "different modules"):
            rank_stage("audit-three", sources, self.objects)
        self.object("OtherModule")
        with self.assertRaisesRegex(ValueError, "different modules"):
            rank_stage("build-basis", sources, self.objects)

    def test_unit_proof_stages(self):
        sources = ordered_sources(TARGETS["tame-eight-rh"])
        inputs, kernels, audits = unit_stage("build-inputs", sources, self.objects)
        self.assertTrue({"SecondSeedWindow", "CyclotomicEight"} <= inputs)
        self.assertFalse(kernels or audits)
        with self.assertRaisesRegex(ValueError, "different modules"):
            unit_stage("build-endpoint", sources, self.objects)
        for name in inputs:
            self.object(name)
        remaining, kernels, audits = unit_stage("build-endpoint", sources, self.objects)
        self.assertFalse(kernels or audits or inputs & remaining)
        self.assertEqual(inputs | remaining, sources.keys() - AUDITS.keys())
        for name in remaining:
            self.object(name)
        self.assertEqual(unit_stage("kernel-endpoint", sources, self.objects), (set(), (CHECK["tame-eight-rh"],), set()))
        self.assertEqual(unit_stage("audit-endpoint", sources, self.objects), (set(), (), {"AuditTameEightRH"}))
        self.object("SecondSeedRH")
        with self.assertRaisesRegex(ValueError, "different modules"):
            unit_stage("audit-endpoint", sources, self.objects)


if __name__ == "__main__":
    unittest.main()
