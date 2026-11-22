import tempfile
import unittest
from pathlib import Path

from replay import AUDITS, CHECK, ENDPOINTS, TARGETS, check_archive_imports, comparison_stage, digest, ordered_sources


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


if __name__ == "__main__":
    unittest.main()
