import tempfile
import unittest
from pathlib import Path

from replay import check_archive_imports, digest


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


if __name__ == "__main__":
    unittest.main()
