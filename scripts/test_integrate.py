#!/usr/bin/env python3
"""Exercise merge-train Git behavior against temporary local bare remotes."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("integrate.sh").read_text()


class MergeTrain(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="syo-train-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.queue = self.root / "queue"
        self.queue.mkdir()
        self.gates = self.root / "gates"
        self.env = dict(os.environ, SYO_INTEGRATE_QUEUE=str(self.queue),
                        SYO_INTEGRATE_LOCK=str(self.root / "lock"),
                        TEST_GATE_LOG=str(self.gates))
        self.git("init", "-q", "--bare", str(self.root / "origin"))
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "Merge train test")
        self.git("config", "user.email", "train@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("config", "core.hooksPath", "/dev/null")
        (self.repo / "scripts").mkdir()
        (self.repo / "scripts/integrate.sh").write_text(SCRIPT)
        (self.repo / "scripts/check_all.sh").write_text(
            '#!/bin/bash\ngit rev-parse HEAD >> "$TEST_GATE_LOG"\n'
            'test ! -e reject-train\n')
        self.commit("base", "base")
        self.git("remote", "add", "origin", str(self.root / "origin"))
        self.git("push", "-q", "-u", "origin", "main")
        self.base = self.git("rev-parse", "HEAD")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.repo,
                                       env=self.env, stderr=subprocess.PIPE,
                                       text=True).strip()

    def commit(self, name, contents):
        (self.repo / name).write_text(contents)
        self.git("add", ".")
        self.git("commit", "-qm", "change " + name)
        return self.git("rev-parse", "HEAD")

    def queue_branch(self, name):
        sha = self.git("rev-parse", name)
        (self.queue / name).write_text(f"{sha} {name} {self.repo}\n")

    def run_train(self):
        run = subprocess.run(["bash", "scripts/integrate.sh"], cwd=self.repo,
                             env=self.env, text=True, capture_output=True,
                             timeout=30)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertNotIn("train-", self.git("branch", "--list"))
        self.git("fetch", "-q", "origin", "main")
        return run.stdout

    def remote_has(self, filename):
        return filename in self.git("ls-tree", "-r", "--name-only", "origin/main").splitlines()

    def test_shared_ancestor_is_picked_once(self):
        shared = self.commit("shared", "shared")
        self.git("checkout", "-qb", "rider", shared)
        self.commit("rider-file", "rider")
        self.queue_branch("rider")
        self.git("checkout", "-qb", "holder", shared)
        self.commit("holder-file", "holder")
        out = self.run_train()
        self.assertIn("landed train", out)
        self.assertTrue(self.remote_has("rider-file"))
        self.assertTrue(self.remote_has("holder-file"))
        self.assertEqual(len(self.gates.read_text().splitlines()), 1)

    def test_rebased_equivalent_patch_is_skipped(self):
        self.git("checkout", "-qb", "rider", self.base)
        patch = self.commit("shared", "shared")
        self.commit("rider-file", "rider")
        self.queue_branch("rider")
        self.git("checkout", "-qb", "holder", self.base)
        self.commit("holder-file", "holder")
        self.git("cherry-pick", patch)
        self.assertNotEqual(self.git("rev-parse", "HEAD"), patch)
        self.assertIn("landed train", self.run_train())
        self.assertTrue(self.remote_has("rider-file"))
        self.assertEqual(len(self.gates.read_text().splitlines()), 1)

    def test_conflicting_rider_rolls_back_all_its_commits(self):
        self.git("checkout", "-qb", "rider", self.base)
        self.commit("rider-file", "rider")
        self.commit("base", "rider conflict")
        self.queue_branch("rider")
        self.git("checkout", "-qb", "holder", self.base)
        self.commit("base", "holder conflict")
        self.assertIn("does not apply cleanly", self.run_train())
        self.assertFalse(self.remote_has("rider-file"))
        self.assertEqual(self.git("show", "origin/main:base"), "holder conflict")
        self.assertEqual(len(self.gates.read_text().splitlines()), 1)

    def test_failed_train_gates_holder_alone(self):
        self.git("checkout", "-qb", "rider", self.base)
        self.commit("reject-train", "fail")
        self.queue_branch("rider")
        self.git("checkout", "-qb", "holder", self.base)
        self.commit("holder-file", "holder")
        self.assertIn("train gate failed", self.run_train())
        self.assertFalse(self.remote_has("reject-train"))
        self.assertTrue(self.remote_has("holder-file"))
        self.assertEqual(len(self.gates.read_text().splitlines()), 2)

    def test_already_landed_needs_no_gate(self):
        self.assertIn("nothing left to land", self.run_train())
        self.assertFalse(self.gates.exists())


if __name__ == "__main__":
    unittest.main()
