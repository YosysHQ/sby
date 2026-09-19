"""Run with python3 -m unittest discover -s tests -p test_jobserver.py."""
from pathlib import Path
from types import SimpleNamespace
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'sbysrc'))
import sby_jobserver as jobs
from sby_core import SbyProc


class CancellationTests(unittest.TestCase):
    def setUp(self):
        jobs.inherited_jobserver_auth_present = False
        jobs.inherited_jobserver_auth = None
        jobs.inherited_jobcount = None
        self.client = jobs.SbyJobClient(1)

    def test_running_then_waiting_cancellation(self):
        active = self.client.request_lease()
        waiting = self.client.request_lease()
        active.done()
        waiting.done()
        self.assertFalse(self.client.has_pending_leases())
        self.assertEqual(self.client.local_slots, 1)
        active.done()
        waiting.done()
        self.assertEqual(self.client.local_slots, 1)

    def test_waiting_cancel_does_not_wait_for_active_slot(self):
        active = self.client.request_lease()
        waiting = self.client.request_lease()
        waiting.done()
        self.assertFalse(self.client.has_pending_leases())
        self.assertEqual(self.client.local_slots, 0)
        active.done()
        self.assertEqual(self.client.local_slots, 1)

    def test_canceled_request_is_skipped_before_live_request(self):
        active = self.client.request_lease()
        canceled = self.client.request_lease()
        live = self.client.request_lease()
        canceled.done()
        self.assertTrue(self.client.has_pending_leases())
        active.done()
        self.assertFalse(canceled.is_ready)
        self.assertTrue(live.is_ready)
        live.done()
        self.assertEqual(self.client.local_slots, 1)

    def test_terminate_releases_ready_and_pending_leases(self):
        active = self.client.request_lease()
        waiting = self.client.request_lease()
        for lease in [waiting, active]:
            proc = SbyProc.__new__(SbyProc)
            proc.task = SimpleNamespace(opt_wait=False, update_proc_canceled=lambda p: None)
            proc.wait = proc.running = proc.finished = proc.terminated = proc.exited = False
            proc.job_lease = lease
            proc.terminate(True)
            self.assertTrue(lease.is_done)
        self.assertFalse(self.client.has_pending_leases())
        self.assertEqual(self.client.local_slots, 1)


if __name__ == '__main__':
    unittest.main()
