"""
Pytest configuration and timing plugin for knuckledragger tests.

This plugin collects timing information for tests and proof operations,
and generates reports that are useful for CI/CD pipelines.
"""
import time
import json
from pathlib import Path
import kdrag.config as config


class TimingPlugin:
    """Plugin to collect timing information for tests and proofs."""
    
    def __init__(self):
        self.test_timings = []
        self.session_start = None
        self.proof_events = []
        
    def pytest_sessionstart(self, session):
        """Called at the start of the test session."""
        self.session_start = time.perf_counter()
        # Enable timing in kdrag config to collect proof timings
        config.timing = True
        config.perf_log.clear()
        
    def pytest_runtest_setup(self, item):
        """Called before each test runs."""
        item.test_start = time.perf_counter()
        
    def pytest_runtest_teardown(self, item):
        """Called after each test completes."""
        if hasattr(item, 'test_start'):
            start_time: float = item.test_start  # type: ignore[attr-defined]
            duration = time.perf_counter() - start_time
            self.test_timings.append({
                'nodeid': item.nodeid,
                'duration': duration,
                'outcome': getattr(item, 'test_outcome', 'unknown')
            })
    
    def pytest_runtest_makereport(self, item, call):
        """Store test outcome."""
        if call.when == 'call':
            if call.excinfo is None:
                item.test_outcome = 'passed'
            else:
                item.test_outcome = 'failed'
            
    def pytest_sessionfinish(self, session):
        """Called at the end of the test session."""
        session_duration = time.perf_counter() - (self.session_start or 0)
        
        # Generate timing report
        report = self._generate_report(session_duration)
        
        # Write JSON report
        report_path = Path('.pytest_timing_report.json')
        with open(report_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        # Print summary to console
        self._print_summary(report)
        
    def _generate_report(self, session_duration):
        """Generate a comprehensive timing report."""
        # Sort tests by duration
        sorted_tests = sorted(
            self.test_timings, 
            key=lambda x: x['duration'], 
            reverse=True
        )
        
        # Group proof events by type
        proof_events = {}
        for tag, data, duration in config.perf_log:
            if tag not in proof_events:
                proof_events[tag] = []
            proof_events[tag].append({
                'description': str(data),
                'duration': duration
            })
        
        # Sort proof events within each category
        for tag in proof_events:
            proof_events[tag] = sorted(
                proof_events[tag],
                key=lambda x: x['duration'],
                reverse=True
            )
        
        return {
            'session_duration': session_duration,
            'total_tests': len(self.test_timings),
            'slowest_tests': sorted_tests[:20],  # Top 20 slowest
            'all_tests': sorted_tests,
            'proof_events': proof_events,
            'summary': {
                'total_test_time': sum(t['duration'] for t in self.test_timings),
                'avg_test_time': sum(t['duration'] for t in self.test_timings) / len(self.test_timings) if self.test_timings else 0,
                'proof_event_count': len(config.perf_log)
            }
        }
    
    def _print_summary(self, report):
        """Print a human-readable summary."""
        print("\n" + "=" * 70)
        print("TIMING REPORT SUMMARY")
        print("=" * 70)
        
        print(f"\nSession Duration: {report['session_duration']:.2f}s")
        print(f"Total Tests: {report['total_tests']}")
        print(f"Total Test Time: {report['summary']['total_test_time']:.2f}s")
        print(f"Average Test Time: {report['summary']['avg_test_time']:.4f}s")
        print(f"Proof Events Recorded: {report['summary']['proof_event_count']}")
        
        print("\n" + "-" * 70)
        print("TOP 10 SLOWEST TESTS")
        print("-" * 70)
        
        for i, test in enumerate(report['slowest_tests'][:10], 1):
            print(f"{i:2d}. {test['duration']:7.4f}s  {test['nodeid']}")
        
        # Print slowest proof events by category
        if report['proof_events']:
            print("\n" + "-" * 70)
            print("SLOWEST PROOF OPERATIONS (by category)")
            print("-" * 70)
            
            for tag, events in sorted(report['proof_events'].items()):
                top_events = events[:5]  # Top 5 per category
                if top_events:
                    print(f"\n{tag}:")
                    for event in top_events:
                        desc = event['description']
                        if len(desc) > 60:
                            desc = desc[:57] + "..."
                        print(f"  {event['duration']:7.4f}s  {desc}")
        
        print("\n" + "=" * 70)
        print("Full report saved to: .pytest_timing_report.json")
        print("=" * 70 + "\n")


def pytest_configure(config):
    """Register the timing plugin."""
    if not config.option.collectonly:
        plugin = TimingPlugin()
        config.pluginmanager.register(plugin, "timing_plugin")
