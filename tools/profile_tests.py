#!/usr/bin/env python3
"""
Run tests with cProfile to generate detailed profiling data.

Usage:
    python tools/profile_tests.py [pytest-args]
    python tools/profile_tests.py tests/test_kernel.py
    python tools/profile_tests.py -k test_Lemma
"""
import sys
import cProfile
import pstats
import io
from pathlib import Path


def main():
    """Run pytest with profiling and generate report."""
    # Import pytest here so it doesn't slow down normal imports
    import pytest
    
    # Run pytest with profiling
    profiler = cProfile.Profile()
    profiler.enable()
    
    # Pass all arguments to pytest
    exit_code = pytest.main(sys.argv[1:])
    
    profiler.disable()
    
    # Generate profiling statistics
    stats = pstats.Stats(profiler)
    
    # Save raw profile data
    profile_file = Path('.pytest_profile.prof')
    profiler.dump_stats(profile_file)
    print(f"\n✓ Profile data saved to: {profile_file}")
    print(f"  View with: python -m pstats {profile_file}")
    
    # Print summary to console
    print("\n" + "=" * 80)
    print("PROFILING SUMMARY")
    print("=" * 80)
    
    # Print statistics sorted by cumulative time
    print("\nTop 20 functions by cumulative time:")
    print("-" * 80)
    s = io.StringIO()
    stats.stream = s  # type: ignore[misc]
    stats.sort_stats('cumulative')
    stats.print_stats(20)
    print(s.getvalue())
    
    # Print statistics sorted by internal time
    print("\nTop 20 functions by internal time:")
    print("-" * 80)
    s = io.StringIO()
    stats.stream = s  # type: ignore[misc]
    stats.sort_stats('time')
    stats.print_stats(20)
    print(s.getvalue())
    
    # Save detailed report to file
    report_file = Path('.pytest_profile.txt')
    with open(report_file, 'w') as f:
        stats.stream = f  # type: ignore[misc]
        stats.sort_stats('cumulative')
        stats.print_stats()
    print(f"\n✓ Detailed profile report saved to: {report_file}")
    
    return exit_code


if __name__ == '__main__':
    sys.exit(main())
