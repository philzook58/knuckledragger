import os
import subprocess

# https://github.com/gleachkr/Aufbau


aufbau_dir = os.path.join(os.path.dirname(__file__), "Aufbau")
aufbau_path = os.path.join(aufbau_dir, "zig-out", "bin", "abc")
mm0_zig_path = os.path.join(aufbau_dir, "zig-out", "bin", "mm0-zig")


def build_aufbau(update: bool = False):
    import ziglang

    zigpath = os.path.join(ziglang.__path__[0], "zig")
    if not os.path.exists(aufbau_dir):
        update = False
        subprocess.run(
            ["git", "clone", "--depth", "1", "https://github.com/gleachkr/Aufbau"],
            cwd=os.path.dirname(__file__),
            check=True,
        )
    if update:
        subprocess.run(["git", "pull"], cwd=aufbau_dir, capture_output=True, check=True)
    subprocess.run(
        [zigpath, "build", "-Doptimize=ReleaseFast"],
        cwd=aufbau_dir,
        check=True,
    )
    return aufbau_path, mm0_zig_path


def test_auf():
    import pytest

    if not os.path.exists(mm0_zig_path):
        pytest.skip()
        # pytest.skip(reason="Aufbau mm0-zig binary is not built")
    res = subprocess.run([mm0_zig_path], capture_output=True)
    assert res.stdout.decode() == "Usage: mm0-zig FILE.mmb < FILE.mm0\n"
