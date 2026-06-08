import ziglang
import os

zigpath = os.path.join(ziglang.__path__[0], "zig")
import subprocess
import kdrag.solvers
# https://github.com/gleachkr/Aufbau


aufbau_dir = os.path.join(os.path.dirname(__file__), "Aufbau")
if not os.path.exists(aufbau_dir):
    subprocess.run(
        ["git", "clone", "--depth", "1", "https://github.com/gleachkr/Aufbau"],
        cwd=os.path.dirname(__file__),
        check=True,
    )

subprocess.run(["git", "pull"], cwd=aufbau_dir, capture_output=True, check=True)

subprocess.run(
    [zigpath, "build", "-Doptimize=ReleaseFast"],
    cwd=aufbau_dir,
    check=True,
)


aufbau_path = os.path.join(aufbau_dir, "zig-out", "bin", "abc")
mm0_zig_path = os.path.join(aufbau_dir, "zig-out", "bin", "mm0-zig")


def test_auf():
    res = subprocess.run([mm0_zig_path], capture_output=True)
    assert res.stdout.decode() == "Usage: mm0-zig FILE.mmb < FILE.mm0\n"
