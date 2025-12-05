import shutil
import subprocess
import os

cargo_path = shutil.which("cargo")
if cargo_path is None:
    raise ImportError(
        "Could not find 'cargo' in PATH; is Rust installed? Visit https://rustup.rs/"
    )

print("Building kdrag Rust extensions. This may take a while...")
# Not necessary it seems
# subprocess.call(["cargo", "build", "--release"], cwd=os.path.join(__path__[0], "rust"))
subprocess.call(
    ["maturin", "develop", "--release"],
    cwd=os.path.join(list(__path__)[0], "rust", "kdragrs"),
)
