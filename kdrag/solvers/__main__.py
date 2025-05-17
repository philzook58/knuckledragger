import sys
import subprocess
from . import binpath, install_solvers2


def run_subprocess(command, args):
    """Run a subprocess with the provided command and arguments."""
    try:
        result = subprocess.run([command] + args, check=True)
        return result
    except subprocess.CalledProcessError as e:
        print(f"Error running command {command}: {e}")
        sys.exit(e.returncode)


def main():
    usage_string = "Usage: python3 -m kdrag.solvers (install | vampire | vampire-ho | eprover | twee | nanocopi | prover9 | kissat) [args...]"
    if len(sys.argv) < 2:
        print(usage_string)
        sys.exit(1)

    command = sys.argv[1]
    args = sys.argv[2:]

    if command == "install":
        install_solvers2()
    elif command == "vampire":
        run_subprocess(binpath("vampire"), args)
    elif command == "vampire-ho":
        run_subprocess(binpath("vampire-ho"), args)
    elif command == "eprover":
        run_subprocess(binpath("eprover-ho"), args)
    elif command == "twee":
        run_subprocess(binpath("twee"), args)
    elif command == "nanocopi":
        run_subprocess(binpath("nanoCoP-i20/nanocopi.sh"), args)
    elif command == "prover9":
        run_subprocess(binpath("Prover9/bin/prover9"), args)
    elif command == "kissat":
        run_subprocess(binpath("kissat/build/kissat"), args)
    elif command == "aprove":
        run_subprocess("java", ["-ea", "-jar", binpath("aprove.jar")] + args)
    else:
        print(f"Unknown command: {command}")
        print(usage_string)
        sys.exit(1)


if __name__ == "__main__":
    main()
