import sys
import subprocess
from . import _kissat_path, binpath, install_solvers


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
        install_solvers()
    elif command in ("vampire", "vampire-ho"):
        from vampire import vampire_path

        run_subprocess(vampire_path, args)
    elif command == "eprover":
        from eprover import eprover_path

        run_subprocess(eprover_path, args)
    elif command == "twee":
        run_subprocess(binpath("twee"), args)
    elif command == "nanocopi":
        run_subprocess(binpath("nanoCoP-i20/nanocopi.sh"), args)
    elif command == "prover9":
        run_subprocess(binpath("Prover9/LADR-2026-8A/bin/prover9"), args)
    elif command == "kissat":
        run_subprocess(_kissat_path(), args)
    elif command == "aprove":
        run_subprocess("java", ["-ea", "-jar", binpath("aprove.jar")] + args)
    else:
        print(f"Unknown command: {command}")
        print(usage_string)
        sys.exit(1)


if __name__ == "__main__":
    main()
