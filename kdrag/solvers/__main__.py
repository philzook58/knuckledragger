import sys
import subprocess
from . import binpath


def run_subprocess(command, args):
    """Run a subprocess with the provided command and arguments."""
    try:
        result = subprocess.run([command] + args, check=True)
        return result
    except subprocess.CalledProcessError as e:
        print(f"Error running command {command}: {e}")
        sys.exit(e.returncode)


def main():
    if len(sys.argv) < 2:
        print("Usage: script_name <command> [args...]")
        sys.exit(1)

    command = sys.argv[1]
    args = sys.argv[2:]

    if command == "vampire":
        run_subprocess(binpath("vampire"), args)
    if command == "vampire-ho":
        run_subprocess(binpath("vampire-ho"), args)
    elif command == "eprover":
        run_subprocess(binpath("eprover-ho"), args)
    elif command == "twee":
        run_subprocess(binpath("twee"), args)
    elif command == "nanocopi":
        run_subprocess(binpath("nanoCoP-i20/nanocopi.sh"), args)
    else:
        print(f"Unknown command: {command}")
        sys.exit(1)


if __name__ == "__main__":
    main()
