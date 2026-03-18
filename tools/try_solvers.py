import glob
import os
import subprocess


if __name__ == "__main__":
    for filename in glob.glob("**/*.smt2", root_dir="/tmp/kdrag", recursive=True):
        filename = os.path.join("/tmp/kdrag", filename)
        print(filename)
        smtlib = open(filename).read()
        if any(
            s in smtlib
            for s in ["complement", "setminus", "union", "intersection", "subset"]
        ):
            print(f"Skipping {filename} due to unsupported features")
            continue
        subprocess.run(["cvc5", filename], check=True)
