// Run a Python script against a knuckledragger wheel under Pyodide in Node.
//   npm install pyodide@314.0.6   (or set PYODIDE_DIR to an installed copy)
//   node tools/pyodide_smoke.mjs dist/knuckledragger-*.whl [script.py] [args...]
// script.py defaults to tools/real_smoke.py; args become sys.argv[1:].
// The current directory is mounted at /repo and is the working directory.
import { readFileSync } from "node:fs";
import { basename, dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const { loadPyodide } = await import(
  process.env.PYODIDE_DIR ? pathToFileURL(join(process.env.PYODIDE_DIR, "pyodide.mjs")).href : "pyodide"
);

const [wheel, script = join(dirname(fileURLToPath(import.meta.url)), "real_smoke.py"), ...args] =
  process.argv.slice(2);
const py = await loadPyodide();
await py.loadPackage("micropip");
const whl = `/wheels/${basename(wheel)}`;
py.FS.mkdirTree("/wheels");
py.FS.writeFile(whl, readFileSync(wheel));
await py.runPythonAsync(`
import micropip
await micropip.install(["emfs:${whl}", "z3-solver==5.3.3.0"])
`);
py.FS.mkdirTree("/repo");
py.FS.mount(py.FS.filesystems.NODEFS, { root: process.cwd() }, "/repo");
py.FS.chdir("/repo");
py.globals.set("argv", py.toPy([script, ...args]));
try {
  await py.runPythonAsync(`import sys; sys.argv = list(argv)\n` + readFileSync(script, "utf8"));
} catch (e) {
  console.error(e.message);
  process.exit(1);
}
