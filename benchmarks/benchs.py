#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import signal
import subprocess
import shutil
import json
import time
import curses
import threading
import atexit
import itertools
from glob import glob

import fire

######## General Utils ########

_active_groups = set()

def cleanup_all():
    for pgid in list(_active_groups):
        try: os.killpg(pgid, signal.SIGKILL)
        except ProcessLookupError: pass
    _active_groups.clear()

atexit.register(cleanup_all)

def printLog(x, f):
    if f: print(x, file=f)
    else: print(x)

def timerBench(func, *args, **kwargs):
    start = time.perf_counter()
    result = func(*args, **kwargs)
    elapsed = time.perf_counter() - start
    if result is None: return None
    return {**result, "time": elapsed}

def protectPath(p):
    return "\"" + p + "\""

def concat(xxs):
    r = []
    for xs in xxs: r.extend(xs)
    return r

timeoutOpCode = 124

def runCommand(secs, f, command):
    printLog(command, f)
    stdout, stderr = "", ""

    process = subprocess.Popen(
        command, shell=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True
    )
    pgid = process.pid
    _active_groups.add(pgid)

    try:
        try:
            stdout, stderr = process.communicate(timeout=secs)
        except subprocess.TimeoutExpired:
            try: os.killpg(pgid, signal.SIGKILL)
            except ProcessLookupError: pass
            stdout, stderr = process.communicate()
            stderr += f"\nTimed out after {secs} seconds"
            return subprocess.CompletedProcess(command, timeoutOpCode, stdout, stderr)
        except Exception:
            try: os.killpg(pgid, signal.SIGKILL)
            except ProcessLookupError: pass
            stdout, stderr = process.communicate()
            raise
    finally:
        if stdout: printLog(stdout, f)
        if stderr: printLog(stderr, f)
        _active_groups.discard(pgid)

    return subprocess.CompletedProcess(process.args, process.returncode, stdout, stderr)

def runDockerCommand(container, secs, f, command):
    pwd = os.getcwd()
    return runCommand(secs, f, "docker run -v " + pwd + ":/mnt " + container + " /bin/bash -c \"" + command + "\"")

def runCommandMode(config, command):
    runmode = config.get("runmode", "native")
    secs = config["timeout"]
    f = config["logfile"]
    if runmode == "docker": return runDockerCommand(config["dockerContainer"], secs, f, command)
    if runmode == "native": return runCommand(secs, f, command)
    raise Exception("runmode unsupported: " + runmode)

######## SMV / Formula Utils ########

def toolExt(tool):
    if tool == "HyperQube": return ".hq"
    if tool == "AutoHyper": return ".ah"
    if tool == "QBF":       return ".qcir"
    raise Exception("tool unsupported: " + tool)

def parseFormulaHeader(inf):
    with open(inf, "r") as f:
        first = f.readline().strip()
        return [s[-1] for s in first.split(".") if s]

def lookupSMV(v, xs): return [x for x in xs if x.endswith(v + ".smv")][0]
def sortSMVs(xs, vs): return [lookupSMV(v, xs) for v in vs]

def convertFormula(tool, inhq):
    filename, oldExt = os.path.splitext(inhq)
    newExt = toolExt(tool)
    if newExt == oldExt: return inhq
    outhq = filename + newExt
    if os.path.exists(outhq): return outhq

    with open(inhq, "r") as inf:
        s = inf.read()
    if oldExt == ".ah" and newExt == ".hq":
        for a, b in [("{","*"),("}","*"),("\"",""),("_A","[A]"),("_B","[B]"),("_C","[C]"),
                     ("&","/\\"),("|","\\/"),("!","~")]:
            s = s.replace(a, b)
    else:
        raise Exception("conversion unsupported from " + oldExt + " to " + newExt)
    with open(outhq, "w") as outf: outf.write(s)
    return outhq

######## Benchmark Data ########

def readBenchs(jsonfile):
    with open(jsonfile) as f:
        dta = json.load(f)
    return dta["path"], dta["benchs"]

pathAutoHyper, benchsAutoHyper                       = readBenchs("benchsAutoHyper.json")
pathAutoHyperToHyperAlloy, benchsAutoHyperToHyperAlloy = readBenchs("benchsAutoHyperToHyperAlloy.json")
pathHyperAlloy, benchsHyperAlloy                     = readBenchs("benchsHyperAlloy.json")

BENCH_GROUPS = {
    "AutoHyper":              (pathAutoHyper,              benchsAutoHyper),
    "AutoHyperToHyperAlloy":  (pathAutoHyperToHyperAlloy,  benchsAutoHyperToHyperAlloy),
    "HyperAlloy":             (pathHyperAlloy,             benchsHyperAlloy),
}

######## Benchmark Output Parsing ########

def parseOutput(tool, out):
    lines = [l for l in out.splitlines() if l]
    lines.reverse()
    status = None
    if tool in ("AutoHyper", "QBF"):
        for l in lines:
            if   l.startswith("SAT"):   status = True;  break
            elif l.startswith("UNSAT"): status = False; break
    elif tool == "HyperQube":
        if   "r SAT"   in out: status = True
        elif "r UNSAT" in out: status = False
    conclusivity = True if "(conclusive" in out else False if "(inconclusive" in out else None
    sizes = None
    for l in lines:
        if l.startswith("Model size"):
            sizes = l[len("Model size"):].strip(); break
    return status, conclusivity, sizes

def fmtBytes(n):
    if n < 1024:        return f"{n}B"
    if n < 1024 * 1024: return f"{n/1024:.1f}KB"
    return f"{n/(1024*1024):.1f}MB"

def parseAutoHyperSystemSizes(txt):
    # AutoHyper --log emits e.g. "> system-sizes: [167,167]". Format as "167x167".
    for l in txt.splitlines():
        s = l.strip().lstrip("> ").lstrip()
        if s.startswith("system-sizes:"):
            raw = s[len("system-sizes:"):].strip().strip("[]")
            parts = [p.strip() for p in raw.split(",") if p.strip()]
            if parts: return "x".join(parts)
    return None

def collectQcirSize(started_at):
    # hyperqb writes its qcir to ./build_today/HQ.qcir (see hyperqb shell wrapper).
    # Fall back to a recursive scan in case the path changes.
    candidates = glob("build_today/*.qcir") + glob("**/*.qcir", recursive=True)
    candidates = [p for p in set(candidates) if os.path.getmtime(p) >= started_at]
    if not candidates: return None
    path = max(candidates, key=os.path.getmtime)
    return fmtBytes(os.path.getsize(path))

def inferHyperQubeConclusivity(status, sem):
    # HyperQube doesn't print conclusivity. The bounded encoding is one-sided:
    #   pessimistic (pes/hpes): TRUE is conclusive, FALSE may be a bound artefact
    #   optimistic  (opt/hopt): FALSE is conclusive, TRUE may be a bound artefact
    if status is None or sem is None: return None
    if sem in ("pes", "hpes"):  return False if status is False else True
    if sem in ("opt", "hopt"):  return False if status is True  else True
    return None

def runBench(config, n, command, expected, sem=None):
    started_at = time.time()
    result = runCommandMode(config, command)
    if result.returncode == timeoutOpCode:
        return {"symbol": "⏱ msg", "message": "timeout ", "color": "warning"}
    txt = result.stdout + "\n" + result.stderr
    status, conclusivity, sizes = parseOutput(config["tool"], txt)

    if sizes is None:
        if config["tool"] == "AutoHyper":
            sizes = parseAutoHyperSystemSizes(txt)
        elif config["tool"] == "HyperQube":
            sizes = collectQcirSize(started_at)

    if conclusivity is None and config["tool"] == "HyperQube":
        conclusivity = inferHyperQubeConclusivity(status, sem)

    if status is None:
        return {"symbol": "! err", "message": "see logs", "color": "error"}
    if expected != status:
        printLog(f"Expected {expected} but got {status}\n", config["logfile"])
        return {"expected": expected, "got": status, "result": False,
                "conclusivity": conclusivity, "sizes": sizes}
    return {"expected": expected, "got": status, "result": True,
            "conclusivity": conclusivity, "sizes": sizes}

######## Benchmark Stages ########

def genSMVfromHyperAlloy(config, outdir, bench):
    filepath = os.path.join(config["path"], bench["prop"])
    cmd = bench["cmd"]
    hostfile = "../" + filepath
    hostoutdir = outdir

    pwd = os.getcwd()
    os.chdir(pwd + "/" + hostoutdir)
    try:
        opts = "" if config["vanillaAlloy"] else bench.get("alloyOpts", {}).get(config["tool"], "")
        flags = []
        if config["vanillaAlloy"]: flags += ["--compositionoff", "--multboundsoff", "-y 0"]
        if config["noComp"]:       flags += ["--compositionoff"]
        if config["noMult"]:       flags += ["--multboundsoff"]
        if config["noSymm"]:       flags += ["-y 0"]
        if config["debug"]:        flags += ["-d"]
        flagstr = " ".join(flags)
        command = f"hyperalloy {flagstr} exec {opts} -s electrod.hypermcts -c {cmd} -f {hostfile}"
        runCommandMode(config, command)
    finally:
        os.chdir(pwd)

    rbench = bench.copy()
    hps = glob(outdir + "/*/*.hp")
    if len(hps) != 1:
        raise Exception(f"hyperalloy produced {len(hps)} hyperformulas for {outdir} {bench} {config}")
    quants = parseFormulaHeader(hps[0])
    smvs = glob(outdir + "/*.smv")
    rbench["model"] = sortSMVs(smvs, quants)
    rbench["prop"] = hps[0]
    return rbench

def optimizeSMV(config, outdir, bench):
    smvs = bench["model"]
    hq = bench["prop"]

    flags = []
    if config["debug"]:           flags += ["--debug=True"]
    if config["vanillaSmv"]:      flags += ["--bisim=False", "--splitformula=nosplitformula"]
    if config["noSplitFormulas"]: flags += ["--splitformula=nosplitformula"]
    if config["noSplitInits"]:    flags += ["--splitinits=nosplitinits"]
    flagstr = " ".join(flags)
    if "opts" in bench:    flagstr += " " + bench["opts"]

    ins = " ".join(concat([["-i", config["path"] + "/" + smv] for smv in smvs]))
    if config["tool"] == "QBF":
        outs = f" -k={bench['k']} --sem={bench['sem']}"
        outsmvs = []
        flagstr += " " + bench["qbfOpts"] if "qbfOpts" in bench else ""

    else:
        if config["tool"] == "HyperQube":
            if "hqOpts" in bench: flagstr += " " + bench["hqOpts"]
        outext = "exp" if config["tool"] == "AutoHyper" else "smv" if config["tool"] == "HyperQube" else None
        if outext is None: raise Exception("tool unsupported")
        outs = " ".join(concat([["-o", f"{outdir}/{i}.{outext}"] for i, _ in enumerate(smvs)]))
        outsmvs = [f"{outdir}/{i}.{outext}" for i, _ in enumerate(smvs)]

    outhq = outdir + "/" + "".join(str(i) for i, _ in enumerate(smvs)) + toolExt(config["tool"])
    tool = "QCIR" if config["tool"] == "QBF" else config["tool"]

    runCommandMode(config,
        f"hypersmv tomc {ins} {outs} -H={tool} -I {config['path']}/{hq} -O {outhq} {flagstr}")

    rbench = bench.copy()
    rbench["model"] = outsmvs
    rbench["prop"] = outhq
    return rbench

def benchHyperChecker(config, name, bench, gen):
    def dobench(n, b):
        outdir = "out_" + n
        if os.path.exists(outdir): shutil.rmtree(outdir)
        os.mkdir(outdir)

        bench = gen(outdir, n, b)
        smvs = bench["model"]
        hq = convertFormula(config["tool"], config["path"] + "/" + bench["prop"])

        prefix = (lambda p: "/mnt/" + p) if config.get("hypercheckerDocker", False) else (lambda p: p)
        isExplicit = any(os.path.splitext(s)[1] == ".exp" for s in smvs)
        inputstr = " ".join(prefix(config["path"] + "/" + s) for s in smvs) + " "

        if config["tool"] == "HyperQube":
            k, sem = bench["k"], bench["sem"]
            hqmode = bench.get("mode", "find")
            params = f"{k} -{sem} -{hqmode}"
            command = f"hyperqb {inputstr}{prefix(hq)} {params}"
        elif config["tool"] == "AutoHyper":
            params = "--witness" if config["witness"] else ""
            debugparams = "--log" if config["debug"] else ""
            kind = "--explicit" if isExplicit else "--nusmv"
            command = f"AutoHyper {debugparams} {kind} {inputstr}{prefix(hq)} {params}"
        else:
            raise Exception("tool unsupported: " + config["tool"])

        expected = bench.get("expected")
        runmode = "docker" if config.get("hypercheckerDocker", False) else "native"
        return runBench({**config, "runmode": runmode}, n, command, expected, sem=bench.get("sem"))

    return timerBench(dobench, name, bench)

def benchHyperSmv(config, name, bench, gen):
    def dobench(n, b):
        if "slow" in b and b["slow"] and not config["slow"]: return None

        outdir = "out_" + n
        if os.path.exists(outdir): shutil.rmtree(outdir)
        os.mkdir(outdir)

        bench = gen(outdir, n, b)
        smvs = bench["model"]
        hq = bench["prop"]

        ins = " ".join(concat([["--input=" + protectPath(config["path"] + "/" + smv)] for smv in smvs]))
        inf = "--informula=" + protectPath(config["path"] + "/" + hq)

        flags = []
        if config["debug"]: flags += ["--debug=True"]
        wantWitness = config["witness"] and bench.get("expectsWitness", False)
        flags += ["--witness=true"] if wantWitness else ["--witness=false"]
        if config["hypersmvSolverDocker"]: flags += ["--docker=" + config["dockerContainer"]]
        if config["vanillaSmv"]:
            flags += ["--bisim=False", "--splitformula=nosplitformula"]
            if config["tool"] == "AutoHyper": flags += ["--ahbisim=True", "--splitinits=nosplitinit"]
        if config["noSplitFormulas"]:
            flags += ["--splitformula=nosplitformula"]
            if config["tool"] == "AutoHyper": flags += ["--bisim=False", "--ahbisim=True"]
        if config["noSplitInits"] and config["tool"] == "AutoHyper":
            flags += ["--splitinits=nosplitinits"]
        flagstr = " ".join(flags)

        opts = bench.get("opts", "")

        if config["tool"] == "AutoHyper":
            if config["vanillaSmv"]: ahopts = ""
            elif wantWitness and "ahOptsWitness" in bench: ahopts = bench["ahOptsWitness"]
            else: ahopts = bench.get("ahOpts", "")
            command = f"hypersmv ah {ins} {inf} {ahopts} {opts} {flagstr}"
        elif config["tool"] == "QBF":
            qbfopts = bench.get("qbfOpts", "")
            command = (f"hypersmv qbf -k={bench['k']} --sem={bench['sem']} "
                       f"{ins} {inf} {opts} {qbfopts} {flagstr}")
        else:
            raise Exception("tool unsupported: " + config["tool"])

        expected = bench.get("expected")
        runmode = "docker" if config.get("hypersmvDocker", False) else "native"
        return runBench({**config, "runmode": runmode}, n, command, expected, sem=bench.get("sem"))

    return timerBench(dobench, name, bench)

def benchOriginalHyperChecker(config, name, bench):
    return benchHyperChecker(config, name, bench, lambda outdir, n, b: b)

def benchHyperSmvHyperChecker(config, name, bench):
    return benchHyperSmv({**config, "path": "."}, name, bench,
                         lambda outdir, n, b: optimizeSMV(config, outdir, b))

def benchHyperAlloyHyperChecker(config, name, bench):
    return benchHyperChecker({**config, "path": "."}, name, bench,
                             lambda outdir, n, b: optimizeSMV({**config, "path": "."}, outdir,
                                                              genSMVfromHyperAlloy(config, outdir, b)))

def benchHyperSmvSolver(config, name, bench):
    return benchHyperSmv(config, name, bench, lambda outdir, n, b: b)

def benchHyperAlloySolver(config, name, bench):
    return benchHyperSmv({**config, "path": "."}, name, bench,
                         lambda outdir, n, b: genSMVfromHyperAlloy(config, outdir, b))

######## Mode dispatch ########

# cls -> (bench-group-key, runner-fn, default-cfg-overrides)
# bench-group-key indexes BENCH_GROUPS for both path and bench dict.
COLUMNS = {
    "low": {
        "AutoHyper":        ("AutoHyper",             benchOriginalHyperChecker, {"tool": "AutoHyper"}),
        "HyperQB":          ("AutoHyper",             benchOriginalHyperChecker, {"tool": "HyperQube"}),
        "HyperSmvExp":      ("AutoHyper",             benchHyperSmvSolver,       {"tool": "AutoHyper"}),
        "HyperSmvSym":      ("AutoHyper",             benchHyperSmvSolver,       {"tool": "QBF"}),
        "HyperPardinusExp": ("AutoHyperToHyperAlloy", benchHyperAlloySolver,     {"tool": "AutoHyper"}),
        "HyperPardinusSym": ("AutoHyperToHyperAlloy", benchHyperAlloySolver,     {"tool": "QBF"}),
    },
    "high": {
        "AutoHyper": ("HyperAlloy", benchHyperAlloyHyperChecker, {"tool": "AutoHyper", "vanillaSmv": True}),
        "HyperQB":   ("HyperAlloy", benchHyperAlloyHyperChecker, {"tool": "HyperQube", "vanillaSmv": True}),
        "Exp-":      ("HyperAlloy", benchHyperAlloySolver,       {"tool": "AutoHyper", "vanillaAlloy": True}),
        "Sym-":      ("HyperAlloy", benchHyperAlloySolver,       {"tool": "QBF",       "vanillaAlloy": True}),
        "Exp":       ("HyperAlloy", benchHyperAlloySolver,       {"tool": "AutoHyper"}),
        "Sym":       ("HyperAlloy", benchHyperAlloySolver,       {"tool": "QBF"}),
    },
}

ABLATION_FLAGS = {
    "C-": "noComp",
    "M-": "noMult",
    "S-": "noSymm",
    "F-": "noSplitFormulas",
    "I-": "noSplitInits",
}
ABLATION_PREFIXES = list(ABLATION_FLAGS) + [""]

def ablationBenchsKey(group):
    if group == "low":  return "AutoHyperToHyperAlloy"
    if group == "high": return "HyperAlloy"
    raise Exception("ablation group unexpected: " + group)

def applyAblation(cls, cfg):
    cfg = dict(cfg)
    for prefix, flag in ABLATION_FLAGS.items():
        if cls.startswith(prefix):
            cfg[flag] = True
    return cfg

# Concrete timeout lists per (mode, column), loaded from timeouts.json.
# Ablation timeouts live under TIMEOUTS_DATA["ablation"][group][cls].
with open("timeouts.json") as _f:
    TIMEOUTS_DATA = json.load(_f)

def timeoutsFor(mode, cls, group=None):
    if mode == "ablation":
        return set(TIMEOUTS_DATA["ablation"][group][cls])
    return set(TIMEOUTS_DATA[mode][cls])

######## Benchmark GUI ########

errorRes   = {"symbol": "! msg", "message": "see logs", "color": "error"}
skippedRes = {"symbol": "ℹ msg", "message": "skipped ", "color": "running"}

spinner = itertools.cycle(['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏'])

def fmtTime(t):
    if t < 10:   return f"{t:.5f}s"
    if t < 100:  return f"{t:.4f}s"
    if t < 1000: return f"{t:.3f}s"
    return f"{t:.2f}s"

class BenchmarkGUI:
    def __init__(self, stdscr, benchmarks, classes, num_iterations):
        self.stdscr = stdscr
        self.benchmarks = list(benchmarks)
        self.classes = list(classes)
        self.num_iterations = num_iterations

        curses.start_color()
        curses.use_default_colors()
        curses.init_pair(1, curses.COLOR_GREEN,   -1)
        curses.init_pair(2, curses.COLOR_CYAN,    -1)
        curses.init_pair(3, curses.COLOR_MAGENTA, -1)
        curses.init_pair(4, curses.COLOR_RED,     -1)
        curses.init_pair(5, curses.COLOR_YELLOW,  -1)
        curses.init_pair(6, curses.COLOR_WHITE,   -1)
        self.colors = {
            "ok":      curses.color_pair(1),
            "ko":      curses.color_pair(2),
            "warning": curses.color_pair(3),
            "error":   curses.color_pair(4),
            "running": curses.color_pair(5),
            "default": curses.color_pair(6),
        }

        # two rows per benchmark: result + sizes
        self.results = [[{"message": "[ waiting...      ]", "color": self.colors["default"]} for _ in self.classes] for _ in self.benchmarks]
        self.sizes   = [[{"message": "[ waiting...      ]", "color": self.colors["default"]} for _ in self.classes] for _ in self.benchmarks]
        self.running = True
        self.completed = False
        self.start_time = time.perf_counter()

        self.pad_h = (len(self.benchmarks) * 2) + 10
        self.pad_w = 31 + (len(self.classes) * 20) + 20
        self.pad = curses.newpad(self.pad_h, self.pad_w)

        self.top_y = 0
        self.left_x = 0
        self.sh = self.sw = 0
        self.current_spinner = "-"
        self.worker_exception = None

    def run_benchmark(self, benchmark, cls):
        raise NotImplementedError

    def worker_logic(self):
        try:
            for i, bench in enumerate(self.benchmarks):
                for j, cls in enumerate(self.classes):
                    result = None
                    times = []
                    has_error = False
                    r = None
                    for it in range(self.num_iterations):
                        its = (str(it + 1) + "/" + str(self.num_iterations)).rjust(7)
                        running = {"message": f"[ iter {its}    ]", "color": self.colors["running"]}
                        self.results[i][j] = running
                        self.sizes[i][j]   = running
                        r = self.run_benchmark(bench, cls)
                        if r is None:
                            r = skippedRes; has_error = True; break
                        if "result" in r:
                            times.append(r["time"])
                            if result is None: result = r["result"]
                            elif result != r["result"]:
                                has_error = True; break
                        else:
                            has_error = True; break

                    if has_error:
                        symbol = r["symbol"]; message = r["message"]; color = self.colors[r["color"]]
                        sizemsg = "N/A"
                    else:
                        conc = r.get("conclusivity")
                        if   conc is None: symbol = "✓    " if r["got"] else "✗    "
                        elif conc:         symbol = "✓✓   " if r["got"] else "✗✗   "
                        else:              symbol = "✓?   " if r["got"] else "✗?   "
                        color = self.colors["ok"] if result else self.colors["ko"]
                        message = fmtTime(sum(times) / len(times))
                        sizemsg = r.get("sizes") or "N/A"

                    self.results[i][j] = {"message": f"[ {symbol}: {message} ]", "color": color}
                    self.sizes[i][j]   = {"message": f"[ {sizemsg:^15} ]",       "color": color}
        except Exception as e:
            self.worker_exception = e
        finally:
            self.completed = True
            self.elapsed_time = time.perf_counter() - self.start_time

    def draw_to_pad(self):
        self.pad.erase()
        self.pad.addstr(0, 0, f"{'Benchmark':<30}", self.colors["default"])
        for j, cls in enumerate(self.classes):
            self.pad.addstr(0, 31 + j * 20, f"{cls:^18}", self.colors["default"])
        self.pad.hline(1, 0, '-', 31 + len(self.classes) * 20, self.colors["default"])

        for i, bench in enumerate(self.benchmarks):
            row = (i * 2) + 2
            self.pad.addstr(row,     0, f"{bench:<30}", self.colors["default"])
            self.pad.addstr(row + 1, 0, f"{'↪ sizes':<30}", self.colors["default"])
            for j, _ in enumerate(self.classes):
                res = self.results[i][j]
                sz  = self.sizes[i][j]
                self.pad.addstr(row,     31 + j * 20, res["message"], res["color"])
                self.pad.addstr(row + 1, 31 + j * 20, sz["message"],  sz["color"])

        footer_y = (len(self.benchmarks) * 2) + 3
        self.pad.hline(footer_y, 0, '-', 31 + len(self.classes) * 20, self.colors["default"])
        if self.completed:
            t = time.strftime('%Hh:%Mm:%Ss', time.gmtime(self.elapsed_time))
            msg = f"All benchmarks completed in {t}. Press 'q' to exit."
        else:
            msg = "Benchmarks running." + self.current_spinner + ". Press 'q' to exit."
        self.pad.addstr(footer_y + 1, 0, msg, self.colors["default"])

    def run_all(self):
        try:
            self.stdscr.keypad(True)
            self.stdscr.nodelay(True)
            curses.curs_set(0)

            thread = threading.Thread(target=self.worker_logic, daemon=True)
            thread.start()

            while self.running:
                if self.worker_exception:
                    raise RuntimeError(f"Background worker crashed: {self.worker_exception}")
                self.sh, self.sw = self.stdscr.getmaxyx()
                self.draw_to_pad()
                try: self.pad.refresh(self.top_y, self.left_x, 0, 0, self.sh - 1, self.sw - 1)
                except curses.error: pass

                key = self.stdscr.getch()
                if   key == curses.KEY_UP:    self.top_y  = max(0, self.top_y - 1)
                elif key == curses.KEY_DOWN:  self.top_y  = min(max(0, self.pad_h - self.sh), self.top_y + 1)
                elif key == curses.KEY_LEFT:  self.left_x = max(0, self.left_x - 2)
                elif key == curses.KEY_RIGHT: self.left_x = min(max(0, self.pad_w - self.sw), self.left_x + 2)
                elif key == ord('q'):
                    self.save_screen_to_file(self.pad, "report.txt")
                    self.running = False

                self.current_spinner = next(spinner)
                time.sleep(0.1)
        finally:
            cleanup_all()
            time.sleep(0.1)

    def save_screen_to_file(self, win, filename):
        h, _ = win.getmaxyx()
        with open(filename, 'w', encoding='utf-8') as f:
            for y in range(h):
                try:
                    line = win.instr(y, 0).decode('utf-8').rstrip()
                    f.write(line + '\n')
                except curses.error:
                    continue

class DispatchGUI(BenchmarkGUI):
    def __init__(self, stdscr, config):
        self.config = config
        mode = config["mode"]

        if mode not in ("low", "high"):
            raise Exception("mode must be 'low' or 'high'")
        ablation = config.get("ablation")
        if ablation is not None and ablation not in ("Exp", "Sym"):
            raise Exception("ablation must be 'Exp' or 'Sym' (or unset)")

        if ablation is None:
            cols_all = list(COLUMNS[mode])
            cols = [c for c in cols_all if (not config["col"]) or c == config["col"]]
            row_keys = []
            for c in cols:
                groupKey = COLUMNS[mode][c][0]
                for k in BENCH_GROUPS[groupKey][1].keys():
                    if k not in row_keys: row_keys.append(k)
        else:
            cols_all = [p + ablation for p in ABLATION_PREFIXES]
            cols = [c for c in cols_all if (not config["col"]) or c == config["col"]]
            row_keys = list(BENCH_GROUPS[ablationBenchsKey(mode)][1].keys())

        if config["row"]: row_keys = [r for r in row_keys if r == config["row"]]
        super().__init__(stdscr, row_keys, cols, config["nruns"])

        if not os.path.exists("logs"): os.makedirs("logs")

    def run_benchmark(self, benchmark, cls):
        cwd = os.getcwd()
        with open("logs/" + benchmark + cls, "w+") as f:
            try:
                mode = self.config["mode"]
                ablation = self.config.get("ablation")

                if ablation is None:
                    groupKey, runner, overrides = COLUMNS[mode][cls]
                    path, benchs = BENCH_GROUPS[groupKey]
                    if benchmark not in benchs: return skippedRes
                    bench = benchs[benchmark]
                    cfg = {**self.config, "logfile": f, "path": path, **overrides}
                    if benchmark in timeoutsFor(mode, cls) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out", f); return skippedRes
                else:
                    groupKey = ablationBenchsKey(mode)
                    path, benchs = BENCH_GROUPS[groupKey]
                    bench = benchs[benchmark]
                    runner = benchHyperAlloySolver
                    tool = "AutoHyper" if ablation == "Exp" else "QBF"
                    cfg = {**self.config, "logfile": f, "path": path, "tool": tool}
                    cfg = applyAblation(cls, cfg)
                    if mode == "high" and ablation == "Sym":
                        cfg["hypersmvSolverDocker"] = True
                    if benchmark in timeoutsFor("ablation", cls, mode) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out", f); return skippedRes

                return runner(cfg, benchmark, bench)
            except Exception as e:
                printLog(e, f)
                os.chdir(cwd)
                return errorRes

######## CLI ########

def run(
    mode="low",
    ablation=None,
    nruns=1,
    row=None,
    col=None,
    benchmark=None,  # alias for row, kept for compat
    debug=True,
    witness=True,
    timeout=200,
    skipTimeout=True,
    slow=False,
    vanillaSmv=False,
    vanillaAlloy=False,
    noComp=False,
    noMult=False,
    noSymm=False,
    noSplitFormulas=False,
    noSplitInits=False,
    hypersmvDocker=False,
    hypersmvSolverDocker=False,
    hypercheckerDocker=False,
    dockerContainer="hyperalloy/hyperalloy",
):
    """Run HyperAlloy / HyperPardinus benchmarks.

    Args:
        mode: 'low' (benchsAutoHyper as model checker) or 'high' (idiomatic HyperAlloy).
        ablation: If set ('Exp' or 'Sym'), run ablation columns over the chosen mode's bench set.
        nruns: Iterations per benchmark; reported time is the average.
        row: Run only this benchmark name. (alias: benchmark)
        col: Run only this column name.
        debug: Pass debug flags to invoked tools and write per-(bench,col) logs to ./logs.
        witness: Compute witnesses where the bench supports them.
        timeout: Seconds before each command-line invocation is killed.
        skipTimeout: Skip benchmarks pre-marked as known-timeouts.
        slow: Include benchmarks marked 'slow' in the JSON.
        vanillaSmv: Disable all HyperSmv optimizations.
        vanillaAlloy: Disable all HyperPardinus optimizations.
        noComp / noMult / noSymm: Disable individual HyperPardinus optimizations.
        noSplitFormulas / noSplitInits: Disable individual HyperSmv optimizations.
        hypersmvDocker: Run hypersmv inside docker.
        hypersmvSolverDocker: Run solvers invoked by hypersmv inside docker.
        hypercheckerDocker: Run the original hyperchecker inside docker.
        dockerContainer: Docker image name for the above.
    """
    if isinstance(ablation, str):
        ablation = ablation[:1].upper() + ablation[1:].lower() if ablation else ablation
    cfg = {
        "mode": mode, "ablation": ablation, "nruns": nruns,
        "row": row or benchmark, "col": col,
        "debug": debug, "witness": witness,
        "timeout": timeout, "skipTimeout": skipTimeout, "slow": slow,
        "vanillaSmv": vanillaSmv, "vanillaAlloy": vanillaAlloy,
        "noComp": noComp, "noMult": noMult, "noSymm": noSymm,
        "noSplitFormulas": noSplitFormulas, "noSplitInits": noSplitInits,
        "hypersmvDocker": hypersmvDocker,
        "hypersmvSolverDocker": hypersmvSolverDocker,
        "hypercheckerDocker": hypercheckerDocker,
        "dockerContainer": dockerContainer,
    }

    def go(stdscr):
        curses.curs_set(0)
        DispatchGUI(stdscr, cfg).run_all()
    curses.wrapper(go)

if __name__ == '__main__':
    fire.Fire(run)
