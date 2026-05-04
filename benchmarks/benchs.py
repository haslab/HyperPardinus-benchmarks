#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from glob import glob
import subprocess
#import threading
#from io import StringIO
import re
#import pandas as pd
import fire
import shutil
import json
import time
import curses

######## General Utils ########

def printLog(x,f):
    if f: print(x,file=f)
    else: print(x)

def timerBench(func, *args, **kwargs):

    start_time = time.perf_counter()
    result = func(*args, **kwargs)
    end_time = time.perf_counter()
    elapsed_time = end_time - start_time
    
    return {**result, "time" : elapsed_time }

def protectPath(p):
    return "\""+p+"\""

def concat(xxs):
    r = []
    for xs in xxs:
        r.extend(xs)
    return r

timeoutOpCode = 124

def runCommand(secs,f,command):
    printLog(command,f)
    
    try:
        result = subprocess.run(command, shell=True, capture_output=True, text=True,timeout=secs)
        printLog(result.stdout,f)
        printLog(result.stderr,f)
        return result
    except subprocess.TimeoutExpired as e:
        return subprocess.CompletedProcess(
                    args = command,
                    returncode = timeoutOpCode,
                    stdout = (e.stdout.decode() if e.stdout else ""),
                    stderr = (e.stderr.decode() if e.stderr else "") + f"Timed out after {secs} seconds"
                )

#def runDockerInterative():
#    pwd = os.getcwd()
#    os.system("docker run -v "+pwd+":/mnt -it hyperalloy/hyperalloy")

def runDockerCommand(container,secs,f,command):
    pwd = os.getcwd()
    result = runCommand(secs,f,"docker run -v "+pwd+":/mnt " + container + " /bin/bash -c \""+command+"\"")
    return result

def runCommandMode(config,command):
    runmode = config["runmode"]
    secs = config["timeout"]
    f = config["logfile"]
    if runmode=="docker": result = runDockerCommand(config["dockerContainer"],secs,f,command)
    elif runmode=="native": result = runCommand(secs,f,command)
    else: raise Exception("runmode unsupported: " + runmode)
    return result

######## SMV / Formula Utils ########

def toolExt(tool):
    if tool=="HyperQube": return ".hq"
    elif tool=="AutoHyper": return ".ah"
    elif tool=="QBF": return ".qcir"
    else: raise Exception("mode unsupported: " + tool)

def parseFormulaHeader(inf):
    with open(inf,"r") as f:
        first_line = f.readline().strip()
        return [ s[-1] for s in first_line.split(".") if s ]

def lookupSMV(v,xs):
    return [ x for x in xs if x.endswith(v+".smv") ][0]
def sortSMVs(xs,vs):
    return [ lookupSMV(v,xs) for v in vs ]

#def dropFileHead(n,inf,outf):
#    runCommand("tail -n +" + str(n) + " " + inf + " > " + outf)
#    return outf
    
def convertFormula(tool,inhq):
    filename,oldExt = os.path.splitext(inhq)
    newExt = toolExt(tool)
    if newExt==oldExt: return inhq
    outhq = filename+newExt
    if os.path.exists(outhq): return outhq
    
    with open(inhq,"r") as inf:
        s = inf.read()
        with open(outhq,"w") as outf:
            if oldExt==".ah" and newExt==".hq":
                s = s.replace("{","*")
                s = s.replace("}","*")
                s = s.replace("\"","")
                s = s.replace("_A","[A]")
                s = s.replace("_B","[B]")
                s = s.replace("_C","[C]")
                s = s.replace("&","/\\")
                s = s.replace("|","\\/")
                s = s.replace("!","~")
            else: raise Exception("conversion unsupported from " + oldExt + " to " + newExt)
            outf.write(s)
    return outhq

######## Benchmark Data ########

def readBenchs(jsonfile):
    with open(jsonfile) as f:
        dta = json.load(f)
        path = dta["path"]
        benchs = dta["benchs"]
    return path,benchs

pathAutoHyper,benchsAutoHyper = readBenchs("benchsAutoHyper.json")
pathAutoHyperToHyperAlloy,benchsAutoHyperToHyperAlloy = readBenchs("benchsAutoHyperToHyperAlloy.json")
pathHyperAlloy,benchsHyperAlloy = readBenchs("benchsHyperAlloy.json")

######## Benchmark Utils ########

def parseOutput(tool,out):
    lines = [ l for l in out.splitlines() if l ]
    lines.reverse()
    status = None
    if tool=="AutoHyper":
        for l in lines:
            if l.startswith("SAT"): status=True; break
            elif l.startswith("UNSAT"): status=False; break
    elif tool=="QBF":
        for l in lines:
            if l.startswith("SAT"): status=True; break
            elif l.startswith("UNSAT"): status=False; break
    elif tool=="HyperQube":
        if "r SAT" in out: status=True
        elif "r UNSAT" in out: status=False
    conclusivity = True if "(conclusive" in out else False if "(inconclusive" in out else None
    sizes = None
    for l in lines:
        if l.startswith("Model size"): sizes = l[len("Model size"):].strip(); break
    return status,conclusivity,sizes

def runBench(config,n,command,expected):
    result = runCommandMode(config,command)
    if result.returncode == timeoutOpCode:
        return { "symbol" : "⏱ msg", "message" : "timeout ", "color" : "warning" }
    txt = result.stdout + "\n" + result.stderr
    status,conclusivity,sizes = parseOutput(config["tool"],txt)
    
    if status is None:
        return { "symbol" : "! err", "message" : "see logs", "color" : "error" }
    if expected != status:
        msg = f"Expected {expected} but got {status}\n"
        if config["logfile"]: print(msg,file=config["logfile"])
        else: print(msg)
        return { "expected" : expected, "got" : status, "result" : False, "conclusivity" : conclusivity, "sizes" : sizes }
    else: return { "expected" : expected, "got" : status, "result" : True, "conclusivity" : conclusivity, "sizes" : sizes }

def genSMVfromHyperAlloy(config,outdir,bench):
    filepath = os.path.join(config["path"],bench["prop"])
    cmd = bench["cmd"]
    #if config["runmode"]=="docker":
    #    hostfile = "/mnt/"+filepath
    #    hostoutdir = "/mnt/" + outdir
    #elif config["runmode"]=="native":
    hostfile = "../"+filepath
    hostoutdir = outdir
    #else: raise Exception("runmode unsupported: " + config["runmode"])
    
    pwd = os.getcwd()
    os.chdir(pwd + "/" + hostoutdir)
    opts = "" if config["vanillaAlloy"] else bench.get("alloyOpts",{}).get(config["tool"],"")
    vanillaopts = " --compositionoff --multboundsoff -y 0 " if config["vanillaAlloy"] else ""
    nocompopts = " --compositionoff " if config["noComp"] else ""
    nomultsopts = " --multboundsoff " if config["noMult"] else ""
    nosymmopts = " -y 0 " if config["noSymm"] else ""
    debugparams = "-d" if config["debug"] else ""
    command = "hyperalloy " + debugparams + " exec " + opts + " " + vanillaopts + nocompopts + nomultsopts + nosymmopts + " -s electrod.hypermcts -c " + str(cmd) + " -f " + hostfile     
    
    result = runCommandMode(config,command)
    
    os.chdir(pwd)

    rbench = bench.copy()
    hps = glob(outdir + "/*/*.hp")
    if (len(hps) == 1): hp = hps[0]
    else:
        raise Exception("hyperalloy produced " + str(len(hps)) + " hyperformulas for " + outdir + " " + str(bench) + str(config))
    quants = parseFormulaHeader(hp)
    smvs = glob(outdir + "/*.smv")
    rbench["model"] = sortSMVs(smvs,quants)
    rbench["prop"] = hp
    return rbench

def optimizeSMV(config,outdir,bench):
    smvs = bench["model"]
    hq = bench["prop"]
    
    debugparams = "--debug=True" if config["debug"] else ""
    vanillaparams = "--bisim=False --splitformula=nosplitformula" if config["vanillaSmv"] else ""
    nosplitformulasparams = " --splitformula=nosplitformula " if config["noSplitFormulas"] else ""
    nosplitinitsparams =  "--splitinits=nosplitinits " if config["noSplitInits"] else ""
    
    ins  = " ".join(concat([ ["-i",config["path"] + "/" + smv] for i,smv in enumerate(smvs) ]))
    if config["tool"]=="QBF":
        k = bench["k"]
        sem = bench["sem"]
        outs=" -k="+str(k) + " " + "--sem=" + sem
        outsmvs = []
    else:
        if config["tool"]=="AutoHyper": outext = "exp"
        elif config["tool"]=="HyperQube": outext = "smv"
        else: raise Exception("tool unsupported")
        outs = " ".join(concat([ ["-o",outdir + "/" + str(i)+"."+outext] for i,smv in enumerate(smvs) ]))
        outsmvs = [ outdir + "/" + str(i)+"."+outext for i,smv in enumerate(smvs) ]
    
    outhq = outdir + "/" + "".join([ str(i) for i,smv in enumerate(smvs) ])+toolExt(config["tool"])
    tool = "QCIR" if config["tool"]=="QBF" else config["tool"]
    
    runCommandMode(config,"hypersmv tomc " + ins + " " + outs + " -H=" + tool +" -I " + config["path"] + "/" + hq + " -O " + outhq + " " + debugparams + " " + vanillaparams + nosplitformulasparams + nosplitinitsparams)
    
    rbench = bench.copy()
    rbench["model"] = outsmvs
    rbench["prop"] = outhq
    return rbench

def benchHyperChecker(config,name,bench,gen):
    
    def dobench(n,b) : 
        outdir = "out_"+n
        if os.path.exists(outdir): shutil.rmtree(outdir)
        os.mkdir(outdir)
        
        bench = gen(outdir,n,b)
        
        smvs = bench["model"]
        hq = convertFormula(config["tool"],config["path"] + "/" + bench["prop"])
        inputstr = ""
        def addPrefix(p):
            if config.get("hypercheckerDocker",False): return "/mnt/"+p
            else: return p
        
        isExplicit = False
        for smv in smvs:
            filename,oldExt = os.path.splitext(smv)
            if oldExt == ".exp": isExplicit = True
                
            smvfile = addPrefix(config["path"]+"/"+smv)
            inputstr += smvfile + " "
        
        if config["tool"]=="HyperQube":
            k = bench["k"]
            sem = bench["sem"]
            if "mode" in bench: hqmode = bench["mode"]
            else: hqmode = "find"
            params=str(k) + " -" + sem + " -"+hqmode
            command = "hyperqb " + inputstr + addPrefix(hq) +" "+params
        elif config["tool"]=="AutoHyper":
            params="--witness" if config["witness"] else ""
            debugparams = "--log" if config["debug"] else ""
            if isExplicit:
                command = "AutoHyper " + debugparams + " --explicit " + inputstr +addPrefix(hq)+" "+params
            else:
                command = "AutoHyper " + debugparams + " --nusmv " + inputstr +addPrefix(hq)+" "+params
#        elif config["tool"]=="QBF":
#            params = "--partial-assignment" if witness else ""
#            prop = addPrefix(config["path"] + "/" + bench["prop"])
#            command = "quabs " + params + " " + prop
            
        else: raise Exception("tool unsupported: " + config["tool"])
        
        expected = bench["expected"] if "expected" in bench else None
        
        runmode = "docker" if config.get("hypercheckerDocker",False) else "native"
        return runBench({**config, "runmode" : runmode },n,command,expected)
    
    return timerBench(dobench,name,bench)

def benchHyperSmv(config,name,bench,gen):
    
    def dobench(n,b):
        
        if not "slow" in b or b["slow"]==False or config["slow"]:
        
            outdir = "out_"+n
            if os.path.exists(outdir): shutil.rmtree(outdir)
            os.mkdir(outdir)
            
            bench = gen(outdir,n,b)
            
            smvs = bench["model"]
            hq = bench["prop"]
            
            ins  = " ".join(concat([ ["--input=" + protectPath (config["path"] + "/" + smv)] for i,smv in enumerate(smvs) ]))
            inf = "--informula=" + protectPath (config["path"] + "/" + hq)
            
            debugparams = "--debug=True" if config["debug"] else ""
            witnessparams="--witness=true" if config["witness"] and bench["expectsWitness"] else "--witness=false"
            dockerparams= "--docker=" + config["dockerContainer"] if config["hypersmvSolverDocker"] else ""
            vanillaparams = ("--bisim=False --ahbisim=True --splitformula=nosplitformula" + "--splitinits=nosplitinit" if config["tool"] == "AutoHyper" else "") if config["vanillaSmv"] else ""
            nosplitformulasparams = " --splitformula=nosplitformula " + (" --bisim=False --ahbisim=True" if config["tool"]=="AutoHyper" else "") if config["noSplitFormulas"] else ""
            nosplitinitsparams = " --splitinits=nosplitinits " if config["noSplitInits"] and config["tool"]=="AutoHyper" else ""
            
            opts = bench["opts"] if "opts" in bench else ""
            
            if config["tool"]=="AutoHyper":
                ahopts = "" if config["vanillaSmv"] else bench["ahOptsWitness"] if config["witness"] and bench["expectsWitness"] and "ahOptsWitness" in bench else bench["ahOpts"] if "ahOpts" in bench else "" 
                command = "hypersmv ah " + ins + " " + inf + " " + ahopts + " " + opts + " " + debugparams + " " + witnessparams + " " + vanillaparams + nosplitformulasparams + nosplitinitsparams + " " + dockerparams
            elif config["tool"]=="QBF":
                qbfopts = bench["qbfOpts"] if "qbfOpts" in bench else ""
                k = bench["k"]
                sem = bench["sem"]
                command = "hypersmv qbf -k="+str(k) + " " + "--sem=" + sem + " " + ins + " " + inf + " " + opts + " " + qbfopts + " " + debugparams + " " + witnessparams + " " + vanillaparams + nosplitformulasparams + nosplitinitsparams + " " + dockerparams
                
            expected = bench["expected"] if "expected" in bench else None
            
            runmode = "docker" if config.get("hypersmvDocker",False) else "native"
            return runBench({**config, "runmode" : runmode },n,command,expected)
    
    return timerBench(dobench,name,bench)

def benchOriginalHyperChecker(config,name,bench):
    gen = lambda outdir,n,b : b
    return benchHyperChecker(config,name,bench,gen)
    
def benchHyperSmvHyperChecker(config,name,bench):
    gen = lambda outdir,n,b : optimizeSMV(config,outdir,b)
    return benchHyperSmv({**config, "path": "."},name,bench,gen)

def benchHyperAlloyHyperChecker(config,name,bench):
    gen = lambda outdir,n,b : optimizeSMV({**config, "path": "."},outdir,genSMVfromHyperAlloy(config,outdir,b))
    return benchHyperChecker({**config, "path": "."},name,bench,gen)

def benchHyperSmvSolver(config,name,bench):
    gen = lambda outdir,n,b : b
    return benchHyperSmv(config,name,bench,gen)

def benchHyperAlloySolver(config,name,bench):
    gen = lambda outdir,n,b : genSMVfromHyperAlloy(config,outdir,b)
    return benchHyperSmv({**config, "path": "."},name,bench,gen)

defaultBenchConfig = {
      "vanillaSmv" : False # do not apply HyperSmv optimizations
    , "noSplitFormulas" : False # do not apply HyperSmv split formulas optimization
    , "noSplitInits" : False # do not apply HyperSmv split initial states optimization
    , "vanillaAlloy" : False # do not apply HyperPardinus optimizations
    , "noComp" : False # do not apply HyperPardinus composition optimization
    , "noMult" : False # do not apply HyperPardinus multiplicity bounds optimization
    , "noSymm" : False # do not apply HyperPardinus symmetry breaking optimization
    , "debug" : False # print debugging info
    , "hypersmvDocker" : False # if hypersmv runs inside docker
    , "hypersmvSolverDocker" : False #if hypersmv runs solvers inside docker
    , "hypercheckerDocker": False # if original hyperchecker runs inside docker
    , "runmode" : "native"
    , "dockerContainer": "hyperalloy/hyperalloy" # name of the docker container
    , "path" : "." #PWD for the executables
    , "tool" : "" # hyper tool to run
    , "witness" : False # compute witnesses
    , "timeout": 200 # timeout in seconds per command-line invocation
    , "skipTimeout" : True # do not run testes that will timeout
    , "logfile" : None
    , "nruns": 1 # how many times to run each benchmark
    }

######## Benchmark GUI ########

class BenchmarkGUI:
    def __init__(self, stdscr, benchmarks, classes, num_iterations):
        self.stdscr = stdscr
        self.benchmarks = benchmarks
        self.classes = classes
        self.num_iterations = num_iterations
        self.colors = {}

    def setup_colors(self):
        curses.start_color()
        curses.init_pair(1, curses.COLOR_GREEN, curses.COLOR_BLACK)   # OK
        curses.init_pair(2, curses.COLOR_CYAN, curses.COLOR_BLACK)  # KO
        curses.init_pair(3, curses.COLOR_MAGENTA, curses.COLOR_BLACK)  # WARNING
        curses.init_pair(4, curses.COLOR_RED, curses.COLOR_BLACK)     # ERROR
        curses.init_pair(5, curses.COLOR_YELLOW, curses.COLOR_BLACK)  # RUNNING
        curses.init_pair(6, curses.COLOR_WHITE, curses.COLOR_BLACK)   # DEFAULT

        self.colors = {
            "ok": curses.color_pair(1),
            "ko": curses.color_pair(2),
            "warning": curses.color_pair(3),
            "error": curses.color_pair(4),
            "running": curses.color_pair(5),
            "default": curses.color_pair(6)
        }

    def draw_header(self):
        self.stdscr.addstr(0, 0, f"{'Benchmark':<30}", self.colors["default"])
        for j, cls in enumerate(self.classes):
            self.stdscr.addstr(0, 31 + j * 20, f"{cls:^18}", self.colors["default"])
        self.stdscr.hline(1, 0, '-', 31 + len(self.classes) * 20)

    def draw_initial_grid(self):
        for i, bench in enumerate(self.benchmarks):
            self.stdscr.addstr((i*2) + 2, 0, f"{bench:<30}")
            for j, cls in enumerate(self.classes):
                self.stdscr.addstr((i*2) + 2, 31 + j * 20, "[ waiting...      ]", self.colors["default"])
            lbl = "↪ sizes"
            self.stdscr.addstr((i*2) + 3, 0, f"{lbl:<30}")
            for j, cls in enumerate(self.classes):
                self.stdscr.addstr((i*2) + 3, 31 + j * 20, "[ waiting...      ]", self.colors["default"])
        self.stdscr.refresh()

    def run_benchmark(self, benchmark, cls):
        """Simulate a single test iteration."""
        time.sleep(0.2)
        if random.random() < 0.8:
            return { "expected" : True, "result" : True, "time" : random.uniform(100, 300) }
        else:
            return { "symbol" : "! err" , "message" : "error   ", "color" : "error" }

    def run_all(self):
        self.setup_colors()
        self.draw_header()
        self.draw_initial_grid()

        def showits(i,j,size):
            return (str(i)+"/"+str(j)).rjust(size)

        for i, bench in enumerate(self.benchmarks):
            for j, cls in enumerate(self.classes):
                result = None
                times = []
                has_error = False

                for it in range(self.num_iterations):
                    its = showits(it+1,self.num_iterations,7)
                    self.stdscr.addstr((i*2) + 2, 31 + j * 20,f"[ iter {its}    ]", self.colors["running"])
                    self.stdscr.addstr((i*2) + 3, 31 + j * 20,f"[ iter {its}    ]", self.colors["running"])
                    self.stdscr.refresh()

                    r = self.run_benchmark(bench, cls) 
                    if "result" in r:
                        times.append(r["time"])
                        if result is None:
                            result = r["result"]
                        elif result != r["result"]:
                            has_error = True
                            break    
                    else:
                        has_error = True
                        break

                # Compute and display final result
                if has_error: 
                    symbol=r["symbol"]
                    message=r["message"]
                    color=self.colors[r["color"]]
                else:
                    if not "conclusivity" in r or r["conclusivity"] is None: symbol = "✓    " if r["got"] else "✗    "
                    elif r["conclusivity"]: symbol = "✓✓   " if r["got"] else "✗✗   "
                    else: symbol = "✓?   " if r["got"] else "✗?   "
                    color = self.colors["ok"] if result else self.colors["ko"]
                
                    bst = sum(times) / len(times)
                    if bst < 10:
                        message = f"{bst:.5f}s"
                    elif bst < 100:
                        message = f"{bst:.4f}s"
                    elif bst < 1000:
                        message = f"{bst:.3f}s"
                    
                self.stdscr.addstr((i*2) + 2, 31 + j * 20,f"[ "+symbol+f": {message} ]", color)
                sizemessage = r["sizes"] if "sizes" in r and not r["sizes"] is None else "N/A"
                self.stdscr.addstr((i*2) + 3, 31 + j * 20,f"[ {sizemessage:^15} ]", color)
                self.stdscr.refresh()

        self.stdscr.addstr(len(self.benchmarks)*2 + 3, 0, "All benchmarks completed. Press any key to exit.")
        self.stdscr.getch()

######## Benchmark Results ########

errorRes = { "symbol" : "! msg", "message" : "see logs", "color" : "error" }
skippedRes = { "symbol" : "ℹ msg", "message" : "skipped ", "color" : "running" }

class LowBenchmarkGUI(BenchmarkGUI):
    
    def __init__(self, stdscr, config):
            super().__init__(stdscr, benchsAutoHyper.keys(), ["AutoHyper","HyperQB","HyperSmvExp","HyperSmvSym","HyperPardinusExp","HyperPardinusSym"] ,config["nruns"])
            self.config = {**config }
            if not os.path.exists("logs"): os.makedirs("logs")
    
    def run_benchmark(self, benchmark, cls):
        logfile = "logs/"+benchmark+cls
        cwd = os.getcwd()
        with open(logfile,"w+") as f:
            if self.config["col"] and not (cls == self.config["col"]): return skippedRes
            if self.config["benchmark"] and not (benchmark == self.config["benchmark"]): return skippedRes
            try:
                if cls=="AutoHyper":
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f, "path": pathAutoHyper }
                    bench = benchsAutoHyper[benchmark]
                    res = benchOriginalHyperChecker(cfg,benchmark,bench)
                elif cls=="HyperQB":
                    cfg = {**self.config, "tool": "HyperQube", "logfile" : f, "path": pathAutoHyper} #, "hypercheckerDocker": True }
                    bench = benchsAutoHyper[benchmark]
                    res = benchOriginalHyperChecker(cfg,benchmark,bench)
                elif cls=="HyperSmvExp":
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f, "path": pathAutoHyper }
                    bench = benchsAutoHyper[benchmark]
                    res = benchHyperSmvSolver(cfg,benchmark,bench)
                elif cls=="HyperSmvSym":
                    cfg = {**self.config, "tool": "QBF", "logfile" : f, "path": pathAutoHyper} #, "hypersmvSolverDocker" : True }
                    bench = benchsAutoHyper[benchmark]
                    res = benchHyperSmvSolver(cfg,benchmark,bench)
                elif cls=="HyperPardinusExp":
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f, "path": pathAutoHyperToHyperAlloy }
                    bench = benchsAutoHyperToHyperAlloy[benchmark]
                    res = benchHyperAlloySolver(cfg,benchmark,bench)
                elif cls=="HyperPardinusSym":
                    cfg = {**self.config, "tool": "QBF", "logfile" : f, "path": pathAutoHyperToHyperAlloy} #, "hypersmvSolverDocker" : True }
                    bench = benchsAutoHyperToHyperAlloy[benchmark]
                    res = benchHyperAlloySolver(cfg,benchmark,bench)
            except Exception as e:
                printLog(e,f)
                os.chdir(cwd)
                return errorRes
        
        return res
        
class HighBenchmarkGUI(BenchmarkGUI):
    
    def __init__(self, stdscr, config):
            allcols = ["AutoHyper","HyperQB","Exp-","Sym-","Exp","Sym"]
            cols = [ col for col in allcols if config["col"] == col ]
            super().__init__(stdscr, benchsHyperAlloy.keys(), cols ,config["nruns"])
            self.config = {**config, "path" : pathHyperAlloy }
            if not os.path.exists("logs"): os.makedirs("logs")
    
    def run_benchmark(self, benchmark, cls):
        logfile = "logs/"+benchmark+cls
        cwd = os.getcwd()
        with open(logfile,"w+") as f:
            if self.config["col"] and not (cls == self.config["col"]): return skippedRes
            if self.config["benchmark"] and not (benchmark == self.config["benchmark"]): return skippedRes
            try:
                if cls=="AutoHyper":
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f, "vanillaSmv" : True }
                    bench = benchsHyperAlloy[benchmark]
                    def timeouts(s): return s.endswith("ni_1") or s.endswith("gni_2") or s.endswith("gni_3") or s.endswith("robust") or s.endswith("enemies") or s=="robot_two"
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloyHyperChecker(cfg,benchmark,bench)
                elif cls=="HyperQB":
                    cfg = {**self.config, "tool": "HyperQube", "logfile" : f, "vanillaSmv" : True } #, "hypercheckerDocker": True, }
                    bench = benchsHyperAlloy[benchmark]
                    def timeouts(s): return s.startswith("easychair") or s.endswith("robust")
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloyHyperChecker(cfg,benchmark,bench)
                elif cls=="Exp-":
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f, "vanillaAlloy" : True }
                    bench = benchsHyperAlloy[benchmark]
                    def timeouts(s): return s.startswith("easychair") or s.startswith("robot")
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(cfg,benchmark,bench)
                elif cls=="Sym-":
                    cfg = {**self.config, "tool": "QBF", "logfile" : f, "vanillaAlloy" : True} #, "hypersmvSolverDocker" : True }
                    bench = benchsHyperAlloy[benchmark]
                    def timeouts(s): return s=="robot_two"
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(cfg,benchmark,bench)
                elif cls=="Exp":
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f }
                    bench = benchsHyperAlloy[benchmark]
                    def timeouts(s): return s.endswith("ni_1") or s.endswith("gni_3")
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(cfg,benchmark,bench)
                elif cls=="Sym":
                    cfg = {**self.config, "tool": "QBF", "logfile" : f} #, "hypersmvSolverDocker" : True }
                    bench = benchsHyperAlloy[benchmark]
                    def timeouts(s): return False
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(cfg,benchmark,bench)
                else: raise Exception ("HighBenchmarkGUI class unexpected")
            except Exception as e:
                printLog(e,f)
                os.chdir(cwd)
                return errorRes
        
        return res

class AblationBenchmarkGUI(BenchmarkGUI):
    
    def __init__(self, stdscr, config):
            tabs = ["C-","M-","S-","F-","I-",""]
            cols = [ tab + config["mode"] for tab in tabs ]
            if config["group"] == "low": benchs = benchsAutoHyper.keys()
            elif config["group"] == "high": benchs = benchsHyperAlloy.keys()
            else: raise Exception ("AblationBenchmarkGUI group unexpected: " + config["group"])
            super().__init__(stdscr, benchs, cols ,config["nruns"])
            self.config = {**config }
            if not os.path.exists("logs"): os.makedirs("logs")
    
    def clsOpts(self,cls,cfg): 
        newCfg = dict(cfg)
        if   ("C-" in cls): newCfg["noComp"] = True
        elif ("M-" in cls): newCfg["noMult"] = True
        elif ("S-" in cls): newCfg["noSymm"] = True
        elif ("F-" in cls): newCfg["noSplitFormulas"] = True
        elif ("I-" in cls): newCfg["noSplitInits"] = True
        return newCfg
    
    def run_benchmark(self, benchmark, cls):
        logfile = "logs/"+benchmark+cls
        cwd = os.getcwd()
        with open(logfile,"w+") as f:
            if self.config["col"] and not (cls == self.config["col"]): return skippedRes
            if self.config["benchmark"] and not (benchmark == self.config["benchmark"]): return skippedRes
            try:
                if (self.config["group"] == "low" and "Exp" in cls):
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f, "path": pathAutoHyperToHyperAlloy }
                    bench = benchsAutoHyperToHyperAlloy[benchmark]
                    ablationCfg = self.clsOpts(cls,cfg)
                    def timeouts(s): return False
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(ablationCfg,benchmark,bench)
                elif (self.config["group"] == "low" and "Sym" in cls):
                    cfg = {**self.config, "tool": "QBF", "logfile" : f, "path": pathAutoHyperToHyperAlloy } 
                    bench = benchsAutoHyperToHyperAlloy[benchmark]
                    ablationCfg = self.clsOpts(cls,cfg)
                    def timeouts(s): return False
                    if timeouts(benchmark) and cfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(ablationCfg,benchmark,bench)
                elif (self.config["group"] == "high" and "Exp" in cls):
                    cfg = {**self.config, "tool": "AutoHyper", "logfile" : f, "path" : pathHyperAlloy }
                    bench = benchsHyperAlloy[benchmark]
                    ablationCfg = self.clsOpts(cls,cfg)
                    def timeouts(s): return \
                        s.endswith("ni_1") \
                        or (s=="easychair_sat_sat_gni_2" and (ablationCfg["noComp"] or ablationCfg["noMult"] or ablationCfg["noSplitInits"])) \
                        or (s=="easychair_sat_unsat_gni_2" and (ablationCfg["noComp"] or ablationCfg["noMult"] or ablationCfg["noSplitInits"] or ablationCfg["noSplitFormulas"])) \
                        or (s=="easychair_unsat_unsat_gni_2" and (ablationCfg["noComp"] or ablationCfg["noMult"] or ablationCfg["noSymm"] or ablationCfg["noSplitInits"] or ablationCfg["noSplitFormulas"])) \
                        or s.endswith("gni_3") \
                        or (s.startswith("robot_") and ablationCfg["noMult"]) \
                        or (s.startswith("robot_robust") and ablationCfg["noSplitFormulas"]) \
                        or (s.startswith("robot_enemies") and ablationCfg["noSplitFormulas"]) \
                        or (s.startswith("robot_two") and ablationCfg["noSplitFormulas"]) 
                    if timeouts(benchmark) and ablationCfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(ablationCfg,benchmark,bench)
                elif (self.config["group"] == "high" and "Sym" in cls):
                    cfg = {**self.config, "tool": "QBF", "logfile" : f, "path" : pathHyperAlloy }
                    bench = benchsHyperAlloy[benchmark]
                    ablationCfg = self.clsOpts(cls,cfg)
                    def timeouts(s): return \
                        (s.startswith("robot_two") and ablationCfg["noMult"]) 
                    if timeouts(benchmark) and ablationCfg["skipTimeout"]:
                        printLog("skipped benchmark that times out",f)
                        res = skippedRes
                    else: res = benchHyperAlloySolver(ablationCfg,benchmark,bench)
            except Exception as e:
                printLog(e,f)
                os.chdir(cwd)
                return errorRes
        
        return res

class CLI(object):
  """HyperAlloy Benchmarking"""
    
  def __init__(self,nruns=1,mode=None,group=None,benchmark=None,col=None):
        self._nruns = nruns
        self._mode = mode
        self._col = col
        self._group = group
        self._benchmark = benchmark

  def doLow(self):
    """Run low-level standard AutoHyper/HyperQube benchmarks"""
    nruns = self._nruns
    col = self._col
    benchmark = self._benchmark
    cfg = {**defaultBenchConfig, "debug" : True, "nruns": nruns, "col" : col, "witness": True, "benchmark" : benchmark } # "hypersmvSolverDocker" : True, "hypercheckerDocker" : True }
    
    def go(stdscr):
        curses.curs_set(0)
        gui = LowBenchmarkGUI(stdscr, cfg)
        gui.run_all()

    curses.wrapper(go)

  def doHigh(self):
    """Run high-level idiomatic HyperAlloy benchmarks"""
    nruns = self._nruns
    col = self._col
    benchmark = self._benchmark
    cfg = {**defaultBenchConfig, "debug" : True, "nruns": nruns, "col" : col, "witness": True, "benchmark" : benchmark } # "hypersmvSolverDocker" : True, "hypercheckerDocker" : True }
    
    def go(stdscr):
        curses.curs_set(0)
        gui = HighBenchmarkGUI(stdscr, cfg)
        gui.run_all()

    curses.wrapper(go)

  def doAblation(self):
    """Run ablation tests for low-level and high-level HyperAlloy benchmarks"""
    nruns = self._nruns
    col = self._col
    mode = self._mode
    group = self._group
    benchmark = self._benchmark
    cfg = {**defaultBenchConfig, "debug" : True, "nruns": nruns, "col" : col, "witness": True, "mode" : mode, "group" : group, "benchmark" : benchmark} # "hypersmvSolverDocker" : True, "skipTimeout" : False }
    
    def go(stdscr):
        curses.curs_set(0)
        gui = AblationBenchmarkGUI(stdscr, cfg)
        gui.run_all()

    curses.wrapper(go)

if __name__ == '__main__':
  fire.Fire(CLI)
  