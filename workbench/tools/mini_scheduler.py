"""Many round-1 jobs on the mini itself, with no ssh: model calls, HOL4 checks, fix rounds and Z3 checks.

One process. Each job (one case with one model) runs call -> HOL4 -> (fix call -> HOL4)* -> Z3 in its own thread,
and each resource has its own number of slots: model calls per model, HOL4 checks, Z3 checks, so hundreds of jobs
wait on the network at once while the mini's cores are never oversubscribed. The run folders are laid out exactly as
run_native.py and fix_round.py lay them out (the same messages, the same request body as loop_call.py, the same fix
feedback), so every later tool reads them unchanged. A finished job is skipped and a started one goes on from its
last run, so the scheduler can be stopped and started again. Run only after the user has approved the exact inputs.

  OPENROUTER_API_KEY=... python3 tools/mini_scheduler.py JOBS.json        (started by tools/mini_launch.py)

JOBS.json: {"out_dir": "runs/DATE/NAME", "inputs": "data/...json", "prompt": "prompts/...txt",
            "models": [{"tag": "glm53", "model": "z-ai/glm-5.3", "provider": ["z-ai/fp8"]}, ...],
            "cases": [keys] (default: every case in inputs), "max_fix": 3,
            "call_slots": 32 (per model), "hol_slots": 6, "z3_slots": 3, "z3_budget": 600}
"""
import hashlib, json, os, re, shutil, subprocess, sys, threading, time, traceback, urllib.error, urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
HOL = TOOLS.parent
sys.path.insert(0, str(TOOLS))
from native_check import check, source_of                  # noqa: E402
from fix_round import hol4_error                            # noqa: E402

lock = threading.Lock()


def digest(b):
    return hashlib.sha256(b).hexdigest()


def write_json(path, obj, indent=2):
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=indent))


class Scheduler:
    def __init__(self, jobs_file):
        self.cfg = cfg = json.loads(Path(jobs_file).read_text())
        self.out = HOL / cfg["out_dir"]
        self.out.mkdir(parents=True, exist_ok=True)
        self.prompt_path = HOL / cfg["prompt"]
        self.prompt_bytes = self.prompt_path.read_bytes()
        m = re.search(r"_(v\d+)", self.prompt_path.resolve().name)
        self.ver = m.group(1) if m else "vX"
        self.cases = {c["key"]: c for c in json.loads((HOL / cfg["inputs"]).read_text())}
        self.keys = cfg.get("cases") or list(self.cases)
        self.models = cfg["models"]
        self.max_fix = cfg.get("max_fix", 3)
        self.call_slots = {m["tag"]: threading.Semaphore(cfg.get("call_slots", 32)) for m in self.models}
        self.hol_slots = threading.Semaphore(cfg.get("hol_slots", 6))
        self.z3_slots = threading.Semaphore(cfg.get("z3_slots", 3))
        self.z3_budget = cfg.get("z3_budget", 600)
        self.key = os.environ["OPENROUTER_API_KEY"]
        self.loop_call = (TOOLS / "loop_call.py").read_bytes()
        self.progress = {"jobs": 0, "finished": 0, "skipped": 0, "calling": 0, "hol4": 0, "z3": 0, "failed": 0,
                         "cost": 0.0, "started": time.strftime("%Y-%m-%d %H:%M:%S")}

    # ---- bookkeeping
    def bump(self, **delta):
        with lock:
            for k, v in delta.items():
                self.progress[k] += v
            self.progress["updated"] = time.strftime("%Y-%m-%d %H:%M:%S")
            write_json(self.out / "progress.json", self.progress)

    def done_cases(self, tag):
        f = self.out / f"summary_{tag}.jsonl"
        return {json.loads(l)["case"] for l in f.read_text().splitlines() if l.strip()} if f.exists() else set()

    # ---- one model call: the request loop_call.py sends, with backoff when the provider is busy
    def call(self, run, model):
        msgs = json.loads((run / "r1_messages.json").read_text())
        body = {"model": model["model"], "messages": msgs, "reasoning": {"effort": "high"},
                "max_tokens": model.get("max_tokens", 64000),   # a job may raise it to the provider's maximum
                "usage": {"include": True}, "provider": {"order": model["provider"], "allow_fallbacks": False}}
        log, r = [], None
        with self.call_slots[model["tag"]]:
            self.bump(calling=1)
            try:
                for attempt in range(6):
                    try:
                        req = urllib.request.Request("https://openrouter.ai/api/v1/chat/completions",
                                                     data=json.dumps(body).encode(),
                                                     headers={"Authorization": "Bearer " + self.key,
                                                              "Content-Type": "application/json"})
                        r = json.loads(urllib.request.urlopen(req, timeout=5400).read())
                        r["choices"][0]["message"]
                        break
                    except Exception as e:
                        code = getattr(e, "code", None)
                        log.append(f"error (attempt {attempt + 1}): {type(e).__name__}" + (f" {code}" if code else ""))
                        r = None
                        busy = code in (429, 500, 502, 503, 504)
                        if attempt >= (5 if busy else 1):        # loop_call.py's two attempts, more when busy
                            break
                        time.sleep(min(300, 20 * 2 ** attempt) if busy else 5)
            finally:
                self.bump(calling=-1)
        if r is None:
            (run / "call.log").write_text("\n".join(log) + "\n")
            return None
        return self.record(run, r, log)

    def record(self, run, r, log):
        """write the answer as loop_call.py and run_native.py write it"""
        m = r["choices"][0]["message"]
        write_json(run / "r1_response.raw.json", r, indent=1)
        finish = r["choices"][0].get("finish_reason")
        write_json(run / "r1_response.json", {"provider": r.get("provider"), "reasoning": m.get("reasoning") or "",
                                              "content": m.get("content") or "", "finish": finish,
                                              "usage": r.get("usage"),
                                              "native_finish": r["choices"][0].get("native_finish_reason"),
                                              "id": r.get("id"), "model": r.get("model")}, indent=1)
        content = m.get("content") or ""
        status = ("generation_filtered" if finish == "content_filter"
                  else "response_received" if content.strip() else "no_response")
        cost = (r.get("usage") or {}).get("cost")
        log.append(f"{'content_filter' if finish == 'content_filter' else status} {r.get('provider')} "
                   + (f"${cost:.4f}" if cost is not None else "cost unavailable"))
        (run / "call.log").write_text("\n".join(log) + "\n")
        (run / "response.txt").write_text(content)
        write_json(run / "generation_result.json", {"status": status, "finish": finish,
                                                    "content_characters": len(content), "usage": r.get("usage")})
        mf = run / "run_manifest.json"
        man = json.loads(mf.read_text())
        if "fix_of" in man:
            man["state"] = status
            write_json(mf, man)
        if cost:
            self.bump(cost=cost)
        return status

    # ---- a call the old runner (run_native.py or fix_round.py over ssh) made: its answer lands on this machine in
    # ~/thick_training/cloud_gen/<run name>/. Wait for it while that call is still running, then take it over.
    def calls_running(self):
        """the folders where a loop_call.py is running now"""
        ps = subprocess.run(["pgrep", "-f", "loop_call.py r1_messages.json"], capture_output=True, text=True).stdout.split()
        dirs = set()
        for pid in ps:
            out = subprocess.run(["lsof", "-a", "-p", pid, "-d", "cwd", "-Fn"], capture_output=True, text=True).stdout
            dirs |= {l[1:] for l in out.splitlines() if l.startswith("n")}
        return dirs

    def adopt(self, run):
        remote = Path.home() / "thick_training/cloud_gen" / run.name
        if not (remote / "r1_messages.json").exists():
            return None
        while not (remote / "r1_response.json").exists():
            if str(remote.resolve()) not in self.calls_running():
                time.sleep(5)                                    # the answer may be in the middle of being written
                if not (remote / "r1_response.json").exists():
                    return None                                  # no call there any more: call again
            time.sleep(30)
        raw = remote / "r1_response.raw.json"
        if not raw.exists():
            return None
        r = json.loads(raw.read_text())
        status = self.record(run, r, ["taken over by mini_scheduler.py from " + str(remote)])
        return status

    # ---- HOL4, on this machine
    def hol4(self, run, timeout):
        with self.hol_slots:
            self.bump(hol4=1)
            try:
                res = check(run / "r1_response.json", run / "native_check", "hol4", "local", timeout=timeout)
            except ValueError as exc:                          # the code block could not be taken out
                return {"status": "extraction_failed", "error": str(exc)}
            finally:
                self.bump(hol4=-1)
        for name in ("controlled_english.txt", "source_declarations_english.txt"):
            link = run / ("mechanical_english.txt" if name == "controlled_english.txt" else name)
            if (run / "native_check" / name).exists() and not link.exists():
                link.symlink_to("native_check/" + name)
        return res

    # ---- the first run and each fix run, laid out as run_native.py and fix_round.py lay them out
    def first_run(self, key, model):
        case = self.cases[key]
        run = self.out / f"{key.replace('/', '_')}_round1_{self.ver}_{model['tag']}_{time.strftime('%Y%m%d_%H%M%S')}"
        run.mkdir(parents=True)
        template = self.prompt_bytes.decode().strip()
        write_json(run / "case_input.json", {k: case[k] for k in ("key", "system", "user")})
        messages = [{"role": "system", "content": (case["system"].strip() + "\n\n" + template).strip()},
                    {"role": "user", "content": case["user"]}]
        write_json(run / "r1_messages.json", messages, indent=1)
        (run / "prompt.txt").write_bytes(self.prompt_bytes)
        (run / "loop_call.py").write_bytes(self.loop_call)
        (run / "mini_scheduler.py").write_bytes(Path(__file__).read_bytes())
        write_json(run / "model.json", {k: model[k] for k in ("model", "provider", "max_tokens") if k in model})
        write_json(run / "run_manifest.json", {
            "case": key, "prompt_file": str(self.prompt_path), "prompt_sha256": digest(self.prompt_bytes),
            "call_script_sha256": digest(self.loop_call), "user_file": None,
            "user_sha256": digest(case["user"].encode()), "original_user_sha256": digest(case["user"].encode()),
            "input_condition": "Original case query",
            "route": f"OpenRouter; {model['model']} from {','.join(model['provider'])}; mini_scheduler.py on the mini "
                     "(the request loop_call.py sends)",
            "checker": "native", "prover": "hol4", "revisions": 0})
        return run

    def fix_run(self, src, n, model, error):
        feedback = error + "\n\nRevise it."
        raw = json.loads((src / "r1_response.raw.json").read_text())
        messages = json.loads((src / "r1_messages.json").read_text()) + [
            raw["choices"][0]["message"], {"role": "user", "content": feedback}]
        key = json.loads((src / "case_input.json").read_text())["key"]
        run = self.out / f"{key.replace('/', '_')}_round1_fix{n}_{self.ver}_{model['tag']}_{time.strftime('%Y%m%d_%H%M%S')}"
        run.mkdir(parents=True)
        mb = json.dumps(messages, ensure_ascii=False, indent=1).encode()
        (run / "r1_messages.json").write_bytes(mb)
        (run / "feedback.txt").write_text(feedback)
        (run / "loop_call.py").write_bytes(self.loop_call)
        if (src / "model.json").exists():               # the same model continues its own conversation
            shutil.copy(src / "model.json", run / "model.json")
        (run / "mini_scheduler.py").write_bytes(Path(__file__).read_bytes())
        shutil.copy(src / "case_input.json", run / "case_input.json")
        sm = json.loads((src / "run_manifest.json").read_text())
        write_json(run / "run_manifest.json", {
            "state": "prepared", "round": 1, "fix_of": str(src), "case": key, "user_sha256": sm.get("user_sha256"),
            "messages_sha256": digest(mb), "feedback": feedback,
            "route": model["model"] + ", high reasoning, mini_scheduler.py on the mini",
            "input_condition": "Round-1 conversation, the failed assistant message with reasoning_details, then "
                               "HOL4's error lines (or the extractor's message) unchanged and 'Revise it.'"})
        return run

    @staticmethod
    def status_of(run):
        g = run / "generation_result.json"
        n = run / "native_check/native_result.json"
        gen = json.loads(g.read_text()) if g.exists() else {}
        return gen.get("status"), (json.loads(n.read_text()).get("status") if n.exists() else None), \
            (gen.get("usage") or {}).get("cost")

    def error_for_fix(self, run, res):
        """the feedback fix_round.py would send, or None when it would send none"""
        if res.get("status") == "extraction_failed":
            return res["error"]
        if res.get("status") == "unproven_theorems":
            return "Theorems without a proof: " + ", ".join(res.get("unproven_theorems", []))
        if res.get("status") == "execution_failed":
            return hol4_error((run / "native_check/native.log").read_text())
        return None

    # ---- one job
    def job(self, key, model):
        tag = model["tag"]
        if key in self.done_cases(tag):
            self.bump(skipped=1)
            return
        slug = key.replace("/", "_")
        chain = sorted((r for r in self.out.glob(f"{slug}_round1_*{self.ver}_{tag}_*") if r.is_dir()),
                       key=lambda r: r.name[-15:])
        try:
            if not chain:
                chain = [self.first_run(key, model)]
            res = None
            while True:
                run = chain[-1]
                gen, native, _ = self.status_of(run)
                if gen is None:
                    gen = self.adopt(run) or self.call(run, model)
                    if gen is None:
                        break                                   # the call failed every attempt
                if gen != "response_received":
                    break
                if native is None and not (run / "native_check").exists():
                    res = self.hol4(run, 300 if len(chain) == 1 else 1200)
                    native = res.get("status")
                elif native is None:                            # an extraction failure from an earlier start
                    try:
                        source_of((run / "response.txt").read_text()); res = {"status": "unknown"}
                    except ValueError as exc:
                        res = {"status": "extraction_failed", "error": str(exc)}
                    native = res["status"]
                else:
                    res = json.loads((run / "native_check/native_result.json").read_text())
                if native == "processed" or len(chain) - 1 >= self.max_fix:
                    break
                error = self.error_for_fix(run, res)
                if not error:
                    break
                chain.append(self.fix_run(run, len(chain), model, error))
            gen, native, _ = self.status_of(chain[-1])
            z3 = None
            if native == "processed" and (chain[-1] / "native_check/kernel_ast.json").exists():
                with self.z3_slots:
                    self.bump(z3=1)
                    try:
                        subprocess.run([sys.executable, str(TOOLS / "reply_check/z3_engine.py"), str(chain[-1]),
                                        "--local", "--host", "local", "--budget-s", str(self.z3_budget)],
                                       cwd=HOL, capture_output=True, text=True, timeout=self.z3_budget + 300)   # a hard wall-clock limit
                    except subprocess.TimeoutExpired:
                        pass
                    finally:
                        self.bump(z3=-1)
                zf = chain[-1] / "z3_engine/z3_engine.json"
                z3 = str(zf.relative_to(HOL)) if zf.exists() else None
            rec = {"case": key, "model": tag, "runs": [str(r.relative_to(HOL)) for r in chain],
                   "generation": gen or "call_failed", "native": native, "fix_rounds": len(chain) - 1,
                   "cost": round(sum(c for c in (self.status_of(r)[2] for r in chain) if c), 4), "z3": z3}
            with lock:
                with open(self.out / f"summary_{tag}.jsonl", "a") as f:
                    f.write(json.dumps(rec) + "\n")
            self.bump(finished=1)
        except Exception:
            self.bump(failed=1)
            with lock:
                with open(self.out / "errors.log", "a") as f:
                    f.write(f"{key} {tag}\n{traceback.format_exc()}\n")

    def run(self):
        jobs = [(k, m) for k in self.keys for m in self.models]
        self.bump(jobs=len(jobs))
        with ThreadPoolExecutor(max_workers=min(len(jobs), 1000)) as ex:
            for k, m in jobs:
                ex.submit(self.job, k, m)
        with lock:
            self.progress["done_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
            write_json(self.out / "progress.json", self.progress)


if __name__ == "__main__":
    Scheduler(sys.argv[1]).run()
