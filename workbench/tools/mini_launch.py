"""Start, watch and collect a mini_scheduler.py run on the mini, from here.

  python3 tools/mini_launch.py start JOBS.json     # copies tools, inputs and prompt to the mini, starts the scheduler
  python3 tools/mini_launch.py status runs/DATE/NAME
  python3 tools/mini_launch.py pull runs/DATE/NAME  # copies the run folders back here

The OpenRouter key goes over once, through the same pipe as before (never printed or stored); the scheduler keeps it
in its environment only. Everything runs on the mini: model calls, HOL4 and Z3. Start only after the user has
approved the exact inputs.
"""
import json, shlex, subprocess, sys
from pathlib import Path

HOL = Path(__file__).resolve().parent.parent
HOST = "mini"
REMOTE = "thick_training/hol_runner"                 # under the mini's home
PY = "~/thick_training/venv_logreco/bin/python3"


def ssh(cmd, **kw):
    return subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ServerAliveInterval=30", HOST, cmd], **kw)


def start(jobs_file):
    jobs_path = Path(jobs_file).resolve()
    cfg = json.loads(jobs_path.read_text())
    out = cfg["out_dir"]
    (HOL / out).mkdir(parents=True, exist_ok=True)
    local_jobs = HOL / out / "jobs.json"
    if jobs_path != local_jobs.resolve():
        local_jobs.write_text(jobs_path.read_text())
    # the code, the inputs, the prompt and any run folders already here (so a run started elsewhere resumes)
    paths = ["tools", cfg["inputs"], cfg["prompt"], out]
    tar = subprocess.Popen(["tar", "czf", "-", "--exclude", "__pycache__", "--exclude", "backups", *paths],
                           cwd=HOL, stdout=subprocess.PIPE)
    ssh(f"mkdir -p {REMOTE} && tar xzf - -C {REMOTE}", stdin=tar.stdout, check=True)
    tar.stdout.close(); tar.wait()
    key = subprocess.Popen(["zsh", "-ic", 'printf "%s\\n" "$OPENROUTER_API_KEY"'], stdout=subprocess.PIPE,
                           stderr=subprocess.DEVNULL)
    cmd = (f"read -r K; cd {REMOTE} && OPENROUTER_API_KEY=\"$K\" nohup {PY} tools/mini_scheduler.py "
           f"{shlex.quote(out + '/jobs.json')} > {shlex.quote(out + '/scheduler.log')} 2>&1 < /dev/null & echo started")
    r = ssh(cmd, stdin=key.stdout, capture_output=True, text=True)
    key.stdout.close(); key.wait()
    print(r.stdout.strip() or r.stderr.strip())


def status(out):
    r = ssh(f"cat {REMOTE}/{shlex.quote(out)}/progress.json; echo; "
            f"tail -3 {REMOTE}/{shlex.quote(out)}/errors.log 2>/dev/null", capture_output=True, text=True)
    print(r.stdout.strip())


def pull(out):
    (HOL / out).mkdir(parents=True, exist_ok=True)
    tar = subprocess.Popen(["ssh", "-o", "BatchMode=yes", HOST, f"tar czf - -C {REMOTE} {shlex.quote(out)}"],
                           stdout=subprocess.PIPE)
    subprocess.run(["tar", "xzf", "-", "-C", str(HOL)], stdin=tar.stdout, check=True)
    tar.stdout.close(); tar.wait()
    print("pulled", out)


if __name__ == "__main__":
    {"start": start, "status": status, "pull": pull}[sys.argv[1]](sys.argv[2])
