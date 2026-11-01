"""One model call on OpenRouter, reasoning effort high. Runs on the mini.
  OPENROUTER_API_KEY=... python3 loop_call.py messages.json response.json
The model is Opus 5.5 from the Anthropic provider, unless a model.json next to this file names another model and its
provider, e.g. {"model": "z-ai/glm-5.3-flash", "provider": ["z-ai/fp8"]}, and optionally "max_tokens"
(default 64000; up to the provider's maximum).
"""
import json, os, sys, urllib.request

msgs = json.load(open(sys.argv[1]))
cfg = {"model": "anthropic/claude-opus-5.5", "provider": ["anthropic"]}
here = os.path.join(os.path.dirname(os.path.abspath(__file__)), "model.json")
if os.path.exists(here):
    cfg.update(json.load(open(here)))
body = {"model": cfg["model"], "messages": msgs, "reasoning": {"effort": "high"}, "max_tokens": cfg.get("max_tokens", 64000),
        "usage": {"include": True}, "provider": {"order": cfg["provider"], "allow_fallbacks": False}}
for attempt in range(2):
    try:
        req = urllib.request.Request("https://openrouter.ai/api/v1/chat/completions", data=json.dumps(body).encode(),
              headers={"Authorization": "Bearer " + os.environ["OPENROUTER_API_KEY"], "Content-Type": "application/json"})
        r = json.loads(urllib.request.urlopen(req, timeout=5400).read()); m = r["choices"][0]["message"]
        raw_path = os.path.splitext(sys.argv[2])[0] + ".raw.json"
        with open(raw_path, "w") as raw_file:
            json.dump(r, raw_file, ensure_ascii=False, indent=1)
        json.dump({"provider": r.get("provider"), "reasoning": m.get("reasoning") or "", "content": m.get("content") or "",
                   "finish": r["choices"][0].get("finish_reason"), "usage": r.get("usage"),
                   "native_finish": r["choices"][0].get("native_finish_reason"),
                   "id": r.get("id"), "model": r.get("model")}, open(sys.argv[2], "w"), ensure_ascii=False, indent=1)
        finish = r["choices"][0].get("finish_reason")
        status = "content_filter" if finish == "content_filter" else "no_response" if not (m.get("content") or "").strip() else "response_received"
        cost = (r.get("usage") or {}).get("cost")
        print(status, r.get("provider"), f"${cost:.4f}" if cost is not None else "cost unavailable"); break
    except Exception as e:
        print(f"error (attempt {attempt + 1}): {type(e).__name__}")
