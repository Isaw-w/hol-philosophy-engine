"""Score given (premise, hypothesis) pairs with an NLI cross-encoder. Runs on the mini. No LLM call.

  ~/negbert-venv/bin/python nli_pairs.py pairs.json out.json [model]

pairs.json is a list of objects with "premise" and "hypothesis"; every other field is copied to the output.
Pairs longer than 1024 tokens are cut from the end of the premise, and the output says so.
"""
import json, sys
import torch
from transformers import AutoModelForSequenceClassification, AutoTokenizer

pairs_path, out_path = sys.argv[1:3]
model_name = sys.argv[3] if len(sys.argv) > 3 else "MoritzLaurer/DeBERTa-v3-large-mnli-fever-anli-ling-wanli"
pairs = json.load(open(pairs_path))
device = "mps" if torch.backends.mps.is_available() else "cpu"
tok = AutoTokenizer.from_pretrained(model_name, local_files_only=True)
model = AutoModelForSequenceClassification.from_pretrained(model_name, local_files_only=True).to(device).eval()
labels = {v.lower(): int(k) for k, v in model.config.id2label.items()}
E, N, C = labels["entailment"], labels["neutral"], labels["contradiction"]
out = []
with torch.no_grad():
    for b in range(0, len(pairs), 8):
        batch = pairs[b:b + 8]
        full = [len(tok(p["premise"], p["hypothesis"])["input_ids"]) for p in batch]
        enc = tok([p["premise"] for p in batch], [p["hypothesis"] for p in batch], truncation="only_first",
                  max_length=1024, padding=True, return_tensors="pt").to(device)
        probs = torch.softmax(model(**enc).logits.float(), -1).cpu().tolist()
        for p, pr, n in zip(batch, probs, full):
            out.append({**p, "entail": round(pr[E], 4), "neutral": round(pr[N], 4), "contradict": round(pr[C], 4),
                        "tokens": n, "cut": n > 1024})
json.dump({"model": model_name, "device": device, "results": out}, open(out_path, "w"), indent=1, ensure_ascii=False)
print("done", len(out), "pairs; longest", max(r["tokens"] for r in out), "tokens")
