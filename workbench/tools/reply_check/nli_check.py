"""Score each glossed claim against the natural reply with an NLI cross-encoder. Runs on the mini. No LLM call.

  ~/negbert-venv/bin/python nli_check.py claims.json reply.txt out.json [model]

Premises tried for each claim: every reply sentence, every window of 2 and 3 consecutive sentences, and the whole
reply (cut from the end if the pair passes 512 tokens). For each claim it keeps the premise with the highest
entailment probability and the one with the highest contradiction probability.
"""
import json, re, sys
import torch
from transformers import AutoModelForSequenceClassification, AutoTokenizer

claims_path, reply_path, out_path = sys.argv[1:4]
model_name = sys.argv[4] if len(sys.argv) > 4 else "MoritzLaurer/DeBERTa-v3-large-mnli-fever-anli-ling-wanli"
claims = json.load(open(claims_path))["claims"]
reply = open(reply_path).read().strip()
sents = [s.strip() for p in reply.split("\n") for s in re.split(r"(?<=[.?!])\s+(?=[A-Z\"“])", p) if s.strip()]
premises = [("sentence", i, i, s) for i, s in enumerate(sents)]
for w in (2, 3):
    premises += [(f"window{w}", i, i + w - 1, " ".join(sents[i:i + w])) for i in range(len(sents) - w + 1)]
premises.append(("whole", 0, len(sents) - 1, reply))

device = "mps" if torch.backends.mps.is_available() else "cpu"
tok = AutoTokenizer.from_pretrained(model_name, local_files_only=True)
model = AutoModelForSequenceClassification.from_pretrained(model_name, local_files_only=True).to(device).eval()
labels = {v.lower(): int(k) for k, v in model.config.id2label.items()}
E, C = labels["entailment"], labels["contradiction"]

results = []
with torch.no_grad():
    for c in claims:
        probs = []
        for b in range(0, len(premises), 16):
            batch = premises[b:b + 16]
            enc = tok([p[3] for p in batch], [c["text"]] * len(batch), truncation="only_first", max_length=512,
                      padding=True, return_tensors="pt").to(device)
            probs += torch.softmax(model(**enc).logits.float(), -1).cpu().tolist()
        best_e = max(range(len(premises)), key=lambda i: probs[i][E])
        best_c = max(range(len(premises)), key=lambda i: probs[i][C])
        whole = probs[-1]
        results.append({**c,
                        "entail": round(probs[best_e][E], 4), "entail_premise": premises[best_e][3], "entail_kind": premises[best_e][0],
                        "contradict": round(probs[best_c][C], 4), "contradict_premise": premises[best_c][3], "contradict_kind": premises[best_c][0],
                        "whole_reply": {"entail": round(whole[E], 4), "contradict": round(whole[C], 4)}})
json.dump({"model": model_name, "device": device, "sentences": sents, "results": results}, open(out_path, "w"), indent=1, ensure_ascii=False)
print("done", len(results), "claims,", len(premises), "premises each")
