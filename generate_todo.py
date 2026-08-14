#!/usr/bin/env python3
import os
import re

# Regexes for Coq
coq_patterns = [
    re.compile(r'^\s*(?:Lemma|Theorem|Record|Definition|Instance|Fact|Remark|Property)\s+(\w+)', re.IGNORECASE)
]

# Regexes for Lean
lean_patterns = [
    re.compile(r'^\s*(?:theorem|def|class|structure|inductive|instance)\s+(\w+)', re.IGNORECASE)
]

# Regex for skipped/ignored theorems via comment: -- @skip name
skip_pattern = re.compile(r'--\s*@skip\s+(\w+)', re.IGNORECASE)

def scan_coq_file(path):
    theorems = set()
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            for pat in coq_patterns:
                m = pat.match(line)
                if m:
                    theorems.add(m.group(1))
    return theorems

def scan_lean_file(path):
    theorems = set()
    skipped = set()
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            for pat in lean_patterns:
                m = pat.match(line)
                if m:
                    theorems.add(m.group(1))
            m_skip = skip_pattern.search(line)
            if m_skip:
                skipped.add(m_skip.group(1))
    return theorems, skipped

def main():
    coq_targets = [
        "basic.v", "Choice.v", "Sublogic.v", "ZFdef.v", "ZF.v",
        "VarMap.v", "MyList.v", "IntMap.v", "EnsEm.v", "Ens.v",
        "Zpairs.v", "Zsum.v", "Zstable.v", "Znats.v", "Lambda.v", "Can.v"
    ]

    coq_theorems = {}
    for f in coq_targets:
        if os.path.isfile(f):
            coq_theorems[f] = scan_coq_file(f)

    lean_dir = "CicModel"
    lean_theorems = {}
    all_skipped = set()
    if os.path.isdir(lean_dir):
        for root, _, files in os.walk(lean_dir):
            for file in files:
                if file.endswith(".lean"):
                    path = os.path.join(root, file)
                    theorems, skipped = scan_lean_file(path)
                    lean_theorems[path] = theorems
                    all_skipped.update(skipped)

    if os.path.isfile("CicModel.lean"):
        theorems, skipped = scan_lean_file("CicModel.lean")
        lean_theorems["CicModel.lean"] = theorems
        all_skipped.update(skipped)

    # Compile flat set of Lean declarations
    flat_lean = set(t.lower() for thms in lean_theorems.values() for t in thms)

    # Gather unported theorems per file
    unported_by_file = {}
    total_unported = 0
    total_coq = 0

    for f, thms in sorted(coq_theorems.items()):
        f_unported = []
        for t in sorted(thms):
            total_coq += 1
            if t.lower() not in flat_lean and t not in all_skipped:
                f_unported.append(t)
        unported_by_file[f] = f_unported
        total_unported += len(f_unported)

    # Write TODO.md
    with open("TODO.md", "w", encoding="utf-8") as out:
        out.write("# Porting To-Do List (Theorems Delta)\n\n")
        out.write(f"This document tracks the unported theorems and definitions from the core files of the Coq library. Out of {total_coq} total core Coq declarations, **{total_unported} remain unported** (the delta).\n\n")
        out.write("### Quick Stats\n")
        out.write(f"- **Total Core Coq Theorems/Defs**: {total_coq}\n")
        out.write(f"- **Ported to Lean 4**: {total_coq - total_unported - len(all_skipped)}\n")
        out.write(f"- **Skipped / Handled Natively via Mathlib**: {len(all_skipped)}\n")
        out.write(f"- **Remaining Unported Delta**: {total_unported} ({(total_unported/total_coq)*100:.2f}%)\n\n")

        out.write("## Unported Declarations by File\n\n")
        for f, thms in sorted(unported_by_file.items()):
            if thms:
                out.write(f"### ✗ {f} ({len(thms)} unported)\n")
                for t in thms:
                    out.write(f"- [ ] `{t}`\n")
                out.write("\n")
            else:
                out.write(f"### ✓ {f} (Fully Ported / Skipped)\n\n")

    print("TODO.md generated successfully!")

if __name__ == "__main__":
    main()
