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
    # Only scan the core files mapped in our porting status
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

    # Compile a flat set of Lean declarations (case-insensitive for robust mapping)
    flat_lean = {}
    for path, thms in lean_theorems.items():
        for t in thms:
            flat_lean[t.lower()] = (t, path)

    # Map Coq theorems
    total_coq_count = sum(len(v) for v in coq_theorems.values())
    total_lean_count = sum(len(v) for v in lean_theorems.values())

    ported_count = 0
    skipped_count = 0
    delta_count = 0

    print("=" * 70)
    print("               THEOREMS PORTING STATUS REPORT")
    print("=" * 70)
    print(f"Total Coq theorems found in core: {total_coq_count}")
    print(f"Total Lean theorems found:        {total_lean_count}")
    print(f"Skipped / Ignored (Mathlib):      {len(all_skipped)}")
    print("-" * 70)

    for f, thms in sorted(coq_theorems.items()):
        print(f"\nCoq File: {f} ({len(thms)} theorems/definitions)")
        f_ported = []
        f_skipped = []
        f_unported = []
        for t in sorted(thms):
            if t.lower() in flat_lean:
                f_ported.append((t, flat_lean[t.lower()][0], flat_lean[t.lower()][1]))
            elif t in all_skipped:
                f_skipped.append(t)
            else:
                f_unported.append(t)

        ported_count += len(f_ported)
        skipped_count += len(f_skipped)
        delta_count += len(f_unported)

        print(f"  Ported: {len(f_ported)} | Skipped: {len(f_skipped)} | Unported: {len(f_unported)}")

        if f_ported:
            print("  [✓ Ported]")
            for coq_t, lean_t, path in f_ported[:10]: # Print first 10 for brevity
                print(f"    - {coq_t}  ==>  {lean_t} ({os.path.basename(path)})")
            if len(f_ported) > 10:
                print(f"    ... and {len(f_ported) - 10} more")

        if f_skipped:
            print("  [⊖ Skipped via Mathlib]")
            for t in f_skipped:
                print(f"    - {t}")

        if f_unported:
            print("  [✗ Unported Delta]")
            for t in f_unported[:10]:
                print(f"    - {t}")
            if len(f_unported) > 10:
                print(f"    ... and {len(f_unported) - 10} more")

    print("\n" + "=" * 70)
    print(f"OVERALL RESULTS:")
    print(f"  Ported:   {ported_count} ({ (ported_count/total_coq_count)*100 if total_coq_count else 0:.2f}%)")
    print(f"  Skipped:  {skipped_count}")
    print(f"  Unported: {delta_count}")
    print("=" * 70)

if __name__ == "__main__":
    main()
