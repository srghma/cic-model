#!/usr/bin/env python3
import os

def find_files(directory, extension):
    file_list = []
    # Only scan root directory and relevant subdirectories, completely bypassing package folders
    for root, dirs, files in os.walk(directory):
        # Modify dirs in-place to prevent os.walk from scanning deep dependencies
        dirs[:] = [d for d in dirs if d not in ['.lake', '.git', 'broken', 'fotheory', 'constructions', 'finite', 'sketches', 'tests', 'lib', 'template', 'CicModel']]
        for file in files:
            if file.endswith(extension):
                rel_path = os.path.relpath(os.path.join(root, file), directory)
                file_list.append(rel_path)
    return file_list

def find_lean_files():
    file_list = []
    if os.path.isdir("CicModel"):
        for root, dirs, files in os.walk("CicModel"):
            for file in files:
                if file.endswith(".lean"):
                    file_list.append(os.path.join(root, file))
    if os.path.isfile("CicModel.lean"):
        file_list.append("CicModel.lean")
    return file_list

def main():
    # Only scan root level for our Coq files to make it instant!
    coq_files = [f for f in os.listdir(".") if f.endswith(".v")]
    lean_files = find_lean_files()

    # Cleaned Coq module names
    coq_modules = {}
    for f in coq_files:
        base = os.path.basename(f)
        module_name = os.path.splitext(base)[0]
        coq_modules[module_name.lower()] = f

    # Cleaned Lean module names
    lean_modules = {}
    for f in lean_files:
        base = os.path.basename(f)
        module_name = os.path.splitext(base)[0]
        lean_modules[module_name.lower()] = f

    # Special mappings (e.g. ZFdef.v / ZF.v both mapped to ZF.lean)
    coq_to_lean_map = {
        "zfdef": "zf",
        "ensem": "ens"
    }

    ported = []
    unported = []

    for coq_mod, coq_path in sorted(coq_modules.items()):
        target_lean = coq_to_lean_map.get(coq_mod, coq_mod)
        if target_lean in lean_modules:
            ported.append((coq_path, lean_modules[target_lean]))
        else:
            unported.append(coq_path)

    print("=" * 60)
    print("                PORTING STATUS REPORT")
    print("=" * 60)
    print(f"Total Coq files found: {len(coq_files)}")
    print(f"Total Lean files found: {len(lean_files)}")
    print(f"Ported files count: {len(ported)}")
    print(f"Unported files count (Delta): {len(unported)}")

    if len(coq_files) > 0:
        completion_pct = (len(ported) / len(coq_modules)) * 100
        print(f"Completion: {completion_pct:.2f}%")
    print("-" * 60)

    print("\n[PORTED FILES]")
    for coq, lean in sorted(ported):
        print(f"  ✓ {coq}  ==>  {lean}")

    print("\n[UNPORTED FILES (DELTA)]")
    for coq in sorted(unported):
        print(f"  ✗ {coq}")
    print("=" * 60)

if __name__ == "__main__":
    main()
