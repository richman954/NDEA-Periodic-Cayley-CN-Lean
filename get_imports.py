import os
import re

def get_lean_files(directory):
    lean_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    return lean_files

def get_dependencies(lean_files):
    dependencies = {}
    import_pattern = re.compile(r'^import\s+([A-Za-z0-9_.]+)')
    for file in lean_files:
        with open(file, 'r', encoding='utf-8') as f:
            deps = []
            for line in f:
                match = import_pattern.match(line.strip())
                if match:
                    deps.append(match.group(1))
            dependencies[file] = deps
    return dependencies

if __name__ == "__main__":
    files = get_lean_files('NDEAMathlibGate')
    deps = get_dependencies(files)
    for k, v in deps.items():
        print(f"{k}: {v}")
