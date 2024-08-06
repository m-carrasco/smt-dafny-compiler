import lit.formats
import shutil
import os
import subprocess

def _clean_test_directory(directory):
    for entry in os.scandir(directory):
        basename = os.path.basename(entry.path)
        if basename == "lit.cfg.py":
            continue
        if entry.is_dir():
            shutil.rmtree(entry.path)
        else:
            os.remove(entry.path)

config.name = "Test suite"
config.test_format = lit.formats.ShTest(True)

config.suffixes = ['.smt2', '.test', '.dfy']

config.my_src_root = os.path.join(os.path.dirname(__file__), "..")

config.compiler_cli_bin = os.path.join(config.my_src_root, "src","SDC","bin","Debug","net8.0","linux-x64","publish","SDC")
assert os.path.exists(config.compiler_cli_bin)

config.test_source_root = os.path.dirname(__file__)
config.test_exec_root = os.path.join(config.test_source_root, "output")
if not os.path.exists(config.test_exec_root):
    os.mkdir(config.test_exec_root)

config.substitutions.append(('%SDC', config.compiler_cli_bin))
config.substitutions.append(('%dafny', os.environ['SDC_DAFNY']))
config.substitutions.append(('%FileCheck', os.environ['SDC_FILE_CHECK']))
config.substitutions.append(('%not', os.environ['SDC_NOT']))

env_vars = {'HOME'}
for e in env_vars:
    if e in os.environ:
        config.environment[e] = os.environ[e]

_clean_test_directory(config.test_exec_root)
