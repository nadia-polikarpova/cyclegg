import subprocess
import argparse
import pathlib
import csv

# 30s time limit
DEFAULT_TIME_LIMIT_MS = 30000

# Assumed UTF-8
SHELL_ENCODING = 'utf-8'

def make_cvc4_args(time_limit):
    # --stats required for timing and file info
    # All other required for running in inductive theorem proving mode
    # (see https://lara.epfl.ch/~reynolds/VMCAI2015-ind/)
    return ['--quant-ind', '--quant-cf', '--full-saturate-quant', '--stats', '--tlimit', str(time_limit)]

def run_file(cvc4_binary, filename, cvc4_args=make_cvc4_args(DEFAULT_TIME_LIMIT_MS), quiet=False):
    '''
    Runs an SMT2 file containing a theorem and returns whether it was proven
    successfully and the time taken
    '''
    if filename.suffix != '.smt2':
        if not quiet:
            print(f'File not SMT2, skipping: {filename}')
        return None
    res = subprocess.run([cvc4_binary.absolute(), *cvc4_args, filename.absolute()],
                         capture_output=True)
    stderr = res.stderr.decode(SHELL_ENCODING)
    last_two_lines = stderr.split('\n')[-3:-1]
    # The last two lines look like
    #
    #     driver::sat/unsat, unknown (TIMEOUT)
    #     driver::totalTime, 0.629364114
    #
    # so we can extract the result we want by taking the second item
    # after splitting on spaces.
    [result, time] = [item.split(' ')[1] for item in last_two_lines]
    time_ms = 1000 * float(time)
    # Due to the encoding, 'unsat' means that the theorem was proven,
    # so we translate it to not be confusing.
    return ('success' if result == 'unsat' else result, f'{time_ms:.2f} ms')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        prog='CVC4 Inductive Benchmark Runner',
        description='Runs CVC4 inductive benchmarks, collecting the results.',
        )

    parser.add_argument('cvc4_binary', type=pathlib.Path,
                        help='CVC4 binary (v1.5 recommended)',
                        )
    parser.add_argument('target', type=pathlib.Path,
                        help='SMT2 file or directory containing SMT2 files to run CVC4 on.',
                        )
    parser.add_argument('-t', '--timeout', type=int,
                        default=DEFAULT_TIME_LIMIT_MS,
                        help='Time limit for each CVC4 run.',
                        )
    parser.add_argument('-o', '--output', type=pathlib.Path,
                        help='Write the results as a CSV to',
                        )
    parser.add_argument('-q', '--quiet',
                        help='Suppress output.',
                        )

    args = parser.parse_args()
    cvc4_binary = args.cvc4_binary
    timeout = args.timeout
    target = args.target
    output = args.output
    quiet = args.quiet

    assert(cvc4_binary.is_file())
    assert(target.is_dir() or target.is_file())

    cvc4_args = make_cvc4_args(timeout)

    filenames = []
    if target.is_file():
        filenames = [target]
    if target.is_dir():
        filenames = sorted(target.iterdir())

    results = []
    for filename in filenames:
        run_result = run_file(cvc4_binary, filename, cvc4_args, quiet)
        if run_result:
            result, time = run_result
            if not quiet:
                print(filename)
                print(f'Result: {result}')
                print(f'Time: {time}')
            with open(filename, 'r') as smt_file:
                # Hack: the 3rd line from the last contains the prop
                # Using their formatting the nicer thing to do would
                # be to search for the line with the comment
                #
                #     ; G85
                #
                # where 85 is replaced by whatever number goal the file is.
                prop = smt_file.readlines()[-3].strip()
            results.append({'name': filename.name, 'result': result, 'time': time, 'prop': prop})
    if output:
        with open(output, 'w', newline='') as csvfile:
            fieldnames = ['name', 'result', 'time', 'prop']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for result in results:
                writer.writerow(result)
