# Exact certificate validator

Run from the Experiment 002 root:

```text
python3 validator/validate_operator_cayley.py \
  certificates/operator_cayley_core.json \
  --receipt metadata/operator_cayley_run_receipt.json \
  --source-root source/julia

python3 controls/run_validator_regression.py
```

The validator accepts only normalized Gaussian-rational encodings, closed structural
key sets, matching source/core/run hashes, reconstructed exact matrix identities, and
the separately fixed numerical limit `1e-10`. The regression suite reports unique
test cases separately from process invocations.

Passing this validator means the finite certificate is internally and independently
reconstructed. It does not prove a universal matrix theorem; that is Lean's role.
