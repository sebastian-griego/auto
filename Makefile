.PHONY: setup lean-build validate ring-regression set-regression

setup:
	./scripts/setup.sh

lean-build:
	cd lean && lake build

validate:
	cd harness && python -m autoform_eval.cli validate --split pilot

ring-regression:
	./scripts/run_ring_identity_regression.sh

set-regression:
	./scripts/run_set_equality_regression.sh
