FSTAR_HOME ?= $(HOME)/.everest/FStar
FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe
FSTAR_ULIB ?= $(FSTAR_HOME)/ulib
FSTAR_Z3_VERSION ?= 4.15.4
ODIR ?= .fstar-cache
CHECK = "$(FSTAR)" \
	--z3version "$(FSTAR_Z3_VERSION)" \
	--report_assumes error \
	--cache_checked_modules \
	--include "$(FSTAR_ULIB)" \
	--include . \
	--odir "$(ODIR)"

.PHONY: verify

verify:
	$(CHECK) ReverseAdd.fst
	$(CHECK) ReverseAddCarry.fst
	$(CHECK) ReverseAddOverflowProfile.fst
	$(CHECK) ReverseAddCarrySummary.fst
	$(CHECK) ReverseAddWitness.fst
	$(CHECK) ReverseAddHighSum.fst
	$(CHECK) ReverseAddBoundary.fst
	$(CHECK) AbstractReachability.fst
	$(CHECK) ReverseAddResidue.fst
	$(CHECK) ReverseAddModPair.fst
	$(CHECK) ReverseAddBlockCarry.fst
	$(CHECK) ReverseAddFixedWidth.fst
	$(CHECK) ReverseAddInvariant.fst
	$(CHECK) ReverseAddFixed3.fst
	$(CHECK) ReverseAddRefinedProduct.fst
	$(CHECK) ReverseAdd196.fst
	$(CHECK) ReverseAddCEGAR.fst
	$(CHECK) ReverseAddPredecessor.fst
	$(CHECK) AbstractReachabilityExample.fst
