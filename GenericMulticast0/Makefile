SPEC_FOLDER=$(ROOT_FOLDER)/GenericMulticast0

agreement:
	@echo "===== Always conflicting! ====="
	sh $(ROOT_FOLDER)/tlc.sh $(SPEC_FOLDER) Agreement/Agreement.tla Agreement/Agreement-AlwaysConflict.cfg
	@echo "===== Never conflicting! ====="
	sh $(ROOT_FOLDER)/tlc.sh $(SPEC_FOLDER) Agreement/Agreement.tla Agreement/Agreement-NeverConflict.cfg
	@echo "===== ID conflicting! ====="
	sh $(ROOT_FOLDER)/tlc.sh $(SPEC_FOLDER) Agreement/Agreement.tla Agreement/Agreement-IdConflict.cfg

integrity:
	@echo "===== Always conflicting! ====="
	sh $(ROOT_FOLDER)/tlc.sh $(SPEC_FOLDER) Integrity/Integrity.tla Integrity/Integrity-AlwaysConflict.cfg
	@echo "===== Never conflicting! ====="
	sh $(ROOT_FOLDER)/tlc.sh $(SPEC_FOLDER) Integrity/Integrity.tla Integrity/Integrity-NeverConflict.cfg
	@echo "===== ID conflicting! ====="
	sh $(ROOT_FOLDER)/tlc.sh $(SPEC_FOLDER) Integrity/Integrity.tla Integrity/Integrity-IdConflict.cfg

validity:
	sh $(ROOT_FOLDER)/tlc.sh $(SPEC_FOLDER) Validity/Validity.tla
