ROOT_FOLDER=$(PWD)

export ROOT_FOLDER

m0-agreement:
	@$(MAKE) -C GenericMulticast0 agreement

m0-integrity:
	@$(MAKE) -C GenericMulticast0 integrity

m0-validity:
	@$(MAKE) -C GenericMulticast0 validity

mcast1:
	@$(MAKE) -C GenericMulticast1

