ROOT_FOLDER=$(PWD)

export ROOT_FOLDER

mcast0:
	@$(MAKE) -C GenericMulticast0 simple

mcast0-agreement:
	@$(MAKE) -C GenericMulticast0 agreement

mcast1:
	@$(MAKE) -C GenericMulticast1

