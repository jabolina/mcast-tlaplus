ROOT_FOLDER=$(PWD)

export ROOT_FOLDER

mcast0:
	@$(MAKE) -C GenericMulticast0

mcast1:
	@$(MAKE) -C GenericMulticast1

