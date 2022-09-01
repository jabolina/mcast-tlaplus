ROOT_FOLDER=$(PWD)

export ROOT_FOLDER

m0-agreement:
	@$(MAKE) -C GenericMulticast0 agreement

m0-collision:
	@$(MAKE) -C GenericMulticast0 collision

m0-integrity:
	@$(MAKE) -C GenericMulticast0 integrity

m0-partial-order:
	@$(MAKE) -C GenericMulticast0 partial-order

m0-validity:
	@$(MAKE) -C GenericMulticast0 validity

m1-agreement:
	@$(MAKE) -C GenericMulticast1 agreement

m1-collision:
	@$(MAKE) -C GenericMulticast1 collision

m1-integrity:
	@$(MAKE) -C GenericMulticast1 integrity

m1-partial-order:
	@$(MAKE) -C GenericMulticast1 partial-order

m1-validity:
	@$(MAKE) -C GenericMulticast1 validity

m2-agreement:
	@$(MAKE) -C GenericMulticast2 agreement

m2-collision:
	@$(MAKE) -C GenericMulticast2 collision

m2-integrity:
	@$(MAKE) -C GenericMulticast2 integrity

m2-partial-order:
	@$(MAKE) -C GenericMulticast2 partial-order

m2-validity:
	@$(MAKE) -C GenericMulticast2 validity

a2-agreement:
	@$(MAKE) -C Algorithm2 agreement

a2-collision:
	@$(MAKE) -C Algorithm2 collision

a2-integrity:
	@$(MAKE) -C Algorithm2 integrity

a2-partial-order:
	@$(MAKE) -C Algorithm2 partial-order

a2-validity:
	@$(MAKE) -C Algorithm2 validity

article:
	@$(MAKE) -C Algorithm2 agreement
	@$(MAKE) -C Algorithm2 collision
	@$(MAKE) -C Algorithm2 integrity
	@$(MAKE) -C Algorithm2 partial-order
	@$(MAKE) -C Algorithm2 validity

generic-multicast-0:
	@$(MAKE) -C GenericMulticast0 agreement
	@$(MAKE) -C GenericMulticast0 collision
	@$(MAKE) -C GenericMulticast0 integrity
	@$(MAKE) -C GenericMulticast0 partial-order
	@$(MAKE) -C GenericMulticast0 validity

generic-multicast-1:
	@$(MAKE) -C GenericMulticast1 agreement
	@$(MAKE) -C GenericMulticast1 collision
	@$(MAKE) -C GenericMulticast1 integrity
	@$(MAKE) -C GenericMulticast1 partial-order
	@$(MAKE) -C GenericMulticast1 validity

generic-multicast-2:
	@$(MAKE) -C GenericMulticast2 agreement
	@$(MAKE) -C GenericMulticast2 collision
	@$(MAKE) -C GenericMulticast2 integrity
	@$(MAKE) -C GenericMulticast2 partial-order
	@$(MAKE) -C GenericMulticast2 validity

prune:
	$$0 $(ROOT_FOLDER)/bin/prune.sh
