export AGDA ?= agda
export AGDADOC ?= $(AGDA) --html

.PHONY: clean
clean:
	find src/ -type f -name "*.agdai" -delete
	find src/ -type f -name "*.DS_Store" -delete
	rm -Rf html/

.PHONY : test
test:
	$(AGDA) --safe src/ATP/Metis.agda
	$(AGDA) --safe test/lazy-test.agda
	$(AGDA) --safe test/resolve.agda
	$(AGDA) --safe test/canonicalize.agda
	$(AGDA) --safe test/simplify.agda

.PHONY : canonicalize
canonicalize:
	$(AGDA) test/canonicalize.agda

.PHONY : resolve
resolve:
	$(AGDA) test/resolve.agda

.PHONY : doc
doc :
	agda --html src/ATP.agda
