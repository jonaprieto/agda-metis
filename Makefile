export AGDA ?= agda
export AGDADOC ?= $(AGDA) --html

.PHONY: clean
clean:
	find src/ -type f -name "*.agdai" -delete
	find src/ -type f -name "*.DS_Store" -delete
	rm -Rf html/

.PHONY : test
test:
	$(AGDA) src/ATP/Metis.agda
	$(AGDA) test/lazy-test.agda
	$(AGDA) test/resolve.agda
	$(AGDA) test/simplify.agda

.PHONY : canonicalize
canonicalize:
	$(AGDA) test/canonicalize.agda

.PHONY : resolve
resolve:
	$(AGDA) test/resolve.agda

.PHONY : doc
doc :
	agda --html src/ATP.agda
