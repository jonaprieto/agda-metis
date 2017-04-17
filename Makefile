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

.PHONY : doc
doc :
	agda --html src/ATP.agda
