.PHONY: clean
clean:
	find src/ -type f -name "*.agdai" -delete

.PHONY : test
test:
	agda src/ATP/Metis.agda
