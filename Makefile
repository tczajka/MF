.PHONY: all
all: tests

tests:
	mlton tests.mlb

.PHONY: clean
clean:
	rm -f tests
