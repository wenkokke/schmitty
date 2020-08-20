init:
	git config core.hooksPath .githooks

test:
	agda -i. -isrc index.agda

listings:
	agda -i. -isrc index.agda --html --html-dir=docs
