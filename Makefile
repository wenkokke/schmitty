AGDA ?= agda
SHELL := sh
SOURCES := $(shell find . -type f -and -path './src/*' -and -name '*.agda')
OBJECTS := $(SOURCES:.agda=.agdai)
MODULES := $(subst /,.,$(subst ./src/,,$(basename $(SOURCES))))
DOCS := $(addprefix ./docs/,$(addsuffix .html,$(MODULES)))


default: listings

########################
# Initialise Git hooks #
########################

.PHONY: init
init:
	git config core.hooksPath .githooks


#######################
# Generate index.agda #
#######################

index.agda: $(SOURCES)
	@echo "module index where\n$(foreach module_name,$(MODULES),\nimport $(module_name))" > index.agda


##################
# Positive tests #
##################

TEST_SUCCEED_SOURCES := $(shell find . -type f -and -path './test/Succeed/*' -and -name '*.agda')
TEST_SUCCEED_OBJECTS := $(TEST_SUCCEED_SOURCES:.agda=.agdai)

test/Succeed/%.agdai: test/Succeed/%.agda
	@echo "Checking $(notdir $(basename $<))..."
	@$(AGDA) -v0 -isrc -itest/Succeed "$<"

.PHONY: test-succeed
test-succeed: $(TEST_SUCCEED_OBJECTS)


##################
# Negative tests #
##################

TEST_FAIL_SOURCES := $(shell find . -type f -and -path './test/Fail/*' -and -name '*.agda')
TEST_FAIL_OBJECTS := $(TEST_FAIL_SOURCES:.agda=.agdai)

# TODO: Failing tests don't generate *.agdai files,
#       so effectively these are .PHONY tasks.
test/Fail/%.agdai: test/Fail/%.agda test/Fail/%.err
	@echo "Checking $(notdir $(basename $<))..."
	@$(AGDA) -v0 -isrc -itest/Fail "$<" \
	        | tail -n +2 \
	        | diff --suppress-common-lines "$(<:.agda=.err)" -

.PHONY: test-fail
test-fail: $(TEST_FAIL_OBJECTS)


#############
# All Tests #
#############

index.agdai: index.agda
	@echo "Checking schmitty..."
	@$(AGDA) -i. -isrc index.agda

.PHONY: test
test: \
	index.agdai \
	$(TEST_SUCCEED_OBJECTS) \
	$(TEST_FAIL_OBJECTS)


#####################
# Generate listings #
#####################

docs/index.html: index.agda
	@echo "Generating listings..."
	@$(AGDA) -v0 -i. -isrc index.agda --html --html-dir=docs

.PHONY: listings
listings: $(DOCS)

define HTML_template
$(1): docs/index.html
endef
$(foreach html_file,$(DOCS),$(eval $(call HTML_template,$(html_file))))

