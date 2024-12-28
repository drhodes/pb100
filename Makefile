SHELL = bash
.SHELLFLAGS := -eu -o pipefail -c
MAKEFLAGS += --warn-undefined-variables
MAKEFLAGS += --no-builtin-rules

# -----------------------------------------------------------------------------
# Section: Python

VENV = source venv/bin/activate &&
PY = ${VENV} python3

venv: util/requirements.txt ## establish a virtual environment for python
	python3 -m venv venv && \
	${PY} -m pip install --upgrade pip
	${PY} -m pip install -r util/requirements.txt
	touch venv 


# -----------------------------------------------------------------------------
# Section: Lectures

MACROS=src/macros.html
BUILD=../builds/pb100-build
LECTURE_BUILD_DIR=${BUILD}/lectures

${BUILD}/lectures/%.html: venv ./src/%.html ${MACROS} 
	$(shell mkdir -p ${BUILD}/lectures)
	${VENV} auxml singlefile \
	--macros ./src/macros.html \
	--infile ./src/$(notdir $@) \
	--outfile ${BUILD}/lectures/$(notdir $@)

	sed -i '1s/^/<!DOCTYPE html>\n/' ${BUILD}/lectures/$(notdir $@)

LECTURES := about lec1 lec2 lec3 lec4
# BUILD_LEC := $(addprefix ${BUILD}/lectures/, $(addsuffix .html, $(LECTURES)))

$(LECTURES): %: ${BUILD}/lectures/%.html


.PHONY: lectures 
lectures: venv about ${LECTURES} media

.PHONY: media
media: ${BUILD}/media
${BUILD}/media: media/css/* media/js/* 
	cp -av media ${BUILD}


.PHONY: tidy
tidy:	
	tidy -q -e ${BUILD}/lectures/lec1.html


# -----------------------------------------------------------------------------
# Section: Deploy

.PHONY: deploy
deploy: venv lectures
	rsync -ravP ${BUILD} derek@proofbased.org:~/




# -----------------------------------------------------------------------------
# Section: Local development 

.PHONY: serve
serve: lectures
	${PY} util/serve_livereload.py



# -----------------------------------------------------------------------------
# Section: Cleaning


.PHONY: clean-python
clean-python: 
	py3clean .

.PHONY: clean-build
clean-build: 
	trash ${BUILD}

.PHONY: clean-venv
clean-venv: 
	rm -rf venv

.PHONY: clean-all
clean-all: clean-python clean-build 
