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

MACROS=src/macros.xml

BUILD=../builds/pb100-build
LECTURE_BUILD_DIR=${BUILD}/lectures

${LECTURE_BUILD_DIR}:
	$(shell mkdir -p ${BUILD}/lectures)

.PHONY: lec1
lec1: ${BUILD}/lectures/lec1.html
${BUILD}/lectures/lec1.html: venv ./src/lec1.html ${MACROS} ${LECTURE_BUILD_DIR}
	${VENV} auxml singlefile \
	--macros ./src/macros.xml \
	--infile ./src/lec1.html \
	--outfile ${BUILD}/lectures/lec1.html

	# ---------------------------------
	echo "<!DOCTYPE html>" > /tmp/foo
	cat /tmp/foo ${BUILD}/lectures/lec1.html > /tmp/foo2
	mv /tmp/foo2 ${BUILD}/lectures/lec1.html


.PHONY: lec2
lec2: ${BUILD}/lectures/lec2.html
${BUILD}/lectures/lec2.html: venv ./src/lec2.xml ${MACROS} ${LECTURE_BUILD_DIR}
	${VENV} auxml singlefile \
	--macros ./src/macros.xml \
	--infile ./src/lec2.xml \
	--outfile ${BUILD}/lectures/lec2.html

	# ---------------------------------
	echo "<!DOCTYPE html>" > /tmp/foo
	cat /tmp/foo ${BUILD}/lectures/lec2.html > /tmp/foo2
	mv /tmp/foo2 ${BUILD}/lectures/lec2.html

.PHONY: lectures
lectures: lec1 lec2 media

.PHONY: media
media: ${BUILD}/media
${BUILD}/media: media/css/* media/js/*
	cp -av media ${BUILD}


.PHONY: serve
serve: 
	${PY} util/serve_livereload.py

.PHONY: clean-python
clean-python: 
	py3clean .

.PHONY: clean-build
clean-build: 
	trash ${BUILD}

.PHONY: clean-venv
clean-venv: 
	rm -rf venv

