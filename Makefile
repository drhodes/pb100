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

.PHONY: about
about: ${BUILD}/lectures/about.html
${BUILD}/lectures/about.html: venv ./src/about.html ${MACROS} ${LECTURE_BUILD_DIR}
	${VENV} auxml singlefile \
	--macros ./src/macros.xml \
	--infile ./src/about.html \
	--outfile ${BUILD}/lectures/about.html

	sed -i '1s/^/<!DOCTYPE html>\n/' ${BUILD}/lectures/about.html

	# echo "<!DOCTYPE html>" > /tmp/foo
	# cat /tmp/foo ${BUILD}/lectures/about.html > /tmp/foo2
	# mv /tmp/foo2 ${BUILD}/lectures/about.html


.PHONY: lec1
lec1: ${BUILD}/lectures/lec1.html
${BUILD}/lectures/lec1.html: venv ./src/lec1.html ${MACROS} ${LECTURE_BUILD_DIR}
	${VENV} auxml singlefile \
	--macros ./src/macros.xml \
	--infile ./src/lec1.html \
	--outfile ${BUILD}/lectures/lec1.html

	sed -i '1s/^/<!DOCTYPE html>\n/' ${BUILD}/lectures/lec1.html

.PHONY: tidy
tidy:	
	tidy -q -e ${BUILD}/lectures/lec1.html


.PHONY: lec2
lec2: ${BUILD}/lectures/lec2.html
${BUILD}/lectures/lec2.html: venv ./src/lec2.html ${MACROS} ${LECTURE_BUILD_DIR}
	${VENV} auxml singlefile \
	--macros ./src/macros.xml \
	--infile ./src/lec2.html \
	--outfile ${BUILD}/lectures/lec2.html

	sed -i '1s/^/<!DOCTYPE html>\n/' ${BUILD}/lectures/lec2.html

.PHONY: lec3
lec3: ${BUILD}/lectures/lec3.html
${BUILD}/lectures/lec3.html: venv ./src/lec3.xml ${MACROS} ${LECTURE_BUILD_DIR}
	${VENV} auxml singlefile \
	--macros ./src/macros.xml \
	--infile ./src/lec3.xml \
	--outfile ${BUILD}/lectures/lec3.html

	sed -i '1s/^/<!DOCTYPE html>\n/' ${BUILD}/lectures/lec3.html

.PHONY: lec4
lec4: ${BUILD}/lectures/lec4.html
${BUILD}/lectures/lec4.html: venv ./src/lec4.xml ${MACROS} ${LECTURE_BUILD_DIR}
	${VENV} auxml singlefile \
	--macros ./src/macros.xml \
	--infile ./src/lec4.xml \
	--outfile ${BUILD}/lectures/lec4.html

	sed -i '1s/^/<!DOCTYPE html>\n/' ${BUILD}/lectures/lec4.html


.PHONY: lectures 
lectures: venv about lec1 lec2 lec3 lec4 media 

.PHONY: media
media: ${BUILD}/media
${BUILD}/media: media/css/* media/js/* 
	cp -av media ${BUILD}


# THEOREMS:=src/pb100/Pb100/
# ${THEOREM}/*.lean: venv
# 	echo '$%'
# 	echo pygmentize -f html -l lean -o test.html theorem-1-1-12.lean


THEOREMS_LEAN := $(wildcard src/pb100/Pb100/theorem-*.lean)
THEOREMS_HTML = $(pathsubst %.lean, %.html, $(THEOREMS_LEAN))
THEOREMS_HTML_DIR=media/html/theorems
.PHONY: asdf
asdf: ${THEOREMS_LEAN}
	echo $^
	echo ${THEOREMS_HTML_DIR}
	echo ${THEOREMS_HTML}



# -----------------------------------------------------------------------------
# Section: Deploy

.PHONY: deploy
deploy: venv lectures
	rsync -ravP ${BUILD} derek@proofbased.org:~/

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

.PHONY: clean-all
clean-all: clean-python clean-build 
