


#!/usr/bin/env python
from livereload import Server, shell
server = Server()
server.watch('./src/*', shell('make lectures'))
server.watch('./media/css/main.css', shell('make media'))
server.watch('./media/js/*', shell('make media'))
server.serve(root='../builds/pb100-build/')


