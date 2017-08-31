#!/usr/bin/env python

import magic
import codecs

ifilename = 'schema-cleaned.sql'
ofilename = 'schema-translated.sql'

## Guess the type
blob = open(ifilename).read()
m = magic.open(magic.MAGIC_MIME_ENCODING)
m.load()
encoding = m.buffer(blob)
print encoding

## read at that type
fh = codecs.open(ifilename, 'r', encoding=encoding)
# write at utf-8
g = codecs.open(ofilename,'w', encoding='utf-8')
g.write(fh.read())

## Check that it is correct
blob = open(ofilename).read()
m = magic.open(magic.MAGIC_MIME_ENCODING)
m.load()
encoding = m.buffer(blob)
print encoding
