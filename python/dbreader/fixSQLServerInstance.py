#!/usr/bin/env python

import magic
import codecs
import re

ifilename = 'ipgdata-cleaned.sql'
ofilename = 'ipgdata-translated.sql'

## Guess the type
#blob = open(ifilename).read()
#m = magic.open(magic.MAGIC_MIME_ENCODING)
#m.load()
#encoding = m.buffer(blob)

## read at that type
fh = codecs.open(ifilename, 'r', encoding='utf-16-le')
# write at utf-8
g = codecs.open(ofilename,'w', encoding='utf-8')

for line in fh:
    if re.match('^SET',line):
        pass
    else:
        s = re.sub('\[dbo\]\.\[(.*)\] ', "ipg.\g<1> ", line)
        s = re.sub('\[', "'", s)
        s = re.sub('\]', "'", s)
        s = re.sub(" N'", " '", s)
    
        g.write(s)

g.close()

## Check that it is correct
#blob = open(ofilename).read()
#m = magic.open(magic.MAGIC_MIME_ENCODING)
#m.load()
#encoding = m.buffer(blob)
#print encoding


