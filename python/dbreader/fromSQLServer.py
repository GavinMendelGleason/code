#!/usr/bin/env python

import argparse
import magic
import codecs
import re
import os

usepat = re.compile('.*USE .*')
gopat = re.compile('^GO.*')
setpat = re.compile('^SET.*')
emptypat = re.compile('^\s*$')

# substitution matchers
fixquotes = re.compile('\[([^\]]*)\]')
fixstrings = re.compile("N'")
fixdbname = re.compile('"[^"]*"\.')
fixdate = re.compile('DateTime')
    
if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Translate instance data from SQLServer to Postgres.')
    parser.add_argument('--schema-out', help='Log file', default='schema.ttl')
    parser.add_argument('--input-encoding', help='Input encoding', default='utf-16le')
    parser.add_argument('--in', help='Input row data', default='instance.sql')
    parser.add_argument('--out', help='Output row data', default='psql-instance.sql')
    parser.add_argument('--schema-name', help='Name of schema in Postgres', default='ipg')
    global_params = vars(parser.parse_args())



    with codecs.open(global_params['in'], "r", encoding=global_params['input_encoding']) as inputstream:
        with codecs.open(global_params['out'], "w", encoding='utf8') as outputstream:

            count = 0
            for line in inputstream:
                count += 1
                
                # put line drops here                
                if usepat.match(line):
                    line = None
                elif gopat.match(line):
                    line = None
                elif setpat.match(line):
                    line = None
                elif emptypat.match(line):
                    line = None
                else:
                    pass
            
                if line:
                    # put transforms here
                    line = re.sub(fixquotes,'"\g<1>"',line)
                    line = re.sub(fixstrings,"'",line)
                    line = re.sub(fixdbname, ('"%s".' % global_params['schema_name']), line)
                    line = re.sub(fixdate,'timestamp',line)
                                  
                    outputstream.write(line)
    

