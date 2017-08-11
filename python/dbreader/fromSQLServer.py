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
termpat = re.compile(".*;\s*$")
insertintopat = re.compile("^INSERT INTO",re.I)
msnewlinepat = re.compile(r'(.*)\r\n')

# substitution matchers
fixquotes = re.compile('\[([^\]]*)\]')
fixstrings = re.compile("N'")
fixdbname = re.compile('"[^"]*"\.')
fixdate = re.compile('DateTime')

def passes(line):
    c = line.count('"')
    d = line.count("'")

    if c % 2 == 0 and d % 2 == 0:
        return True
    else:
        return False

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
            with codecs.open(global_params['out'] + '.err', "w", encoding='utf8') as errstream:
                
                count = 0
                for line in inputstream:
                    oline = line
                    count += 1
                
                    # put oline drops here                
                    if usepat.match(oline):
                        oline = None
                    elif gopat.match(oline):
                        oline = None
                    elif setpat.match(oline):
                        oline = None
                    elif emptypat.match(oline):
                        oline = None
                    else:
                        pass

                    if oline:
                        # put transforms here
                        oline = re.sub(fixquotes,'"\g<1>"',oline)
                        oline = re.sub(fixstrings,"'",oline)
                        oline = re.sub(fixdbname, ('"%s".' % global_params['schema_name']), oline)
                        oline = re.sub(fixdate,'timestamp',oline)
                        if not termpat.match(oline):
                            oline = re.sub(msnewlinepat, r'\g<1>;\n', oline)
                        if not insertintopat.match(oline):
                            oline = re.sub(r'INSERT', 'INSERT INTO', oline) 
                            
                        # sanity check output or throw in error file
                        if passes(oline):                            
                            outputstream.write(oline)                            
                        else: 
                            errstream.write(oline)
