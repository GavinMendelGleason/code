#!/usr/bin/env python

import MySQLdb
import re

db_name = 'dacura_wordpress'
db = MySQLdb.connect(host="localhost",    # your host, usually localhost
                     user="root",         # your username
                     passwd="root",  # your password
                     db="dacura_wordpress")        # name of the data base


domain = 'http://dacura.org/%(db_name)s' % {'db_name' : db_name }

def get_tables ():
    cur = db.cursor()
    cur.execute(
        """
        SELECT TABLE_NAME FROM INFORMATION_SCHEMA.TABLES
        WHERE TABLE_TYPE = 'BASE TABLE' AND TABLE_SCHEMA='dacura_wordpress'
        """)
    
    tables = [ table for (table,) in cur.fetchall() ]
    
    return tables

def table_columns (table):
    columns = """
    SHOW COLUMNS FROM %s
    """

    query = columns % table
    cur = db.cursor(MySQLdb.cursors.DictCursor)
    cur.execute(query)
    return cur.fetchall()


"""
Select the primary key, and make this the object.

If it is an auto increment then we need to assign a URI. 

If it is not an auto increment number, we need to assign a URI and create an auxilliary 
predicate.
"""

preamble = """
@prefix domain: <%(domain)s> .
@prefix dacura: <http://dacura.scss.tcd.ie/ontology/dacura#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
""" % { 'domain' : domain }

start = 0
prefix = 'http://dacura.scss.tcd.ie/ontology/dacura#'
def genid():
    global start
    uri = prefix + str(start)
    start += 1 
    return uri

def class_name(suffix):
    return 'domain:' + suffix

def is_auto (column):
    return column['Extra'] == 'auto_increment'

def get_xsd_type(ty):
    """"""
    if re.search('int',ty):
        return 'xsd:integer'
    elif re.search('varchar',ty):
        return 'xsd:string'
    else:
        return 'rdf:literal'

def construct_class_identies():
    """This function assigns foreign key constraints of given columns to object identifiers.
    """

def run_class_construction(table_class_dict):
    tables = get_tables()
    doc = []
    for table in tables:
        
        c = class_name(table)
        
        class_record = """ 

domain:%(class)s 
  a owl:class ;
  rdfs:label "%(class)s"@en ;
  rdfs:comment "%(class)s auto-generated from SQL table"@en .
""" % {'class' : c} 

        doc.append(class_record)
        print '\n\n'
        print 'Table: %s' % c
        
        for column in table_columns(table):
            print column
            if is_auto(column):
                pass
            else:
                xsd_type=get_xsd_type(column['Type'])

                predicate = """
domain:%(pred)s
  a owl:DatatypeProperty ;
  rdfs:label "%(pred)s"@en ;
  rdfs:comment "%(pred)s auto-generated from SQL column"@en ;
  rdfs:domain %(class)s ; 
  rdfs:range %(type)s .
""" % {'pred' : column['Field'] , 'class' : c , 'type' : xsd_type}
            
                doc.append(predicate)


def render_turtle(doc):
    print preamble
    for s in doc:
        print s

if __name__ == "__main__":
    #render_turtle(doc)
    
    pass
