#!/usr/bin/env python

import argparse
# import logging
import MySQLdb
import re
import config 

db = MySQLdb.connect(host=config.HOST,
                     user=config.USER,
                     passwd=config.PASSWORD,  # your password
                     db=config.DB)        # name of the data base

domain = 'http://dacura.org/%(db_name)s' % {'db_name' : config.DB }

def get_tables():
    cur = db.cursor()
    stmt = """
SELECT TABLE_NAME FROM INFORMATION_SCHEMA.TABLES
WHERE TABLE_TYPE = 'BASE TABLE' AND TABLE_SCHEMA=%(database)s
    """
    cur.execute(stmt, {'database' : config.DB})
    
    tables = [ table for (table,) in cur.fetchall() ]
    
    return tables

# Not sure how to do this yet,
# we may need a pull-back for cross product indices 
def create_table_name_map():
    tables = get_tables()
    return tables


def classes(edges):
    cns = {}
    for edge in edges:
        cns[edge['name']] = True
    return len(cns)

def intermediate_name(cs):
    res = "%s" % c[0]['edge']
    for c in cs[1:]:
        res += '_x_'+c['edge']
    return res

def intermediate_predicate_name(cs):
    return intermediate_name(cs)

def intermediate_class_name(cs):
    n = intermediate_name(cs)
    return n[0].upper() + n[1:]

def predicates_of_intermediates(cs):
    return []
#    preds = []
#    for c in cs:
#        { 'domain' : intermediate_class_name(cs),
#          'edge' : cs['edge']
#          'range' : 

def pullbacks():
    class_table = {}
    reference_table = {}
    
    stmt = """
SELECT *
FROM INFORMATION_SCHEMA.KEY_COLUMN_USAGE
WHERE TABLE_NAME = %(table)s
    """

    for table in get_tables():
        
        cur = db.cursor(MySQLdb.cursors.DictCursor)
        cur.execute(stmt, {'database' : config.DB , 'table' : table})
        collect = {}
        for constraint in cur:
            if constraint['CONSTRAINT_NAME'] == 'PRIMARY':
                collect[constraint['ORDINAL_POSITION']] = constraint['COLUMN_NAME']

        # Only one primary key
        class_table[table] = collect.values()

    stmt = """
SELECT *
FROM INFORMATION_SCHEMA.KEY_COLUMN_USAGE
WHERE
REFERENCED_TABLE_SCHEMA = %(database)s AND TABLE_NAME = %(table)s
    """

    reference_table = {}
    for table in get_tables():
        reference_table[table] = {}
        
        cur = db.cursor(MySQLdb.cursors.DictCursor)
        cur.execute(stmt, {'database' : config.DB , 'table' : table})
        
        for constraint in cur:
            if constraint['REFERENCED_TABLE_NAME'] in collect:
                reference_table[table][constraint['REFERENCED_TABLE_NAME']].append(constraint['REFERENCED_COLUMN_NAME'])
            else:
                reference_table[table][constraint['REFERENCED_TABLE_NAME']] = [constraint['REFERENCED_COLUMN_NAME']]
                
        # Only one primary key
        reference_table[table] = collect.values()


        
        
    return class_table, reference_table

#def pullbacks(edges):
#    collect = {}
#    for edge in edges:
#        if edge['name'] in collect:
#            collect[edge['name']].append(edge)
#        else:
#            collect[edge['name']] = [edge]
#            
#    pb = []
#    for c in collect:
#        if len(c) > 1:            
#            pb.append({'domain' : c[0]['domain'],
#                       'intermediate_class' : intermediate_class_name(c),
#                       'intermediate_predicate' : intermediate_predicate_name(c),
#                       'preds' : predicates_of_intermediates(c)})
#    return pb

def constraints(name_table):
    tables = get_tables()
    stmt = """
SELECT *
FROM INFORMATION_SCHEMA.KEY_COLUMN_USAGE
WHERE
REFERENCED_TABLE_SCHEMA = %(database)s AND REFERENCED_TABLE_NAME = %(table)s
    """
    cnstrs = {}
    for table in tables:
        cur = db.cursor(MySQLdb.cursors.DictCursor)
        cur.execute(stmt, {'database' : config.DB , 'table' : table})
        for constraint in cur:
            print constraint
            if constraint['TABLE_NAME'] in cnstrs:
                cnstrs[constraint['TABLE_NAME']].append(constraint)
            else:
                cnstrs[constraint['TABLE_NAME']] = [constraint]

    return cnstrs

def table_columns(table):
    stmt = """
SHOW COLUMNS FROM %(table)s
    """ % {'table' : table}
    cur = db.cursor(MySQLdb.cursors.DictCursor)
    cur.execute(stmt)
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

def is_primary (column):
    return column['Key'] == 'PRI'

def get_type_assignment(ty):
    """This needs to be extended"""
    if re.search('int',ty):
        return 'xsd:integer'
    elif re.search('varchar',ty) or re.search('text', ty):
        return 'xsd:string'
    elif re.search('date',ty):
        return 'xsd:dateTime'
    else:
        return 'rdf:literal'

def type_is(col,ty):
    return re.search(ty,col['Type'])

def primary_keys(cols):
    prime = []
    for col_candidate in cols:
        if is_primary(col_candidate):
            prime.append(col_candidate)
    return prime

def composite(col,cols):
    p = primary_keys(cols)
    return col in p

def run_class_construction(class_dict):
    tables = get_tables()
    doc = []
    for table in tables:
        
        class_record = """ 
domain:%(class)s 
  a owl:class ;
  rdfs:label "%(class)s"@en ;
  rdfs:comment "%(class)s auto-generated from SQL table"@en .
""" % {'class' : table} 

        doc.append(class_record)
        print '\n\n'
        print 'Table: %s' % table
        
        columns = table_columns(table) 
        for column in columns:
            # column information
            print column
            if is_auto(column) or (is_primary(column) and not composite(column,columns)):
                # We are the identifier for the object type.
                # As such there is no need to store the column, it will be the
                # the class itself. We will decide what to do with the
                # datatype as needed when creating (or migrating) instances.
                pass
            if composite(column,columns):
                pass
            else:
                if table in class_dict:
                    for cnst in class_dict['table']:
                        print cnst
                        preds = [] 
                        preds.append({'pred' : column['Field'] ,
                                      'domain' : table ,
                                      'range' : class_dict[table]['range']})
                                
                    predicate_tmpl = """
domain:%(dom)s
  a owl:ObjectProperty ;
  rdfs:label "%(pred)s"@en ;
  rdfs:comment "%(pred)s auto-generated from SQL column"@en ;
  rdfs:domain domain:%(dom)s ; 
  rdfs:range domain:%(rng)s .
"""

                    for pred in preds: 
                        doc.append(predicate_tmpl % pred)
                    
                else:
                    # We are a datatype
                    rng = get_type_assignment(column['Type'])

                    predicate = """
domain:%(dom)s_%(pred)s
  a owl:DatatypeProperty ;
  rdfs:label "%(pred)s"@en ;
  rdfs:comment "%(pred)s auto-generated from SQL column"@en ;
  rdfs:domain domain:%(dom)s ; 
  rdfs:range domain:%(rng)s .
""" % {'pred' : column['Field'] , 'dom' : table , 'rng' : rng}
            
                    doc.append(predicate)

    return doc

def render_turtle(doc):
    print preamble
    for s in doc:
        print s

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Translate from MySQL to OWL.')
    name_table = {}
    
    tcd = constraints(name_table)
    doc = run_class_construction(tcd)
    # render_turtle(doc)
