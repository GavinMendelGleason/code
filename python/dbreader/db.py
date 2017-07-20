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
domain_name = config.DB

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
#            print constraint
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
@prefix %(domain_name)s: <%(domain)s> .
@prefix dacura: <http://dacura.scss.tcd.ie/ontology/dacura#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
""" % { 'domain_name' : domain_name , 'domain' : domain }

start = 0
prefix = 'http://dacura.scss.tcd.ie/ontology/dacura#'
def genid():
    global start
    uri = prefix + str(start)
    start += 1 
    return uri

def class_name(suffix):
    return 'prefix:' + suffix

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

def column_label(table,column):
    return table + '_' + column

def column_name(table,column):
    return domain_name + ':' + column_label(table,column)

def compose_label(cc,rcc):
    return 'fk+' + cc['REFERENCED_TABLE_NAME'] + '_' + cc['REFERENCED_COLUMN_NAME']

def compose_name(cc,rcc):
    return domain_name + ':' + compose_label(cc,rcc) 

def label_of(table):
    return table

def class_of(table):
    "Currently does nothing"
    return domain_name + ':' + label_of(table)

def run_class_construction(class_dict):
    tables = get_tables()
    doc = []
    for table in tables:
        
        class_record = """ 
%(class)s 
  a owl:class ;
  rdfs:label "%(label)s"@en ;
  rdfs:comment "%(label)s auto-generated from SQL table"@en .
""" % {'class' : class_of(table), 'label' : label_of(table)} 

        doc.append(class_record)
#        print '\n\n'
#        print 'Table: %s' % table
        
        columns = table_columns(table) 
        for column in columns:

#            print "Here? %s" % (table in class_dict)
#            print "there %s" % class_dict[table]
#            print "Column %s " % column
            if (table in class_dict
                and any(column['Field'] == c['COLUMN_NAME'] for c in class_dict[table])):

                # predicates by column
                preds = []

                # First find the column constraint
                cc = None
                for c in class_dict[table]:
                    if column['Field'] == c['COLUMN_NAME']:
                        cc = c
                        break

                if cc:

                    referenced_columns = table_columns(cc['REFERENCED_TABLE_NAME'])
                    rcc = None
                    # Find the referenced column spec
                    for rc in referenced_columns:
                        if rc['Field'] == cc['REFERENCED_COLUMN_NAME']:
                            rcc = rc
                    if rcc:
                        # Find out the type of the reference.
                        if is_primary(rcc):
                            preds.append({'pred' : compose_name(cc,rcc),
                                          'label' : compose_label(cc,rcc),
                                          'domain' : class_of(table),
                                          'rng' : class_of(cc['REFERENCED_TABLE_NAME'])})
                        else:
                            preds.append({'pred' : compose_name(cc,rcc),
                                          'label' : compose_label(cc,rcc),
                                          'domain' : class_of(table),
                                          'rng' : rcc})
                        
                    else:
                        pass
                else:
                    pass  
                

                for pred in preds:
                    formatted_pred = """
%(pred)s
  a owl:ObjectProperty ;
  rdfs:label "%(label)s"@en ;
  rdfs:comment "%(label)s auto-generated from SQL column"@en ;
  rdfs:domain %(domain)s ; 
  rdfs:range %(rng)s .
""" % pred                     
                    doc.append(formatted_pred)
            
            else:
                # We are a datatype
                rng = get_type_assignment(column['Type'])
                
                predicate = """
%(pred)s
  a owl:DatatypeProperty ;
  rdfs:label "%(label)s"@en ;
  rdfs:comment "%(label)s auto-generated from SQL column"@en ;
  rdfs:domain %(domain)s ; 
  rdfs:range %(rng)s .
""" % {'pred' : column_name(table,column['Field']),
       'label' : column_label(table,column['Field']),
       'domain' : class_of(table) ,
       'rng' : rng}
            
                doc.append(predicate)

    return doc

def lift_instance_data(tcd):
    triples = []
    tables = get_tables()
    
    for table in tables:
        columns = table_columns(table) 
        for column in columns:
            """select
             """

            
def render_turtle(doc):
    print preamble
    for s in doc:
        print s


#def create_triples
        
if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Translate from MySQL to OWL.')
    name_table = {}
    
    tcd = constraints(name_table)
    doc = run_class_construction(tcd)
    render_turtle(doc)
    
    lift_instance_data(tcd)
