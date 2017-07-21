#!/usr/bin/env python

import argparse
# import logging
import MySQLdb
import re
import config 


def get_tables(global_params):
    cur = global_params['db'].cursor()
    stmt = """
SELECT TABLE_NAME FROM INFORMATION_SCHEMA.TABLES
WHERE TABLE_TYPE = 'BASE TABLE' AND TABLE_SCHEMA=%(database)s
    """
    cur.execute(stmt, {'database' : config.DB})
    
    tables = [ table for (table,) in cur.fetchall() ]
    
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

def constraints(name_table,global_params):
    tables = get_tables(global_params)
    stmt = """
SELECT *
FROM INFORMATION_SCHEMA.KEY_COLUMN_USAGE
WHERE
REFERENCED_TABLE_SCHEMA = %(database)s AND REFERENCED_TABLE_NAME = %(table)s
    """
    cnstrs = {}
    for table in tables:
        cur = global_params['db'].cursor(MySQLdb.cursors.DictCursor)
        cur.execute(stmt, {'database' : global_params['db'] , 'table' : table})
        for constraint in cur:
#            print constraint
            if constraint['TABLE_NAME'] in cnstrs:
                cnstrs[constraint['TABLE_NAME']].append(constraint)
            else:
                cnstrs[constraint['TABLE_NAME']] = [constraint]

    return cnstrs

def table_columns(table,global_params):
    stmt = """
SHOW COLUMNS FROM %(table)s
    """ % {'table' : table}
    cur = global_params['db'].cursor(MySQLdb.cursors.DictCursor)
    cur.execute(stmt)
    return cur.fetchall()


"""
Select the primary key, and make this the object.

If it is an auto increment then we need to assign a URI. 

If it is not an auto increment number, we need to assign a URI and create an auxilliary 
predicate.
"""

start = 0
def genid(seed):
    global start
    uri = domain + '#' + seed + str(start)
    start += 1 
    return uri

#def class_name(suffix):
#    return 'prefix:' + suffix

#def is_auto (column):
#    return column['Extra'] == 'auto_increment'

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

def transform_to_xsd_value(e,ty):
    if re.search('int', ty):
        return ('"%d"^^xsd:integer' % e)
    elif re.search('varchar', ty):
        return ('"%s"@en' % e)
    elif re.search('date',ty):
        " need to fix the date here." 
        return ('"%s"^^xsd:dateTime' % e)
    else: 
        return ("%s" % e)
    
def type_is(col,ty):
    return re.search(ty,col['Type'])

def primary_keys(cols):
    prime = []
    for col_candidate in cols:
        if is_primary(col_candidate):
            prime.append(col_candidate)
    return prime

def non_primary_keys(cols):
    noprime = []
    for col_candidate in cols:
        if not is_primary(col_candidate):
            noprime.append(col_candidate)
    return noprime

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

def run_class_construction(class_dict,global_params):
    tables = get_tables(global_params)
    doc = []
    for table in tables:
        
        class_record = """ 
%(class)s 
  a owl:Class ;
  rdfs:label "%(label)s"@en ;
  rdfs:comment "%(label)s auto-generated from SQL table"@en .
""" % {'class' : class_of(table), 'label' : label_of(table)} 

        doc.append(class_record)
#        print '\n\n'
#        print 'Table: %s' % table
        
        columns = table_columns(table,global_params) 
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

                    referenced_columns = table_columns(cc['REFERENCED_TABLE_NAME'], global_params)
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

def where_key(d):
    components = []
    for key in d:
        components.append('%(key)s = %(value)s' % {'key' : key,
                                                   'value' : d[key]})
    return ' and '.join(components)

def lift_instance_data(tcd, global_params):
    triples = []
    tables = get_tables(global_params)
    cursor = global_params['db'].cursor(MySQLdb.cursors.DictCursor)

    swizzle_table = {}

    results = []

    for table in tables:
        columns = table_columns(table, global_params)

        keys = primary_keys(columns)
        npk = non_primary_keys(columns)

        key_names = [d['Field'] for d in keys]
        keystring = ','.join(key_names)

        stmt = """select %(keys)s from %(table)s
        """ % { 'keys' : keystring,
                'table' : table }

        cursor.execute(stmt)
        for row in cursor:
            uri = genid(table)

            swizzle_table[str(row.values())] = uri

            where = where_key(row)
            for c in npk:
                column_cursor = global_params['db'].cursor(MySQLdb.cursors.DictCursor)

                column_stmt = """select %(column)s , %(keys)s from %(table)s where %(where)s
                """ % { 'keys' : keystring,
                        'column' : c['Field'],
                        'where' : where,
                        'table' : table}

                cursor.execute(column_stmt)
                obj = cursor.fetchone()
                column_val = transform_to_xsd_value(obj[c['Field']], c['Type'])
                results.append((uri,column_name(table,c['Field']),column_val))

    return results
            
def render_turtle(doc,args):
    tot = args['preamble']
    for s in doc:
        tot += s + '\n'
    return tot

def render_triples(triples,args):
    tot = ""
    for (x,y,z) in triples:
        tot += x + ' ' + y + ' ' + z + '\n'

    return tot

#def create_triples
        
if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Translate from MySQL to OWL.')
    parser.add_argument('--schema-out', help='Log file', default='schema.ttl')
    parser.add_argument('--instance-out', help='Log file', default='instance.ttl')
    parser.add_argument('--db', help='Log file', default=config.DB)
    parser.add_argument('--user', help='DB User', default=config.USER)
    parser.add_argument('--passwd', help='DB passwd', default=config.PASSWORD)
    parser.add_argument('--host', help='DB host', default=config.HOST)
    global_params = vars(parser.parse_global_params())
    
    global_params['db'] = MySQLdb.connect(host=global_params['host'],
                                          user=global_params['user'],
                                          passwd=global_params['passwd'],  # your password
                                          db=global_params['db'])        # name of the data base

    global_params['domain'] = 'http://dacura.org/ontology/%(db_name)s' % {'db_name' : global_params['db']}
    global_params['domain_name'] = global_params['db']

    global_params['preamble'] = """@prefix %(domain_name)s: <%(domain)s#> .
@prefix dacura: <http://dacura.scss.tcd.ie/ontology/dacura#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
""" % { 'domain_name' : global_params['domain_name'] , 'domain' : global_params['domain'] }

    name_table = {}
    tcd = constraints(name_table,global_params)
    doc = run_class_construction(tcd,global_params)
    schema = render_turtle(doc,global_params)
    
    with open(global_params['schema_out'], "w") as text_file:
        text_file.write(schema)


    triples = lift_instance_data(tcd,global_params)
    instance = render_triples(triples)
    with open(global_params['instance_out'], "w") as text_file:
        text_file.write(instance)
