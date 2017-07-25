#!/usr/bin/env python

import argparse
# import logging
import MySQLdb
import re
import config 
import codecs
import urllib

def get_tables(global_params):
    cur = global_params['dbo'].cursor()
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
        cur = global_params['dbo'].cursor(MySQLdb.cursors.DictCursor)
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
    cur = global_params['dbo'].cursor(MySQLdb.cursors.DictCursor)
    cur.execute(stmt)
    return cur.fetchall()


"""
Select the primary key, and make this the object.

If it is an auto increment then we need to assign a URI. 

If it is not an auto increment number, we need to assign a URI and create an auxilliary 
predicate.
"""

start = 0
def genid(seed,args):
    global start
    uri = args['instance'] + '#' + seed + str(start)
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
    print e
    print ty
    res = None
    if re.search('int', ty):
        res = ('"%d"^^xsd:integer' % e)
    elif re.search('varchar', ty):
        res = ('"%s"@en' % e)
    elif re.search('date',ty):
        " need to fix the date here." 
        res = ('"%s"^^xsd:dateTime' % e)
    elif re.search('text',ty):
        res = ('"%s"@en' % e)
    else: 
        res = ("%s" % e)
    print res
    return res

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

def column_name(table,column,args):
    cleaned_uri = urllib.quote(column_label(table,column))
    return args['domain_name'] + ':' + cleaned_uri

def compose_label(cc,rcc):
    return 'fk-' + cc['REFERENCED_TABLE_NAME'] + '_' + cc['REFERENCED_COLUMN_NAME']

def compose_name(cc,rcc,args):
    cleaned_uri = urllib.quote(compose_label(cc,rcc))
    return args['domain_name'] + ':' + compose_label(cc,rcc) 

def label_of(table):
    return table

def class_of(table,args):
    "Currently does nothing"
    cleaned_uri = urllib.quote(label_of(table))
    return args['domain_name'] + ':' + cleaned_uri

def run_class_construction(class_dict,global_params):
    tables = get_tables(global_params)
    doc = []
    for table in tables:
        
        class_record = """ 
%(class)s 
  a owl:Class ;
  rdfs:subClassOf dacura:Entity ;
  rdfs:label "%(label)s"@en ;
  rdfs:comment "%(label)s auto-generated from SQL table"@en .
""" % {'class' : class_of(table,global_params), 'label' : label_of(table)} 

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
                            preds.append({'pred' : compose_name(cc,rcc,global_params),
                                          'label' : compose_label(cc,rcc),
                                          'domain' : class_of(table, global_params),
                                          'rng' : class_of(cc['REFERENCED_TABLE_NAME'], global_params)})
                        else:
                            preds.append({'pred' : compose_name(cc,rcc, global_params),
                                          'label' : compose_label(cc,rcc),
                                          'domain' : class_of(table, global_params),
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
""" % {'pred' : column_name(table,column['Field'],global_params),
       'label' : column_label(table,column['Field']),
       'domain' : class_of(table, global_params) ,
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
    cursor = global_params['dbo'].cursor(MySQLdb.cursors.DictCursor)

    swizzle_table = {}

    results = []

    # Pass 1 to get swizzle table
    for table in tables:
        columns = table_columns(table, global_params)

        keys = primary_keys(columns)
        npk = non_primary_keys(columns)

        if (len(keys) == 0):
            keys = npk
        
        key_names = [d['Field'] for d in keys]
        keystring = ','.join(key_names)

        stmt = """select %(keys)s from %(table)s
        """ % { 'keys' : keystring,
                'table' : table }

        cursor.execute(stmt)
        for row in cursor:
            uri = genid(table, global_params)

            swizzle_table[table+str(row.values())] = uri
            
    # Pass 2 to use swizzle table
    for table in tables:
        columns = table_columns(table, global_params)

        keys = primary_keys(columns)
        npk = non_primary_keys(columns)

        if (len(keys) == 0):
            keys = npk
        
        key_names = [d['Field'] for d in keys]
        keystring = ','.join(key_names)

        stmt = """select %(keys)s from %(table)s
        """ % { 'keys' : keystring,
                'table' : table }

        cursor.execute(stmt)
        for row in cursor:

            uri = swizzle_table[table+str(row.values())]
            
            # Add the type information to triples 
            results.append((uri, 'rdf:type', class_of(table,global_params)))
            
            where = where_key(row)
            #print where
            
            for c in columns:

                column_cursor = global_params['dbo'].cursor(MySQLdb.cursors.DictCursor)

                column_stmt = """select %(column)s , %(keys)s from %(table)s where %(where)s
                """ % { 'keys' : keystring,
                        'column' : c['Field'],
                        'where' : where,
                        'table' : table}

                cursor.execute(column_stmt)
                obj = cursor.fetchone()

                # \/\/ Reference lookup here

                if (table in tcd
                    and any(c['Field'] == cspec['COLUMN_NAME'] for cspec in tcd[table])):
                    cc = None
                    for cprime in tcd[table]:
                        if c['Field'] == cprime['COLUMN_NAME']:
                            cc = cprime
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
                            if is_primary(rcc) and obj[c['Field']]:
                                keyed_value_stmt = """select %(field)s from %(table)s 
where %(key)s = %(val)s""" % { 'field' : rcc['Field'],
                               'table' : cc['REFERENCED_TABLE_NAME'],
                               'key' : rcc['Field'],
                               'val' : obj[c['Field']]}
                                
                                cursorprime = global_params['dbo'].cursor(MySQLdb.cursors.DictCursor)
                                cursorprime.execute(keyed_value_stmt)
                                keyrow = cursorprime.fetchone()
                                if keyrow and cc['REFERENCED_TABLE_NAME']+str(keyrow.values()) in swizzle_table:
                                    column_val = swizzle_table[cc['REFERENCED_TABLE_NAME']+str(keyrow.values())]
                                    results.append((uri,compose_name(cc,rcc, global_params),column_val))
                
                                    
                # ^^^^ Reference lookup here

                # skip if null
                if obj[c['Field']]:                
                    results.append((uri,column_name(table,c['Field'], global_params),transform_to_xsd_value(obj[c['Field']], c['Type'])))
            # And add the class of the elt.             
        
    return results
            
def render_turtle(doc,args):
    tot = args['preamble']
    for s in doc:
        tot += s + '\n'
    return tot

def is_uri(obj):
    return re.match('^http(s?)://', obj)

def render_point(point, args):
    for key in args:
        cleaned = args[key] 
        point = re.sub(key + ':', cleaned, point)

    if is_uri(point):
        point = "<" + point + ">"
    else:
        point = re.sub('\^\^(.*)$','^^<\g<1>>',point)

    return point

def render_triples(triples,ns):
    tot = ""
    for (x,y,z) in triples:
        # kill nulls. 
        if x and y and z:
            tot += render_point(x,ns) + ' ' + render_point(y,ns) + ' ' + render_point(z,ns) + ' .\n'

    return tot

def render_turtle_namespace(namespace):
    tot = ""
    for key in namespace:
        tot += "@prefix %s: <%s> .\n" % (key , namespace[key])
    return tot
        
if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Translate from MySQL to OWL.')
    parser.add_argument('--schema-out', help='Log file', default='schema.ttl')
    parser.add_argument('--instance-out', help='Log file', default='instance.nt')
    parser.add_argument('--db', help='Log file', default=config.DB)
    parser.add_argument('--user', help='DB User', default=config.USER)
    parser.add_argument('--passwd', help='DB passwd', default=config.PASSWORD)
    parser.add_argument('--host', help='DB host', default=config.HOST)
    global_params = vars(parser.parse_args())
    
    global_params['dbo'] = MySQLdb.connect(host=global_params['host'],
                                           user=global_params['user'],
                                           passwd=global_params['passwd'],  # your password
                                           db=global_params['db'],        # name of the data base
                                           charset='utf8')

    global_params['domain'] = 'http://dacura.org/ontology/%(db_name)s' % {'db_name' : global_params['db']}
    global_params['instance'] = 'http://dacura.org/instance/%(db_name)s' % {'db_name' : global_params['db']}
    global_params['domain_name'] = global_params['db']

    global_params['namespace'] = {'dacura' : 'http://dacura.scss.tcd.ie/ontology/dacura#',
                                  'owl' : 'http://www.w3.org/2002/07/owl#', 
                                  'rdf' : 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
                                  'rdfs' : 'http://www.w3.org/2000/01/rdf-schema#',
                                  'xsd' : 'http://www.w3.org/2001/XMLSchema#',
                                  global_params['domain_name'] : global_params['domain'] + '#'
    }
    #    global_params['preamble'] = ( "@prefix %(domain_name)s: <%(domain)s#> . " +
    global_params['preamble'] = render_turtle_namespace(global_params['namespace']
    ) % { 'domain_name' : global_params['domain_name'] , 'domain' : global_params['domain'] }

    name_table = {}
    tcd = constraints(name_table,global_params)
    doc = run_class_construction(tcd,global_params)
    schema = render_turtle(doc,global_params)
    
    with codecs.open(global_params['schema_out'], "w", encoding='utf8') as text_file:
        text_file.write(schema)

    triples = lift_instance_data(tcd,global_params)
    instance = render_triples(triples,global_params['namespace'])
    with codecs.open(global_params['instance_out'], "w", encoding='utf8') as text_file:
        text_file.write(instance)
