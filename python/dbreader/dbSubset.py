#!/usr/bin/env python

import argparse
import logging
import os
import MySQLdb
import re
import config 
import codecs
import urllib
import datetime
import psycopg2
import psycopg2.extras

def get_dict_cursor(global_params):
    if global_params['variant'] == 'postgres':
        return global_params['dbo'].cursor(cursor_factory=psycopg2.extras.RealDictCursor)
    elif global_params['variant'] == 'mysql':
        return global_params['dbo'].cursor(MySQLdb.cursors.DictCursor)
    else:
        raise Exception("Unknown variant: %s" % global_params['variant'])

def do_connect(global_params):
    if global_params['variant'] == 'postgres':
        global_params['dbo'] = psycopg2.connect("host='%(host)s' dbname='%(db)s' user='%(user)s' password='%(passwd)s'" % global_params)
    elif global_params['variant'] == 'mysql':
        global_params['dbo'] = MySQLdb.connect(host=global_params['host'],
                                               user=global_params['user'],
                                               passwd=global_params['passwd'],  # your password
                                               db=global_params['db'],        # name of the data base
                                               charset='utf8')
    else:
        raise Exception("Unknown variant: %s" % global_params['variant'])        

    if global_params['variant_out'] == 'postgres':
        global_params['dbo_out'] = psycopg2.connect("host='%(host_out)s' dbname='%(db_out)s' user='%(user_out)s' password='%(passwd_out)s'" % global_params)

        cur = global_params['dbo_out'].cursor()
        
        version_stmt = """
SELECT COALESCE(MAX(u.version),0) lastver 
FROM (SELECT version FROM quads_pos 
      UNION SELECT version FROM quads_neg 
      UNION SELECT version FROM literals_pos
      UNION SELECT version FROM literals_neg
      UNION SELECT version FROM texts_pos
      UNION SELECT version FROM texts_neg
      UNION SELECT version FROM dates_pos
      UNION SELECT version FROM dates_neg
      UNION SELECT version FROM ints_pos
      UNION SELECT version FROM ints_neg) u
"""
        cur.execute(version_stmt)
        [version] = cur.fetchone()
        global_params['commit-version'] = version+1
        
        register_stmt = """PREPARE register_uri AS 
INSERT INTO uris (uri)
SELECT $1
WHERE NOT EXISTS (
	  SELECT uri FROM uris WHERE uri = $1
);
"""
        cur.execute(register_stmt)

        insert_stmt = """PREPARE insert_quad AS 
INSERT INTO quads_pos
SELECT a.id, b.id, c.id, g.id, $5
FROM uris a, uris b, uris c, uris g
WHERE a.uri = $1
AND b.uri = $2
AND c.uri = $3
AND g.uri = $4;
"""
        cur.execute(insert_stmt)

        insert_text_stmt = """PREPARE insert_text_quad AS 
INSERT INTO texts_pos
SELECT a.id, b.id, $3, g.id, $5
FROM uris a, uris b, uris g
WHERE a.uri = $1
AND b.uri = $2
AND g.uri = $4;
"""
        cur.execute(insert_text_stmt)

        insert_date_stmt = """PREPARE insert_date_quad AS 
INSERT INTO dates_pos
SELECT a.id, b.id, $3, g.id, $5
FROM uris a, uris b, uris g
WHERE a.uri = $1
AND b.uri = $2
AND g.uri = $4;
"""
        cur.execute(insert_date_stmt)

        insert_int_stmt = """PREPARE insert_int_quad AS 
INSERT INTO ints_pos
SELECT a.id, b.id, $3, g.id, $5
FROM uris a, uris b, uris g
WHERE a.uri = $1
AND b.uri = $2
AND g.uri = $4;
"""
        cur.execute(insert_int_stmt)

        insert_literal_stmt = """PREPARE insert_literal_quad AS 
INSERT INTO literals_pos
SELECT a.id, b.id, $3, g.id, $5
FROM uris a, uris b, uris g
WHERE a.uri = $1
AND b.uri = $2
AND g.uri = $4;
"""
        cur.execute(insert_literal_stmt)

    elif global_params['variant'] == 'mysql' and global_params['dbo_out']:
        global_params['dbo_out'] = MySQLdb.connect(host=global_params['host_out'],
                                                   user=global_params['user_out'],
                                                   passwd=global_params['passwd_out'],  # your password
                                                   db=global_params['db_out'],        # name of the data base
                                                   charset='utf8')
    else:
        raise Exception("Unknown variant: %s" % global_params['variant'])        



    
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
    stmt = None
    
    if global_params['variant'] == 'mysql':
        stmt = """
SELECT *
FROM INFORMATION_SCHEMA.KEY_COLUMN_USAGE
WHERE
REFERENCED_TABLE_SCHEMA = %(database)s AND REFERENCED_TABLE_NAME = %(table)s
    """
    elif global_params['variant'] == 'postgres':
        stmt = """
SELECT
    tc.table_name AS "TABLE_NAME", 
    kcu.column_name as "COLUMN_NAME",
    ccu.table_name AS "REFERENCED_TABLE_NAME",
    ccu.column_name AS "REFERENCED_COLUMN_NAME"
FROM
    information_schema.table_constraints AS tc
    JOIN information_schema.key_column_usage 
        AS kcu ON tc.constraint_name = kcu.constraint_name
    JOIN information_schema.constraint_column_usage 
        AS ccu ON ccu.constraint_name = tc.constraint_name
WHERE constraint_type = 'FOREIGN KEY'
AND kcu.table_name = %(table)s 
AND kcu.table_schema = %(database)s;
"""
    else:
        raise Exception("Unknown variant")

    cnstrs = {}
    for table in tables:
        cur = get_dict_cursor(global_params)
        cur.execute(stmt, {'database' : global_params['db'] , 'table' : table})
        for constraint in cur:
            if constraint['TABLE_NAME'] in cnstrs:
                cnstrs[constraint['TABLE_NAME']].append(constraint)
            else:
                cnstrs[constraint['TABLE_NAME']] = [constraint]

    return cnstrs

def table_columns(table,global_params):
    stmt = None
    if global_params['variant'] == 'mysql':        
        stmt = """
SHOW COLUMNS FROM %(table)s
    """ % {'table' : table}
    elif global_params['variant'] == 'postgres':
        # A bit of acrobatics to mimic the form and content of the mysql 'show columns' command.
        stmt = """
SELECT co.column_name AS "Field", 
       co.data_type AS "Type", 
       co.is_nullable AS "Null",
       (CASE tcu.constraint_type when 'PRIMARY KEY' THEN 'PRI' END) as "Key"
FROM information_schema.columns AS co
LEFT OUTER JOIN (SELECT cu.column_name, tc.constraint_name, tc.constraint_type
		 FROM information_schema.table_constraints AS tc,
		      information_schema.key_column_usage AS cu
                 WHERE tc.table_name = %(table)s
		 AND cu.constraint_name = tc.constraint_name)
		AS tcu 
             ON co.column_name = tcu.column_name 
WHERE co.table_name = %(table)s;
"""
    else:
        raise Exception("Unknown variant: %s" % global_params['variant'])
        
    cur = get_dict_cursor(global_params)
    cur.execute(stmt, {'table' : table})
    return cur.fetchall()

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

# Eventually this function has to do conversion between postgres and mysql
def convert_type(ty,params):
    return ty

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

def register_uri(uri,params):
    uri = expand(uri,params['namespace'])
    if params['variant'] == 'postgres' and params['dbo_out']:
        cur = global_params['dbo_out'].cursor()
        try:
            cur.execute("EXECUTE register_uri (%s)", (uri,))
        except Exception, e:
            logging.info("Failed to register the uri %s with %s" % (uri,str(e)))
            # Try to restart after a bit,
            # this probably has to go outside so we can re-obtain the cursor, but fuck it
            time.sleep(10)            
            do_connect(params)
    else:
        raise Exception("Only postgres variant works as yet, non-postgres variant specified")

def insert_quad(sub,pred,obj,graph,params):
    ns = params['namespace']
    sub = expand(sub,ns)
    pred = expand(pred,ns)
    obj = expand(obj,ns)
    graph = expand(graph,ns)
    # testing
    #logging.info(render_point(sub,'URI') + ' ' + render_point(pred,'URI') + ' ' + render_point(obj,'URI') + ' ' + render_point(graph,'URI') + ' .\n')
    #logging.info("Version: %s" % (params['commit-version'],))
    # print()
    if params['variant_out'] == 'postgres' and params['dbo_out']:
        cur = global_params['dbo_out'].cursor()
        try: 
            cur.execute("EXECUTE insert_quad (%s,%s,%s,%s,%s)", (sub,pred,obj,graph,params['commit-version']))
        except Exception, e:
            logging.info("Failed to write point:\n")
            logging.info(render_point(sub,'URI') + ' ' + render_point(pred,'URI') + ' ' + render_point(obj,'URI') + ' .\n')
    else:
        triple = render_point(sub,ns) + ' ' + render_point(pred,ns) + ' ' + render_point(obj,ns) + ' .\n'
        params['instance_handle'].write(triple)
            
def insert_typed_quad(sub,pred,val,ty,graph,params):
    ns = params['namespace']
    sub = expand(sub,ns)
    pred = expand(pred,ns)
    # testing
    xsdty = get_type_assignment(ty)
    xsdtyex = expand(xsdty,ns)
    #logging.info(render_point(sub,'URI') + ' ' + render_point(pred,'URI') + ' ' + render_point(val,ty) + ' ' + render_point(graph,'URI') + ' .\n')
    #logging.info("Version: %s" % (params['commit-version'],))

    if params['variant_out'] == 'postgres' and params['dbo_out']:
        cur = global_params['dbo_out'].cursor()
        try: 
            if re.search('int', ty):            
                cur.execute("EXECUTE insert_int_quad (%s,%s,%s,%s,%s)", (sub,pred,val,graph,params['commit-version']))
            elif re.search('varchar', ty):
                cur.execute("EXECUTE insert_text_quad (%s,%s,%s,%s,%s)", (sub,pred,val,graph,params['commit-version']))
            elif re.search('date',ty):
                cur.execute("EXECUTE insert_date_quad (%s,%s,%s,%s,%s)", (sub,pred,val,graph,params['commit-version']))
            elif re.search('timestamp',ty):
                cur.execute("EXECUTE insert_date_quad (%s,%s,%s,%s,%s)", (sub,pred,val,graph,params['commit-version']))
            elif re.search('text',ty):
                cur.execute("EXECUTE insert_text_quad (%s,%s,%s,%s,%s)", (sub,pred,val,graph,params['commit-version']))
            else:
                cur.execute("EXECUTE insert_literal_quad (%s,%s,%s,%s,%s)", (sub,pred,val,graph,params['commit-version']))
        except Exception, e:
            logging.info("Failed to write point:\n")
            xsdty = get_type_assignment(ty)
            xsdtyex = expand(xsdty,ns)
            logging.info(render_point(sub,'URI') + ' ' + render_point(pred,'URI') + ' ' + render_point(val,xsdtyex) + ' .\n')

    else:
        xsdty = get_type_assignment(ty)
        xsdtyex = expand(xsdty,ns)
        triple = render_point(sub,'URI') + ' ' + render_point(pred,'URI') + ' ' + render_point(val,xsdtyex) + ' .\n'
        params['instance_handle'].write(triple)

def register_object(table,columns,keys,row,swizzle_table,global_params):

    cache_misses = []
    uri = swizzle_table[table+str(row.values())]
    
    # Add the type information to triples
    class_uri = class_of(table,global_params)
    register_uri(class_uri,global_params)
    insert_quad(uri,'rdf:type',class_uri,global_params['instance'],global_params)
    if global_params['dbo_out']:
        global_params['dbo_out'].commit()        
    
    where = where_key(row)

    key_names = [d['Field'] for d in keys]
    keystring = ','.join(key_names)
    
    for c in columns:
        column_cursor = get_dict_cursor(global_params)

        column_stmt = """select %(column)s , %(keys)s from %(table)s where %(where)s
        """ % { 'keys' : keystring,
                'column' : c['Field'],
                'where' : where,
                'table' : table}

        column_cursor.execute(column_stmt)
        obj = column_cursor.fetchone()

        ###### \/\/ Object references ############################################
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

                        cursorprime = get_dict_cursor(global_params)
                        cursorprime.execute(keyed_value_stmt)
                        keyrow = cursorprime.fetchone()
                        if keyrow and cc['REFERENCED_TABLE_NAME']+str(keyrow.values()) in swizzle_table:
                            pred_uri = compose_name(cc,rcc, global_params)
                            obj_uri = swizzle_table[cc['REFERENCED_TABLE_NAME']+str(keyrow.values())]
                            register_uri(uri,global_params)
                            register_uri(pred_uri,global_params)
                            register_uri(obj_uri,global_params)
                            insert_quad(uri,pred_uri,obj_uri,global_params['instance'],global_params)
                            if global_params['dbo_out']:
                                global_params['dbo_out'].commit()
                        else:
                            miss = {'table' : cc['REFERENCED_TABLE_NAME'],
                                    'keyrow' : keyrow}
                            print("Cache miss: %s" % (miss,))
                            cache_misses.append(miss)

        ###### ^^^^ Object references ############################################

        ###### \/\/ Value reference ############################################
        # skip if null
        if obj[c['Field']]:
            pred_uri = column_name(table,c['Field'], global_params)
            val = obj[c['Field']]
            ty = convert_type(c['Type'],global_params)
            register_uri(uri,global_params)
            register_uri(pred_uri,global_params)          
            insert_typed_quad(uri,pred_uri,val,ty,global_params['instance'],global_params)
            if global_params['dbo_out']:
                global_params['dbo_out'].commit()        
        ###### ^^^^ Value reference ############################################

    if global_params['dbo_out']:
        global_params['dbo_out'].commit()        

    return cache_misses

def lift_instance_data(tcd, global_params):

    triples = []
    tables = get_tables(global_params)
    cursor = get_dict_cursor(global_params)

    swizzle_table = {}

    # put the graph name in the database
    register_uri(global_params['instance'],global_params)
    # also put rdf:type in the db
    register_uri('rdf:type',global_params)

    if global_params['fragment']:
        limit = " LIMIT 1000"
    else:
        limit = ""
    # Store information about ids which we didn't load
    cache_misses = []
    
    # Pass 1 to get swizzle table
    for table in tables:
        columns = table_columns(table, global_params)

        keys = primary_keys(columns)
        npk = non_primary_keys(columns)

        if (len(keys) == 0):
            keys = npk
        
        key_names = [d['Field'] for d in keys]
        keystring = ','.join(key_names)

        stmt = """select %(keys)s from %(table)s %(limit)s
        """ % { 'keys' : keystring,
                'table' : table,
                'limit' : limit }

        cursor.execute(stmt)
        for row in cursor:
            uri = genid(table, global_params)

            swizzle_table[table+str(row.values())] = uri

    cache_misses = []
    # Pass 2 to use swizzle table
    for table in tables:
        
        columns = table_columns(table, global_params)

        keys = primary_keys(columns)
        npk = non_primary_keys(columns)

        if (len(keys) == 0):
            keys = npk
        
        key_names = [d['Field'] for d in keys]
        keystring = ','.join(key_names)

        stmt = """select %(keys)s from %(table)s %(limit)s
        """ % { 'keys' : keystring,
                'table' : table,
                'limit' : limit }

        cursor.execute(stmt)
        print("Processing table: %s" % (table,))
        for row in cursor:
            missed = register_object(table,columns,keys,row,swizzle_table,global_params)
            cache_misses += missed

    # Final pass for cache misses
    # Actually requires that we achieve a fixed-point where no references are misses.
    while cache_misses != []:
        print "Processing cache misses..."
        
        new_cache_misses = []
        for elt in cache_misses:
            print elt
            print cache_misses
            table = elt['table']                    
            columns = table_columns(table, global_params)
            keys = primary_keys(columns)

            row = elt['keyrow']
            uri = genid(table, global_params)
            register_uri(uri,global_params)
            print row

            swizzle_table[table+str(row.values())] = uri
            missed = register_object(table,columns,keys,row,swizzle_table,global_params)
            new_cache_misses.append(missed)
            
        cache_misses = new_cache_misses
        
    if global_params['dbo_out']:
        global_params['dbo_out'].commit()        
        
    return True
            
def render_turtle(doc,args):
    tot = args['preamble']
    for s in doc:
        tot += s + '\n'
    return tot

def is_uri(obj):
    return re.match('^http(s?)://', obj)

def render_point(point, ty):
    if ty == 'URI':
        if point:
            point = "<" + point + ">"
        else:
            point = "<http://www.w3.org/2002/07/owl#Nothing>"
    else:
        point = '"%s"^^<%s>' % (point, ty)

    return point

def expand(point, ns):
    for key in ns:
        uri_base = ns[key]
        prefix = '^' + key + ':'
        if re.match(prefix, point):
            point = re.sub('^' + key + ':', uri_base, point)
            return point

    return point

def render_turtle_namespace(namespace):
    tot = ""
    for key in namespace:
        tot += "@prefix %s: <%s> .\n" % (key , namespace[key])
    return tot
        
if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Translate from MySQL or PostgreSQL to OWL.')
    parser.add_argument('--schema-out', help='Turtle file containing schema', default='schema.ttl')
    parser.add_argument('--instance-out', help='N-triple format output', default='instance.nt')
    parser.add_argument('--variant', help='Database variant (input)', default=config.VARIANT)
    parser.add_argument('--db', help='Log file', default=config.DB)
    parser.add_argument('--user', help='DB User', default=config.USER)
    parser.add_argument('--passwd', help='DB passwd', default=config.PASSWORD)
    parser.add_argument('--host', help='DB host', default=config.HOST)

    parser.add_argument('--variant-out', help='Database variant (output)', default=config.VARIANT_OUT)
    parser.add_argument('--db-out', help='', default=config.DB_OUT)
    parser.add_argument('--user-out', help='', default=config.USER_OUT)
    parser.add_argument('--passwd-out', help='', default=config.PASSWORD_OUT)
    parser.add_argument('--host-out', help='', default=config.HOST_OUT)
    parser.add_argument('--log', help='run logging', action='store_true')
    parser.add_argument('--log-file', help='Log location', default=config.LOG_PATH)
    parser.add_argument('--fragment', help='Log location', action='store_true')
    global_params = vars(parser.parse_args())

    # set up logging
    root = logging.getLogger()
    if root.handlers:
        for handler in root.handlers:
            root.removeHandler(handler)
    logging.basicConfig(filename=global_params['log_file'],level=logging.INFO,
                        format=config.LOG_FORMAT)

    logging.info('Starting transform')
    
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

    do_connect(global_params)
    
    tcd = constraints(name_table,global_params)

    doc = run_class_construction(tcd,global_params)

    schema = render_turtle(doc,global_params)
    
    if not global_params['db_out']:
        global_params['instance_handle'] = codecs.open(global_params['instance_out'], "w", encoding='utf8')
        
    lift_instance_data(tcd,global_params)
