#!/usr/bin/env python

import psycopg2
import psycopg2.extras

def get_tables(global_params):
    cur = global_params['dbo'].cursor()

    stmt = """
SELECT TABLE_NAME FROM INFORMATION_SCHEMA.TABLES
WHERE TABLE_TYPE = 'BASE TABLE' AND TABLE_SCHEMA=%(database)s
    """
    cur.execute(stmt, {'database' : config.DB})
    
    tables = [ table for (table,) in cur.fetchall() ]
    
    return tables


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Delete all instance data.')
    parser.add_argument('--variant', help='Database variant', default=config.VARIANT)
    parser.add_argument('--db', help='Log file', default=config.DB)
    parser.add_argument('--user', help='DB User', default=config.USER)
    parser.add_argument('--passwd', help='DB passwd', default=config.PASSWORD)
    parser.add_argument('--host', help='DB host', default=config.HOST)
    global_params = vars(parser.parse_args())

    do_connect(global_params)

    for table in get_tables(global_params):
        stmt = "delete from %{table}s"
        cur = global_params['dbo'].cursor()
        cur.execute(stmt, {'table' : table})
