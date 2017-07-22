Database Transmutator
=====================

This programme translates a given MySQL database into a useable starting point for an OWL ontology. It produces a "triple assignment pragma" which enables the import of triples from the MySQL database into an OWL structured rdf triple store.

To see how use the program from the command line, you can type `./db.py --help`

~~~
usage: db.py [-h] [--schema-out SCHEMA_OUT] [--instance-out INSTANCE_OUT] [--db DB] [--user USER] [--passwd PASSWD] [--host HOST]

Translate from MySQL to OWL.

optional arguments:
  -h, --help            show this help message and exit
  --schema-out SCHEMA_OUT
                        Log file
  --instance-out INSTANCE_OUT
                        Log file
  --db DB               Log file
  --user USER           DB User
  --passwd PASSWD       DB passwd
  --host HOST           DB host
~~~

There is also a file, `config.py` which contains database information if that is more convenient. It will be overridden by command line switches if they are used. 

The default schema name is `schema.ttl` and is stored in turtle format. The default instance data is `instance.nt` and is stored in ntriple format. 
