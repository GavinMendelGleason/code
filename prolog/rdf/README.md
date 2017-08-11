# RDF in SQL

These files are meant to provide an RDF implementation in SQL which we
can bridge to SWI prolog's rdf/4 predicate.

The design has the following considerations: 

* Graph Structure 

We need to be able to conveniently represent multiple graphs, and be
able to combine graphs into single queries with minimal trouble.

* Performance 

We need a fast way of representing RDF in PSQL.

* Versioning

The tables represent triples in the store, with a versioning number to
take care of transactions. We represent the positive and negative
updates from the store in order to shadow the existing DB state in a
non-destructive fashion. After commit the DB prior state can be
journaled, and changes "garbage collected" to improve performance.

Currently versioning is linear, but it is possible to have
tree-structured versioning which will allow concurrent updates.
