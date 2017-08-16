DROP VIEW IF EXISTS quads CASCADE;

DROP TABLE IF EXISTS uris;
CREATE TABLE uris(
	uri text NOT NULL,
	id SERIAL PRIMARY KEY
);

CREATE UNIQUE INDEX uri_id ON uris (uri);

DROP TABLE IF EXISTS quads_pos;
-- Both a positive and negative graph required to do a sort of
-- 'painters algorithm' on quads.
CREATE TABLE quads_pos(
	sub int NOT NULL,
	pred int NOT NULL,
	obj int NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,obj,graph,version)
);

DROP TABLE IF EXISTS quads_neg;
CREATE TABLE quads_neg(
	sub int NOT NULL,
	pred int NOT NULL,
	obj int NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,obj,graph,version)
);

-- Bung everything not of a known subtype here. 
DROP TABLE IF EXISTS literals_pos;
CREATE TABLE literals_pos(
	sub int NOT NULL,
	pred int NOT NULL,
	val text NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,	
	PRIMARY KEY(sub,pred,val,graph,version)
); 

DROP TABLE IF EXISTS literals_neg;
CREATE TABLE literals_neg(
	sub int NOT NULL,
	pred int NOT NULL,
	val text NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,	
	PRIMARY KEY(sub,pred,val,graph,version)
); 

DROP TABLE IF EXISTS dates_pos;
-- Example with dates
CREATE TABLE dates_pos(
	sub int NOT NULL,
	pred int NOT NULL, 
	val timestamp NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,val,graph,version)
); 

DROP TABLE IF EXISTS dates_neg;
CREATE TABLE dates_neg(
	sub int NOT NULL,
	pred int NOT NULL, 
	val timestamp NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,val,graph,version)
); 

DROP TABLE IF EXISTS texts_pos;
CREATE TABLE texts_pos(
	sub int NOT NULL,
	pred int NOT NULL, 
	val text NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,val,graph,version)
);		

DROP TABLE IF EXISTS texts_neg;
CREATE TABLE texts_neg(
	sub int NOT NULL,
	pred int NOT NULL, 
	val text NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,val,graph,version)
);		

DROP TABLE IF EXISTS ints_pos;
CREATE TABLE ints_pos(
	sub int NOT NULL,
	pred int NOT NULL, 
	val int NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,val,graph,version)
);		

DROP TABLE IF EXISTS ints_neg;
CREATE TABLE ints_neg(
	sub int NOT NULL,
	pred int NOT NULL, 
	val int NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,val,graph,version)
);		

CREATE VIEW quads AS
SELECT maximum.sub, maximum.pred, maximum.obj, maximum.graph, MAX(maximum.version) lastver FROM
 (SELECT p.sub, p.pred, p.obj, p.graph, p.version
  FROM quads_pos p
  WHERE NOT EXISTS
  (SELECT n.sub, n.pred, n.obj, n.graph
   FROM quads_neg n
   WHERE n.sub = p.sub
   AND n.pred = p.pred
   AND n.obj = p.obj
   AND n.graph = p.graph
   AND n.version >= p.version)) AS maximum 
 GROUP BY maximum.sub, maximum.pred, maximum.obj, maximum.graph;

CREATE VIEW rdf_quad AS
SELECT a.uri sub, b.uri pred, c.uri obj, g.uri graph
FROM uris a, uris b, uris c, uris g, quads q
WHERE a.id = q.sub
AND b.id = q.pred
AND c.id = q.obj
AND g.id = q.graph;

