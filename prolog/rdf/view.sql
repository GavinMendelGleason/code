-- This file provides the view on the DB from which we see the current quads

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

-- Example query for uri insert - all uris have to be registered prior to use in inserts
INSERT INTO uris (uri)
SELECT 'sub'
WHERE NOT EXISTS (
	  SELECT uri FROM uris WHERE uri = 'sub'
);

INSERT INTO uris (uri)
SELECT 'pred'
WHERE NOT EXISTS (
	  SELECT uri FROM uris WHERE uri = 'pred'
);

INSERT INTO uris (uri)
SELECT 'obj'
WHERE NOT EXISTS (
	  SELECT uri FROM uris WHERE uri = 'obj'
);

INSERT INTO uris (uri)
SELECT 'obj2'
WHERE NOT EXISTS (
	  SELECT uri FROM uris WHERE uri = 'obj2'
);

INSERT INTO uris (uri)
SELECT 'graph'
WHERE NOT EXISTS (
	  SELECT uri FROM uris WHERE uri = 'graph'
);

-- An insert example
INSERT INTO quads_pos
SELECT a.id, b.id, c.id, g.id, v.lastver+1
FROM uris a, uris b, uris c, uris g, (SELECT COALESCE(MAX(u.version),0) lastver FROM (select * from quads_pos UNION select * from  quads_neg) as u) v
WHERE a.uri = 'sub'
AND b.uri = 'pred'
AND c.uri = 'obj'
AND g.uri = 'graph';

-- A faux delete example
INSERT INTO quads_neg
SELECT a.id, b.id, c.id, g.id, v.lastver+1
FROM uris a, uris b, uris c, uris g, (SELECT COALESCE(MAX(version),0) lastver FROM quads_pos UNION quads_neg) v
WHERE a.uri = 'sub'
AND b.uri = 'pred'
AND c.uri = 'obj'
AND g.uri = 'graph';

