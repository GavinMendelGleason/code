DROP VIEW IF EXISTS uri_quads CASCADE;
DROP VIEW IF EXISTS date_quads CASCADE;
DROP VIEW IF EXISTS text_quads CASCADE;
DROP VIEW IF EXISTS int_quads CASCADE;
DROP VIEW IF EXISTS literal_quads CASCADE;
DROP VIEW IF EXISTS rdf_quad CASCADE;

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
    lang varchar(7) NOT NULL,	
	graph int NOT NULL,
	version int NOT NULL,
	PRIMARY KEY(sub,pred,val,graph,version)
);		

DROP TABLE IF EXISTS texts_neg;
CREATE TABLE texts_neg(
	sub int NOT NULL,
	pred int NOT NULL, 
	val text NOT NULL,
	lang varchar(7) NOT NULL,	
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

CREATE VIEW uri_quads AS
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

CREATE VIEW text_quads AS
SELECT maximum.sub, maximum.pred, maximum.val, maximum.lang, maximum.graph, MAX(maximum.version) lastver FROM
 (SELECT p.sub, p.pred, p.val, p.lang, p.graph, p.version
  FROM texts_pos p
  WHERE NOT EXISTS
  (SELECT n.sub, n.pred, n.val, p.lang, n.graph
   FROM texts_neg n
   WHERE n.sub = p.sub
   AND n.pred = p.pred
   AND n.val = p.val
   AND n.lang = p.lang
   AND n.graph = p.graph
   AND n.version >= p.version)) AS maximum 
 GROUP BY maximum.sub, maximum.pred, maximum.val, maximum.lang, maximum.graph;

CREATE VIEW int_quads AS
SELECT maximum.sub, maximum.pred, maximum.val, maximum.graph, MAX(maximum.version) lastver FROM
 (SELECT p.sub, p.pred, p.val, p.graph, p.version
  FROM ints_pos p
  WHERE NOT EXISTS
  (SELECT n.sub, n.pred, n.val, n.graph
   FROM ints_neg n
   WHERE n.sub = p.sub
   AND n.pred = p.pred
   AND n.val = p.val
   AND n.graph = p.graph
   AND n.version >= p.version)) AS maximum 
 GROUP BY maximum.sub, maximum.pred, maximum.val, maximum.graph;

CREATE VIEW date_quads AS
SELECT maximum.sub, maximum.pred, maximum.val, maximum.graph, MAX(maximum.version) lastver FROM
 (SELECT p.sub, p.pred, p.val, p.graph, p.version
  FROM dates_pos p
  WHERE NOT EXISTS
  (SELECT n.sub, n.pred, n.val, n.graph
   FROM dates_neg n
   WHERE n.sub = p.sub
   AND n.pred = p.pred
   AND n.val = p.val
   AND n.graph = p.graph
   AND n.version >= p.version)) AS maximum 
 GROUP BY maximum.sub, maximum.pred, maximum.val, maximum.graph;

CREATE VIEW literal_quads AS
SELECT maximum.sub, maximum.pred, maximum.val, maximum.graph, MAX(maximum.version) lastver FROM
 (SELECT p.sub, p.pred, p.val, p.graph, p.version
  FROM literals_pos p
  WHERE NOT EXISTS
  (SELECT n.sub, n.pred, n.val, n.graph
   FROM literals_neg n
   WHERE n.sub = p.sub
   AND n.pred = p.pred
   AND n.val = p.val
   AND n.graph = p.graph
   AND n.version >= p.version)) AS maximum 
 GROUP BY maximum.sub, maximum.pred, maximum.val, maximum.graph;

CREATE VIEW rdf_quad AS
SELECT a.uri sub, b.uri pred, c.uri obj, g.uri graph
FROM uris a, uris b, uris c, uris g, uri_quads q
WHERE a.id = q.sub
AND b.id = q.pred
AND c.id = q.obj
AND g.id = q.graph;

CREATE OR REPLACE FUNCTION last_version()
RETURNS integer AS
$block$
    DECLARE
	version integer;  
	BEGIN
		SELECT COALESCE(MAX(u.version),0) lastver INTO STRICT version
		 FROM (SELECT qp.version FROM quads_pos as qp
      	 UNION SELECT qn.version FROM quads_neg as qn
      	 UNION SELECT lp.version FROM literals_pos as lp
      	 UNION SELECT ln.version FROM literals_neg as ln
      	 UNION SELECT tp.version FROM texts_pos as tp
      	 UNION SELECT tn.version FROM texts_neg as tn
      	 UNION SELECT dp.version FROM dates_pos as dp
      	 UNION SELECT dn.version FROM dates_neg as dn
      	 UNION SELECT ip.version FROM ints_pos as ip
      	 UNION SELECT intn.version FROM ints_neg as intn) u;
		RETURN version;
	END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_uri(u text)
RETURNS void AS
$block$
	BEGIN
		INSERT INTO uris (uri)
		SELECT u WHERE NOT EXISTS (SELECT uri FROM uris WHERE uri = u);
	END;
$block$	LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION insert_quad(a text, b text, c text, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		PERFORM register_uri(a), register_uri(b), register_uri(c), register_uri(g); 
		INSERT INTO quads_pos
		SELECT ua.id, ub.id, uc.id, ug.id, v
		FROM uris ua, uris ub, uris uc, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND uc.uri = c
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION insert_text_quad(a text, b text, c text, l varchar(7), g text, v integer)
RETURNS void AS
$block$
	BEGIN
		PERFORM register_uri(a), register_uri(b), register_uri(g);
		INSERT INTO texts_pos
		SELECT ua.id, ub.id, c, l, ug.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION insert_int_quad(a text, b text, c integer, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		PERFORM register_uri(a), register_uri(b), register_uri(g);
		INSERT INTO ints_pos
		SELECT ua.id, ub.id, c, ug.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION insert_date_quad(a text, b text, c timestamp, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		PERFORM register_uri(a), register_uri(b), register_uri(g);
		INSERT INTO dates_pos
		SELECT ua.id, ub.id, c, ug.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION insert_literal_quad(a text, b text, c text, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		PERFORM register_uri(a), register_uri(b), register_uri(g);
		INSERT INTO literals_pos
		SELECT ua.id, ub.id, c, ug.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION delete_quad(a text, b text, c text, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		INSERT INTO quads_neg
		SELECT ua.id, ub.id, uc.id, ug.id, v
		FROM uris ua, uris ub, uris uc, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND uc.uri = c
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION delete_text_quad(a text, b text, c text, l varchar(7), g text, v integer)
RETURNS void AS
$block$
	BEGIN
		INSERT INTO texts_neg
		SELECT ua.id, ub.id, c, l, ug.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION delete_int_quad(a text, b text, c integer, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		INSERT INTO ints_neg
		SELECT ua.id, ub.id, c, ug.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION delete_date_quad(a text, b text, c timestamp, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		INSERT INTO dates_neg
		SELECT a.id, b.id, c, g.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION delete_literal_quad(a text, b text, c text, g text, v integer)
RETURNS void AS
$block$
	BEGIN
		INSERT INTO literals_neg
		SELECT ua.id, ub.id, uc, ug.id, v
		FROM uris ua, uris ub, uris ug
		WHERE ua.uri = a
		AND ub.uri = b
		AND ug.uri = g;
    END;
$block$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION delete_transaction(graph text, version integer)
RETURNS void AS
$block$
	BEGIN
		DELETE FROM quads_pos as qp WHERE qp.version=version AND qp.graph=graph;
		DELETE FROM quads_neg as qn WHERE qn.version=version AND qn.graph=graph;
		DELETE FROM literals_pos as lp WHERE lp.version=version AND lp.graph=graph;
		DELETE FROM literals_neg as ln WHERE ln.version=version AND ln.graph=graph;
		DELETE FROM texts_pos as tp WHERE tp.version=version AND tp.graph=graph;
		DELETE FROM texts_neg as tn WHERE tn.version=version AND tn.graph=graph;
		DELETE FROM dates_pos as dp WHERE dp.version=version AND dp.graph=graph;
		DELETE FROM dates_neg as dn WHERE dn.version=version AND dn.graph=graph;
		DELETE FROM ints_pos as ip WHERE ip.version=version AND ip.graph=graph;
		DELETE FROM ints_neg as intsn WHERE intsn.version=version AND intsn.graph=graph;
	END; 
$block$ LANGUAGE plpgsql;





