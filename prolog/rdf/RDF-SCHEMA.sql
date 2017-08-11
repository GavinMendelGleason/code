
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

DROP TABLE IF EXISTS literal_pos;
-- Bung everything not of a known subtype here. 
CREATE TABLE literal_pos(
	sub int NOT NULL,
	pred int NOT NULL,
	val binary NOT NULL,
	graph int NOT NULL,
	version int NOT NULL,	
	PRIMARY KEY(sub,pred,val,graph,version)
); 

DROP TABLE IF EXISTS literal_neg;
CREATE TABLE literal_neg(
	sub int NOT NULL,
	pred int NOT NULL,
	val binary NOT NULL,
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
-- Example with text
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
