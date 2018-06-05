:- module(db, [add_triple/6]).

use_module(library(odbc)).

interpolate([],'').
interpolate([H|T],S) :-
    atom(H),
    interpolate(T,Rest),
    atom_concat(H,Rest,S) , !.
interpolate([H|T],S) :-
    string(H), atom_string(C,H),
    interpolate(T,Rest),
    atom_concat(C,Rest,S) , !.
interpolate([H|T],S) :- 
    ground(H), term_to_atom(H,C),
    interpolate(T,Rest) ,
    atom_concat(C,Rest,S) , !.

open_db(Connection) :-
    odbc_connect('rdf', Connection,
                 [ user(rdf),
                   password(rdf),
                   alias(rdf),
                   open(once)
                 ]).

uri_id(Connection,URI,ID) :-
	Q = 'SELECT uri,id FROM where uri = ? and id = ?',
	odbc_prepare(Connection,Q,[default,default],Statement),
	odbc_execute(Statement, [URI,ID], _Res).

add_triple(Connection,X,Y,Z,G,M) :-
	Q = 'INSERT INTO quads 
   	     SELECT a.id, b.id, c.id, g.id, ? FROM uris AS a, uris AS b, uris AS c, uris AS g	
      	 WHERE a.uri = ? and b.uri = ? and c.uri = ? and g.uri = ?',
	odbc_prepare(Connection,Q,[default,default,default,default,default],Statement),
	odbc_execute(Statement, [M,X,Y,Z,G], _Res).

triple(Connection,X,Y,Z,G,M) :-
	Q = 'SELECT a.uri, b.uri, c.uri, g.uri, q.mult 
         FROM uris AS a, uris AS b, uris AS c, uris AS g, quads AS q	
         WHERE a.id = q.obj AND b.id = q.pred AND c.id = q.sub AND g.id = q.graph
		       a.uri = ? AND b.uri = ? AND c.uri = ? AND g.uri = ?',
	odbc_prepare(Connection,Q,[default,default,default,default,default],Statement),
	odbc_execute(Statement, [X,Y,Z,G,M], _Res).
