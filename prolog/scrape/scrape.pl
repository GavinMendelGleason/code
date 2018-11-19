:- module(scrape,[run_import/0, csv_to_json/2]).

:- use_module(library(http/http_cookie)).
:- use_module(library(xpath)).
:- use_module(library(pcre)).
:- use_module(library(http/json)).

extract_table(Results,Table) :-
    maplist( [DOM,Rows]>>(
                 extract_votes(DOM,Rows)
             ),Results, RowsSet),
    append(RowsSet,Table).

extract_votes(DOM,Rows) :-
    findall(row(VoteName,Description,Subject,Cllr,Party,Vote),
            select_vote(DOM,VoteName,Description,Subject,Cllr,Party,Vote),            
            Rows).

select_vote(DOM,Title,Description,Subject,Councillor,Party,Vote) :-
    %%format('~n~n~n~q~n~n~n',[DOM]), 
    xpath(DOM, //title(text), Title),
    %format('Title: ~q~n',[Title]), 
    xpath(DOM, //div(@class='text -body', text), Description),
    xpath(DOM, //meta(@name='keywords', @content=Subject), _),
    %format('Description: ~q~n',[Description]), 
    (   xpath(DOM, //div(@class='col-xs-4 box -delineated-h',
                         //div(@class='-for breakdown_item')), Section),
        %format('== Found Section === ~n',[]),
        xpath(Section, //div(@class='party-affiliated'), Councillor_Section),
        xpath(Councillor_Section, /self(text), Pre_Councillor),
        %format('Councillor: ~q~n',[Councillor]),                        
        xpath(Councillor_Section, //div(@class='party-icon', @title=Party), _),
        %format('Party: ~q~n',[Party]),
        Vote = for
    ;   xpath(DOM, //div(@class='col-xs-4 box -delineated-h',
                         //div(@class='-against breakdown_item')), Section),
        xpath(Section, //div(@class='party-affiliated'), Councillor_Section),
        xpath(Councillor_Section, /self(text), Pre_Councillor),
        xpath(Councillor_Section, //div(@class='party-icon', @title=Party), _),
        Vote = against
    ;   xpath(DOM, //div(@class='col-xs-4 box -delineated-h',
                         //div(@class='-abstain breakdown_item')), Section),
        xpath(Section, //div(@class='party-affiliated'), Councillor_Section),
        xpath(Councillor_Section, /self(text), Pre_Councillor),
        xpath(Councillor_Section, //div(@class='party-icon', @title=Party), _),
        Vote = abstain),
    re_replace('\240\\n', '', Pre_Councillor, Councillor).

save_csv_file(File,Header,Table) :-
   setup_call_cleanup(
       open(File, write, Out),
       (   csv_write_stream(Out, [Header], []),
           forall(member(Row,Table),
                  csv_write_stream(Out, [Row], []))
       ),
       close(Out)).


process_vote_files(Directory) :-

    directory_files(Directory,Files),
    
    maplist( {Directory}/[File,Path]>>(
                 atomics_to_string([Directory,'/',File],Path)
             ), Files, All_Paths),

    include(exists_file, All_Paths, Paths),
    
    maplist( [Path,Result]>>(
                 read_html_file(Path,Result)
             ), Paths, Results),

    extract_table(Results,Table),

    File = '/home/francoisbabeuf/Documents/workersparty/Votes.csv',
    save_csv_file(File,row('Name','Description','Councillor','Subject', 'Party','Vote'),Table).


read_html_file(File,DOM) :-
    
    dtd(html, DTD),
    open(File,read,In),
    
    load_structure(stream(In),
                   DOM,
                   [ dtd(DTD),
                     dialect(sgml),
                     shorttag(false),
                     max_errors(-1),
                     syntax_errors(quiet)
                   ]).

run_import :-
    Dir='/home/francoisbabeuf/Documents/workersparty/votes/www.counciltracker.ie/motions',
    process_vote_files(Dir).

/* 

csv_to_json('/home/francoisbabeuf/Documents/code/prolog/scrape/similarity.csv', 
            '/home/francoisbabeuf/Documents/code/javascript/votes/graph.js').
*/
csv_to_json(CSV_File,JSON_File) :-
    csv_read_file(CSV_File, [_Header|Rows], []),
    
    maplist( [row(Cllr_A,Cllr_B,Party_A,Party_B,Inv_Dist),JSON]>>(

                 Dist is (Inv_Dist) ** 2,
                 
                 JSON=json([source=Cllr_A, target=Cllr_B, value=Dist])

             ),
             Rows, JSON_Links),
    
    maplist( [row(Cllr_A,Cllr_B,Party_A,Party_B,Dist),JSON]>>(
                 JSON=json([id=Cllr_A,group=Party_A])
             ),
             Rows, JSON_Nodes_Dups),
    
    sort(JSON_Nodes_Dups, JSON_Nodes),
    
    setup_call_cleanup(
        open(JSON_File, write, Out),
        (   format(Out,'var graph = ', []),
            json_write(Out, json([nodes=JSON_Nodes, links=JSON_Links]))
        ),
        close(Out)).
/*
party_csv_to_json('/home/francoisbabeuf/Documents/code/prolog/scrape/party_similarity.csv', 
            '/home/francoisbabeuf/Documents/code/javascript/votes/graph.js').
*/
party_csv_to_json(CSV_File,JSON_File) :-
    csv_read_file(CSV_File, [_Header|Rows], []),
    
    maplist( [row(Party_A,Party_B,Inv_Dist),JSON]>>(

                 Dist is (Inv_Dist) ** 2,
                 
                 JSON=json([source=Party_A, target=Party_B, value=Dist])

             ),
             Rows, JSON_Links),
    
    maplist( [row(Party_A,Party_B,Dist),JSON]>>(
                 JSON=json([id=Party_A,group=Party_A])
             ),
             Rows, JSON_Nodes_Dups),
    
    sort(JSON_Nodes_Dups, JSON_Nodes),
    
    setup_call_cleanup(
        open(JSON_File, write, Out),
        (   format(Out,'var graph = ', []),
            json_write(Out, json([nodes=JSON_Nodes, links=JSON_Links]))
        ),
        close(Out)).


