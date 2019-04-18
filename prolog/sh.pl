:- module(sh,[split/2,
              split/6,
              cat/2,
              end/0,
              pack/2,
              pack/4,
              cd/1,
              op(1150,xfx,>>),
              '>>'/2
             ]).

/* 

This module contains convenience functions for interaction with the shell.

*/

intersperse(_,[],[]).
intersperse(_,[X],[X]).
intersperse(Item,[X,Y|Rest],[X,Item|New_Rest]) :-
    intersperse(Item,[Y|Rest],New_Rest).

expand(Spec, Files) :-
    expand_file_name(Spec,Files).

cat(Spec,Stream) :-
    expand(Spec,Expanded),
    member(F,Expanded),
    open(F,read,Stream).

read_string_choices(Stream,Sep,Pad,String) :-
    (   read_string(Stream,Sep,Pad,End,Res),
        (   End = (-1)
        ->  String = Res
        ;   (   String = Res
            ;   read_string_choices(Stream,Sep,Pad,String)
            )
        )
    ).

record(Record_Separator,Stream,String) :-
    Pad_Chars = '',
    read_string_choices(Stream,Record_Separator,Pad_Chars,String).

record(Record_Separator,Pad_Chars,Stream,String) :-
    read_string_choices(Stream,Record_Separator,Pad_Chars,String).

fields(FS,String,Fields) :-
    Pad_Chars = '',
    split_string(String,FS,Pad_Chars,Fields).

fields(FS,Pad_Chars,String,Fields) :-
    split_string(String,FS,Pad_Chars,Fields).

split(Stream,Fields) :-
    record('\n','\r',Stream,String),
    fields(',',String,Fields).

split(RS,RPad,FS,FPad,Stream,Fields) :-
    record(RS,RPad,Stream,String),
    fields(FS,FPad,String,Fields).

select(N,Fields,Res) :-
    nth0(N,Fields,Res).

:- op(1150,xfx,>>).
'>>'(Pred,(Spec,Stream)) :-
    expand_file_name(Spec,Files),
    (   Files = [File]
    ->  open(File,write,Stream)
    ;   format(atom(M), '%w: ambiguous redirect', [Spec]),
        throw(error(M))
    ),
    writeq(Pred),
    !,
    (   call(Pred), fail
    ;   close(Stream)).

pack(RS,FS,Fields,Stream) :-
    intersperse(FS,Fields,Elts),
    forall(member(F,Elts),
           format(Stream, '~w', [F])),
    format(Stream, '~w', [RS]).

pack(Fields,Stream) :-
    pack('\n', ' , ', Fields, Stream).

cd(NewCWD) :-
    working_directory(_, NewCWD).

end :-
    fail.
