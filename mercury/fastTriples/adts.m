:- module adts.

:- interface.

:- import_module string, int, integer, bool.

:- type dateTime --->
     %    M   D   Y   H   M   S   Z
     dateTime(int,int,int,int,int,int,int).

:- type literal --->
     l_int(integer)
   ; l_string(string)
   ; l_dateTime(dateTime)
   ; l_boolean(bool)
   ; l_lang(string,string).

:- type triple --->
   o(string,string,string)
   ; l(string,string,literal).
