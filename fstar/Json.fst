
module Json

open FStar.List
open FStar.String
open FStar.Int

type value = 
| I : int -> value
| S : string -> value

type dictionary 'a = 
| KV : string -> 'a -> dictionary
| KV : string -> value -> dictionary

type json = 
| Dict : dictionary json -> json
| List : list json -> json
