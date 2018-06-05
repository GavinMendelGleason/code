
module Example where

open import IO
open import Coinduction
open import RDF
open import Data.Product
open import Data.List
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Properties
open import Data.Sum
open import Data.List
open import RDFParser
open import TotalParserCombinators.BreadthFirst using (parse)
open import Data.String
open import Data.Maybe
open import Function

tryparse : String → Transitions
tryparse str with parse triples (toList str)
...          | [] = []
...          | (h ∷ t) = h

main = run (♯ readFiniteFile "output.ntp" >>= λ s → 
            let mdb = tryparse s
            in ♯ putStrLn (showTransitions mdb))


Polity : Shape
Polity = ν "Pol" ((ℓ[ "name" ] Str) ⊗
                  (ℓ⟨ "population" ⟩ Natural) ⊗
                  ((α⟨ "neighbouringPolity" ⟩ (v "Pol")) has 1))

Thing : Shape
Thing = (ℓ⟨ "thingy" ⟩ Str)

DB : Transitions
DB = ("seshat:Rome" , "neighbouringPolity" , inj₁ "seshat:Carthage") ∷ 
     ("seshat:Rome" , "name" , inj₂ (s "Rome")) ∷
     ("seshat:Rome" , "population" , inj₂ (n 400000)) ∷ 
     ("seshat:Carthage" , "neighbouringPolity" , inj₁ "seshat:Rome") ∷ 
     ("seshat:Carthage" , "name" , inj₂ (s "Carthage")) ∷
     ("seshat:Carthage" , "population" , inj₂ (n 300000)) ∷ []

checkRome : Bool
checkRome with checkφ DB "seshat:Rome" Polity
checkRome | yes p = true
checkRome | no ¬p = false

checkCarthage : Bool
checkCarthage with checkφ DB "seshat:Carthage" Polity
checkCarthage | yes p = true
checkCarthage | no ¬p = false

open import Relation.Nullary.Decidable
open import Data.String renaming (_≟_ to eqString) hiding (_++_)

main = run (♯ (putStrLn "Checking to see if Rome is a polity") >>
            ♯ (if checkRome
               then putStrLn "Rome is a Polity!"
               else putStrLn "No elements of this formula exist") >>
            ♯ (if checkCarthage
               then putStrLn "Carthage is a Polity!"
               else putStrLn "No elements of this formula exist"))
