module RDFParser where

open import RDF hiding (⊤)

open import Coinduction
open import Data.Char as Char using (Char ; _==_ ; show)
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.String as String using (String ; _++_)
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import Data.Maybe
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Bool.Show renaming (show to show𝔹)

open Token Char Char._≟_

comment : Parser Char ⊤ _
comment =
  tok '#'                  >>= λ _ →
  sat′ (not ∘ ('\n' ==_)) ⋆ >>= λ _ →
  tok '\n'                 >>= λ _ →
  return tt

isnt : Char → Char → Maybe Char
isnt x y = if x == y then nothing else just y

isSpace : Char → Bool
isSpace c = (c == ' ') ∨ (c == '\t') ∨ (c == '\n') ∨ (c == '\r')

dataChar : Parser Char Char _
dataChar = sat (λ c → if isSpace c ∨ (c == '"') then nothing else just c)

pointChar : Parser Char Char _
pointChar = sat (isnt '>')

match : String → Parser Char ⊤ _
match str = matchAuxOne (String.toList str)
  where matchAux : Char → List Char → Parser Char ⊤ _
        matchAux x [] = tok x >>= λ _ → return tt
        matchAux x (y ∷ l) = tok x >>= λ _ → matchAux y l
        matchAuxOne : List Char → Parser Char ⊤ _
        matchAuxOne [] = fail
        matchAuxOne (x ∷ l) = matchAux x l

bool : Parser Char Bool _
bool = match "true" >>= λ _ → return true
     ∣ match "false" >>= λ _ → return false

integerType = match "xsd:integer"
            ∣ match "<http://www.w3.org/2001/XMLSchema#integer>"

boolType = match "xsd:boolean"
         ∣ match "<http://www.w3.org/2001/XMLSchema#boolean>"

stringType = match "xsd:string"
           ∣ match "<http://www.w3.org/2001/XMLSchema#string>"

typeMarker = match "^^"
langMarker = match "@"

dat = tok '"' >>= λ _ →
      dataChar + >>= λ ds →
      tok '"' >>= λ _ →
      return (String.fromList ds)

point = tok '<' >>= λ _ →
        pointChar + >>= λ ps →
        tok '>' >>= λ _ → 
        return (String.fromList ps)

literal = number >>= λ num →
          typeMarker >>= λ _ →
          integerType >>= λ _ → 
          return (n num)
        ∣ dat >>= λ d →
          typeMarker >>= λ _ →
          stringType >>= λ _ → 
          return (s d)
        ∣ bool >>= λ d →
          typeMarker >>= λ _ →
          boolType >>= λ _ → 
          return (b d)
        ∣ dat >>= λ d →
          langMarker >>= λ _ →
          dat >>= λ _ → 
          return (s d)

point∣lit = point >>= λ p → 
            return (inj₁ p)
          ∣ literal >>= λ l →
            return (inj₂ l)

triple : Parser Char (String × String × (String ⊎ D)) _
triple = whitespace ⋆ >>= λ _ →
         point >>= λ p₁ →
         whitespace ⋆ >>= λ _ →
         point >>= λ p₂ →
         whitespace ⋆ >>= λ _ →
         point∣lit >>= λ p₃ →
         whitespace ⋆ >>= λ _ →
         tok '.' >>= λ _ → 
         return (p₁ , p₂ , p₃)

end = match "END"

triples : Parser Char Transitions _
triples = triple + 

showTransitions : Transitions → String
showTransitions [] = ""
showTransitions ((proj₁ , proj₂ , inj₁ x) ∷ l) = "<" ++ proj₁ ++ "> <" ++ proj₂ ++ "> <" ++ x ++ "> .\n" ++
                                                  showTransitions l 
showTransitions ((proj₁ , proj₂ , inj₂ (n x)) ∷ l) = "<" ++ proj₁ ++ "> <" ++ proj₂ ++ "> \"" ++ showℕ x ++ "\"^^xsd:integer .\n" ++
                                                  showTransitions l 
showTransitions ((proj₁ , proj₂ , inj₂ (b x)) ∷ l) = "<" ++ proj₁ ++ "> <" ++ proj₂ ++ "> \"" ++ show𝔹 x ++ "\"^^xsd:boolean .\n" ++
                                                  showTransitions l 
showTransitions ((proj₁ , proj₂ , inj₂ (s x)) ∷ l) = "<" ++ proj₁ ++ "> <" ++ proj₂ ++ "> " ++ x ++ "@en .\n" ++
                                                  showTransitions l  -- 
