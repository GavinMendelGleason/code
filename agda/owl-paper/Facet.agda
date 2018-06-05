
module Facet where

data Facet : Set where 
  length : Facet
  minLength : Facet 
  fpattern : Facet
  minInclusive : Facet
  maxInclusive : Facet
  minExclusive : Facet
  maxExclusive : Facet
  totalDigits : Facet 
  fractionDigits : Facet
