  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# x₁ y#a) (bindx≈yα {_} {y₁} x₂ x₃ a≈b) | yes refl | no ¬p with eq y₁ x
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {_} {a} x₁ y#a) (bindx≈yα {_} {.x} x₂ x₃ a≈b) | yes refl | no ¬p | yes refl
    rewrite eq-yes y refl | ⟨↔⟩-invol y x a with ⟨ x ↔ y₁ ⟩ₐ y | lemma↔ₐ x y₁ y | ⟨ x ↔ y₁ ⟩ₐ y₁ | lemma↔ₐ x y₁ y₁
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {_} {a} x₁ y#a) (bindx≈yα {_} {.x} x₂ x₃ a≈b) | yes refl | no ¬p | yes refl | e | res₁ | f | res₂ = ?
  ⟨x↔y⟩a≈αb⇒x#b x y _ _ x≢y (x·y# {_} {_} {a} x₁ y#a) (bindx≈yα {_} {y₁} x₂ x₃ a≈b) | yes refl | no ¬p | no ¬p₁
    rewrite eq-yes y refl with ⟨↔⟩-dist x y₁ y y₁ a = {!!}



			$fail_setting = $srvr->getServiceSetting("fail_on_ontology_hijack", false);
            $fail_on_ontology_hijack = $srvr->getServiceSetting("fail_on_ontology_hijack", false) == "false" ? false : $fail_setting;
            if(count($violations) > 0 && $fail_on_ontology_hijack){





I'd be very keen on discussing these 4 - and indeed what would constitute a sufficient basis of pre-requisites for understanding the differences between them. 

*Warning random opining follows*

"Real world" programming is currently a long way from use of dependent types, and as someone who has spent a fair bit of time programming in industry, I view this as a bad thing.  So many problems that I encountered could have been solved once and for all by types (SQL injection attacks spring to mind, but also a host of other safety issues)  However, there are good reasons for not employing languages of dependent types, and that's that the costs (largely in human labour) of using them are simply too high at present.  I'd like to see type theory tools deployed in such a way that this is no longer the case.

While I'm interested in the mathematical foundations, and I think it's often the case that mathematical elegance has its own utility even in practice, I lean more towards the programming praxis angle.

I'd be curious to see where dependent types have been deployed in practice already, but also imagining how they might be feasibly deployed and what sort of tool-chain would be necessary to make this a reality.

One thing that particularly impressed me of late was F-star. While It's a bit irritating that you don't get to interact with the theorem prover directly and have to attempt to coax it in the right direction, it does have a lot of the things that I think will prove essential for broadening the appeal and deployment.  For instance, a graded hierarchy from quick and dirty imperative, right up to pure functional -  and all made visible in the type system.  

And while I'm in the rhythm of ranting, I'll go ahead and wager that the following will prove important:

1. You can start with something akin to one of these modern lisp like languages (garbage collected, dynamically typed but with effects, ala python / javascript) or perhaps something of the ML family (garbage collected, statically typed but with effects ala F#) and "turn up" the type checking for regions of the code that you want to lock down, right up to the point that you have a full dependent type system at your disposal. 

I think this will turn out to be important because for large amounts of code, the specification is not actually known yet and will only be found as it is explored, the code changes too fast for a very careful typing discipline to be desirable and because sometimes correctness just matters less than getting the damn thing limping.

Maybe we really can just go full fledged with "pure" functional programs but I'm a bit skeptical that using monad transformers should be necessary to add a debugging print statement when using exceptions. If it goes this route I think it's going to have to force the user to pay less for the price of admission.

2. That you have facilities for automating the boring parts of the proof (at the very least). 

I just spent some wicked stupid amount of time doing an obviously banal and decidable proof in Agda by hand - I started using reflection and writing a prover and gave up proving the prover produced the appropriate type after wasting 4 hours when the program to write the program started exceeding the size and time of the boring proof. This should have been 10 minutes max playing with some tactic language.

3. Proof of concept. 

The system should be developed with an actual deployment in mind.  This can help to hone the approach under the stress of practice.  It's often very hard to choose from among a number of potentially beautiful approaches without the guide of necessity.
