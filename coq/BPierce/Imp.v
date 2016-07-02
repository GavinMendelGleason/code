(** * Imp: Simple Imperative Programs *)
(* Version of 4/21/2010 *)





(** In this chapter, we begin a new direction that we'll continue for
    the rest of the course: whereas up to now we've been mostly
    studying Coq itself, from now on we'll mostly be using Coq to
    formalize other things.

    Our first case study is a _simple imperative programming language_
    called Imp.  This chapter looks at how to define the _syntax_ and
    _semantics_ of Imp; the chapters that follow will develop a theory
    of _program equivalence_ and introduce _Hoare Logic_, the best
    known logic for reasoning about imperative programs. *)

(* ####################################################### *)
(** *** Sflib *)

(** A minor technical point: Instead of asking Coq to import our
    earlier definitions from Logic.v, we import a small library called
    Sflib.v, containing just a few definitions and theorems from
    earlier chapters that we'll actually use in the rest of the
    course.  You won't notice much difference, since most of what's
    missing from Sflib has identical definitions in the Coq standard
    library.  The main reason for doing this is to tidy the global Coq
    environment so that, for example, it is easier to search for
    relevant theorems. *)

Require Export SfLib.

(* ####################################################### *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

Module AExp.

(* ####################################################### *)
(** ** Syntax *)

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  

    The file ImpParser.v develops a simple implementation of a lexical
    analyzer and parser that can perform this translation.  You do
    _not_ need to understand that file to understand this one, but if
    you haven't taken a course where these techniques are
    covered (e.g., a compilers course) you may enjoy skimming it. *)

(* ####################################################### *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression reduces it to a single number. *)

Fixpoint aeval (e : aexp) : nat :=
  match e with
  | ANum n => n
  | APlus a1 a2 => plus (aeval a1) (aeval a2)
  | AMinus a1 a2  => minus (aeval a1) (aeval a2)
  | AMult a1 a2 => mult (aeval a1) (aeval a2)
  end.

Example test_aeval1: 
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (e : bexp) : bool :=
  match e with 
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ####################################################### *)
(** ** Optimization *)

(** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (e:aexp) : aexp := 
  match e with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus: 
  optimize_0plus (APlus (ANum 2) 
                        (APlus (ANum 0) 
                               (APlus (ANum 0) (ANum 1)))) =
  APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)

Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHe2. 
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMinus".  
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.  Qed.


(* ####################################################### *)
(** * Coq Automation *)

(** The repetition in this last proof is starting to be a little
    annoying.  It's still just about bearable, but if either the
    language of arithmetic expressions or the optimization being
    proved sound were significantly more complex, it would begin to be
    a real problem.
 
    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its very powerful
    facilities for constructing proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some energy
    -- Coq's automation is a power tool -- but it will allow us to
    scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, or low-level details. *)

(* ####################################################### *)
(** ** Tacticals *)

(** _Tactical_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ####################################################### *)
(** *** The [try] Tactical *)

(** One very simple tactical is [try]: If [T] is a tactic, then [try
    T] is a tactic that is just like [T] except that, if [T] fails,
    [try T] does nothing at all (instead of failing). *)

(* ####################################################### *)
(** *** The [;] Tactical *)

(** Another very basic tactical is written [;].  If [T], [T1], ...,
    [Tn] are tactics, then
[[
      T; [T1 | T2 | ... | Tn] 
]]
   is a tactic that first performs [T] and then performs [T1] on the
   first subgoal generated by [T], performs [T2] on the second
   subgoal, etc.

   In the special case where all of the [Ti]'s are the same tactic
   [T'], we can just write [T;T'] instead of:
[[
      T; [T' | T' | ... | T'] 
]]
   That is, if [T] and [T'] are tactics, then [T;T'] is a tactic that
   first performs [T] and then performs [T'] on _each subgoal_
   generated by [T].  This is the form of [;] that is used most often
   in practice. *)

(** For example, consider the following trivial lemma: *)

Lemma foo : forall n, ble_nat 0 n = true. 
Proof. 
  intros.
  destruct n. 
    (* Leaves two subgoals...  *) 
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
    (* ... which are discharged similarly *)
Qed.

(** We can simplify the proof above using the [;] tactical. *)

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros. 
  (* Apply [destruct] to the current goal *)
  destruct n; 
  (* then apply [simpl] to each resulting subgoal *)
  simpl;
  (* then apply [reflexivity] to each resulting subgoal *)
  reflexivity.
Qed.
 
(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e; 
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
  Case "ANum". reflexivity.
  Case "APlus". 
    destruct e1; 
      (* Most cases follow directly by the IH *)
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    (* The interesting case, on which the above fails, is when e1 =
       ANum n. In this case, we have to destruct n (to see whether the
       optimization applies) and rewrite with the inductive
       hypothesis. *)
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity.   Qed.

(** In practice, Coq experts often use [try] with a tactic like
    [induction] to take care of many similar "straightforward" cases
    all at once.  Naturally, this practice has an analog in informal
    proofs. *)
(** Here is an informal proof of this theorem that
    matches the structure of the formal one:
    
    _Theorem_: For all arithmetic expressions [e],
[[
       aeval (optimize_0plus e) = aeval e.
]]
    _Proof_: By induction on [e].  The [AMinus] and [AMult] cases
    follow directly from the IH.  The remaining cases are as follows:

      - Suppose [e = ANum n] for some [n].  We must show 
[[
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
]]
        This is immediate from the definition of [optimize_0plus].
    
      - Suppose [e = APlus e1 e2] for some [e1] and [e2].  We
        must show
[[
          aeval (optimize_0plus (APlus e1 e2)) 
        = aeval (APlus e1 e2).
]]
        Consider the possible forms of [e1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [e1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [e1 = ANum n] for some [n].
        If [n = ANum 0], then
[[
          optimize_0plus (APlus e1 e2) = optimize_0plus e2
]]
        and the IH for [e2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)
    
(** This proof can still be improved: the first case (for [e = ANum
    n]) is very trivial -- even more trivial than the cases that we
    said simply followed from the IH -- yet we have chosen to write it
    out in full.  It would be better and clearer to drop it and just
    say, at the top, "Most cases are either immediate or direct from
    the IH.  The only interesting case is the one for [APlus]..."  We
    can make the same improvement in our formal proof too.  Here's how
    it looks: *)

Theorem optimize_0plus_sound'': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. 
  induction e; 
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when e = APlus e1 e2. *)
  Case "APlus". 
    destruct e1; 
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity.  Qed.


(* ####################################################### *)
(** ** Defining New Tactic Notations *)

(** Coq also provides several ways of "programming" tactic scripts. 

      - The [Tactic Notation] command gives a handy way to define
        "shorthand tactics" that, when invoked, apply several tactics
        at the same time.

      - For more sophisticated programming, Coq offers a small
        built-in programming language called [Ltac] with primitives
        that can examine and modify the proof state.  The details are
        a bit too complicated to get into here (and it is generally
        agreed that [Ltac] is not the most beautiful part of Coq's
        design!), but they can be found in the reference manual, and
        there are many examples of [Ltac] definitions in the Coq
        standard library that you can use as examples.

      - There is also an OCaml API that can be used to build new
        tactics that access Coq's internal structures at a lower
        level, but this is seldom worth the trouble for ordinary Coq
        users. 

The [Tactic Notation] mechanism is the easiest to come to grips with,
and it offers plenty of power for many purposes.  Here's an example. 
*)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** This defines a new tactical called [simpl_and_try] which
    takes one tactic [c] as an argument, and is defined to be
    equivalent to the tactic [simpl; try c].  For example, writing
    "[simpl_and_try reflexivity.]" in a proof would be the same as
    writing "[simpl; try reflexivity.]" *)

(** The next subsection gives a more sophisticated use of this
    feature... *)

(* ####################################################### *)
(** *** Bulletproofing Case Analyses *)

(** Being able to deal with most of the cases of an [induction] or
    [destruct] all at the same time is very convenient, but it can
    also be a little confusing.  One problem that often comes up is
    that _maintaining_ proofs written in this style can be difficult.
    For example, suppose that, later, we extended the definition of
    [aexp] with another constructor that also required a special
    argument.  The above proof might break because Coq generated the
    subgoals for this constructor before the one for [APlus], so that,
    at the point when we start working on the [APlus] case, Coq is
    actually expecting the argument for a completely different
    constructor.  What we'd like is to get a sensible error message
    saying "I was expecting the [AFoo] case at this point, but the
    proof script is talking about [APlus]."  Here's a nice little
    trick that smoothly achieves this. *)

Tactic Notation "aexp_cases" tactic(first) tactic(c) :=
  first;
  [ c "ANum" | c "APlus" | c "AMinus" | c "AMult" ].

(** For example, if [e] is a variable of type [aexp], then doing
[[
      aexp_cases (induction e) Case
]]
    will perform an induction on [e] (the same as if we had just typed
    [induction e]) and _also_ add a [Case] tag to each subgoal
    generated by the [induction], labeling which constructor it comes
    from.  For example, here is yet another proof of
    optimize_0plus_sound, using [aexp_cases]: *)

Theorem optimize_0plus_sound''': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  (* Note that we must put the entire [aexp_cases] expression in
     parentheses when following it by a semicolon! *)
  (aexp_cases (induction e) Case); 
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.

  (* At this point, there is already an ["APlus"] case name in the
     context.  The [Case "APlus"] here in the proof text has the
     effect of a sanity check: if the "Case" string in the context is
     anything _other_ than ["APlus"] (for example, because we added a
     clause to the definition of [aexp] and forgot to change the
     proof) we'll get a helpful error at this point telling us that
     this is now the wrong case. *)
  Case "APlus". 
    (aexp_cases (destruct e1) SCase); 
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHe2; reflexivity.  Qed.

(** **** Exercise: 3 stars (optimize_0plus_b) *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, optional (optimizer) *)
(** DESIGN EXERCISE: The optimization implemented by our
    [optimize_0plus] function is only one of many imaginable
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.

(* FILL IN HERE *)
*)
(** [] *)

End AExp.

(* ####################################################### *)
(** ** The [omega] Tactic *)

(** The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic), 

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. 
 *)

Example silly_presburger_formula : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega. 
Qed.

(** Andrew Appel calls this the "Santa Claus tactic." *)

(* ####################################################### *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave just like
       [apply H].

    We'll see many examples of these in the proofs below. *)


(* ####################################################### *)
(** * Expressions With Variables *)

(** Now let's turn our attention back to defining Imp.  The next thing
    we need to do is to enrich our arithmetic and boolean expressions
    with variables. *)

(* ##################################################### *)
(** ** Identifiers *)

(** In the rest of the course, we'll often need to talk about
    "identifiers," such as program variables.  We could use strings
    for this, or (as in a real compiler) some kind of fancier
    structures like symbols from a symbol table.  But for simplicity
    let's just use natural numbers as identifiers.  

    We define a new inductive datatype [Id] so that we won't
    confuse identifiers and numbers. *)

Inductive id : Type := 
  Id : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

(** Now, having "wrapped" numbers as identifiers in this way, it is
    convenient to recapitulate a few properties of numbers as
    analogous properties of identifiers, so that we can work with
    identifiers in definitions and proofs abstractly, without
    unwrapping them to expose the underlying numbers.  Since all we
    need to know about identifiers is whether they are the same or
    different, just a few basic facts are all we need. *)

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl.  Qed.

(** **** Exercise: 1 star, optional *)
(** For this and the following exercises, do not prove by induction,
    but rather by applying similar results already proved for natural
    numbers.  Some of the tactics mentioned above may prove useful. *)
Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, optional *)
Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, optional *)
Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *) 
(** ** States *)

(** A _state_ represents the current set of values for all the
    variables at some point in the execution of a program. *)

Definition state := id -> nat.

Definition empty_state : state := fun _ => 0.
 
Definition update (st : state) (V:id) (n : nat) : state :=
  fun V' => if beq_id V V' then n else st V'.

(** We'll need a few simple properties of [update]. *)

(** **** Exercise: 2 stars, optional *)
Theorem update_eq : forall n V st,
  (update st V n) V = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional *)
Theorem update_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat), 
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars *)
Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update  (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional *)
Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional *)
Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false -> 
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(** ** Syntax  *)

(** We add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) tactic(c) :=
  first;
  [ c "ANum" | c "AId" | c "APlus" | c "AMinus" | c "AMult" ].

(** Shorthands for variables: *)
Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(** (This convention for naming program variables ([X], [Y], [Z])
    clashes a bit with our earlier use of uppercase letters for
    [Types].  Since we're not using polymorphism heavily in this part
    of the course, this overloading will hopefully not cause
    confusion.) *)

(** Same [bexp]s as before (using the new [aexp]s): *)
Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) tactic(c) :=
  first;
  [ c "BTrue" | c "BFalse" | 
    c "BEq" | c "BLe" | 
    c "BNot" | c "BAnd" ].

(* ################################################### *)
(** ** Evaluation  *)

(** We extend the arith evaluator to handle variables. *)

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId i => st i
  | APlus a1 a2 => plus (aeval st a1) (aeval st a2)
  | AMinus a1 a2  => minus (aeval st a1) (aeval st a2)
  | AMult a1 a2 => mult (aeval st a1) (aeval st a2)
  end.

(** We update the boolean evaluator with the new [aeval]. *)

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with 
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 : 
  aeval (update empty_state X 5) 
        (APlus (ANum 3) (AMult (AId X) (ANum 2))) 
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5) 
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ####################################################### *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (or _statements_). *)

(* ################################################### *)
(** ** Syntax *)

(** Commands: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) tactic(c) :=
  first;
  [ c "SKIP" | c "::=" | c ";" | c "IFB" | c "WHILE" ].

(** More readable concrete syntax, for examples: *)

Notation "'SKIP'" := 
  CSkip.
Notation "l '::=' a" := 
  (CAss l a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).

(* ####################################################### *)
(** ** Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

(** Loops: *)

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;
  Z ::= ANum 5 ;
  subtract_slowly.

(** An infinite loop: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(** Factorial: *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum  1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.

(* ################################################################ *)
(** * Evaluation *)

(** Next we need to define what it means to evaluate an Imp command.
    [WHILE] loops actually make this a bit tricky... *)

(* #################################### *)
(** ** Evaluation Function *)

(** Here's a first try at an evaluation function for commands,
    omitting [WHILE]. *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with 
    | SKIP => 
        st
    | l ::= a1 => 
        update st l (aeval st a1)
    | c1 ; c2 => 
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI => 
        if (beval st b) then ceval_step1 st c1 else ceval_step1 st c2
    | WHILE b1 DO c1 END => 
        st  (* bogus *)
  end.

(** Second try, using an extra numeric argument as a "step index" to
    ensure that evaluation always terminates. *)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with 
  | O => empty_state
  | S i' =>
    match c with 
      | SKIP => 
          st
      | l ::= a1 => 
          update st l (aeval st a1)
      | c1 ; c2 => 
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i' 
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) then ceval_step2 st c1 i' else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1) 
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(** _Note_: It is tempting to think that the index [i] here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same [i] is passed to both recursive
    calls.  Understanding the exact way that [i] is treated will be
    important in the proof of [ceval__ceval_step], which is given as
    an exercise below. *)

(** Third try, returning an [option state] instead of just a [state]
    so that we can distinguish between normal and abnormal
    termination. *)

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ; c2 => 
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) then ceval_step3 st c1 i' else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(** We can improve the readability of this definition by introducing
    an auxiliary function [bind_option] to hide some of the "plumbing"
    involved in repeatedly matching against optional states. *)

Definition bind_option {X Y : Type} (xo : option X) (f : X -> option Y) 
                      : option Y :=
  match xo with
    | None => None
    | Some x => f x
  end.

Fixpoint ceval_step (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ; c2 => 
          bind_option 
            (ceval_step st c1 i')
            (fun st' => ceval_step st' c2 i')
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) then ceval_step st c1 i' else ceval_step st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then bind_option 
                 (ceval_step st c1 i')
                 (fun st' => ceval_step st' c i')
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) := 
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.  

(*
Eval compute in 
  (test_ceval empty_state 
      (X ::= ANum 2; 
       IFB BLe (AId X) (ANum 1)
         THEN Y ::= ANum 3 
         ELSE Z ::= ANum 4
       FI)).
====>
   Some (2, 0, 4)
*)

(** **** Exercise: 2 stars *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Make sure
   your solution satisfies the test that follows. *)

Definition pup_to_n : com := 
  (* FILL IN HERE *) admit.

(** <<
Example pup_to_n_1 : 
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
>> *)
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Write a [While] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [ceval_test] to test your
    program. *)

(* FILL IN HERE *)
(** [] *)

(* #################################### *)
(** ** Evaluation Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type].  

    This is an important change.  Besides freeing us from the
    silliness of passing around step indices all over the place, it
    gives us a lot more flexibility in the definition.  For example,
    if we added concurrency features to the language, we'd want the
    definition of evaluation to be non-deterministic -- not only not
    total, but not even a function. *)

Module CEvalFirstTry.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      ceval SKIP st st
  | E_Ass  : forall st a1 n l,
      aeval st a1 = n ->
      ceval (l ::= a1) st (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st' ->
      ceval c2 st' st'' ->
      ceval (c1 ; c2) st st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval c1 st st' ->
      ceval (IFB b1 THEN c1 ELSE c2 FI) st st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval c2 st st' ->
      ceval (IFB b1 THEN c1 ELSE c2 FI) st st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval (WHILE b1 DO c1 END) st st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval c1 st st' ->
      ceval (WHILE b1 DO c1 END) st' st'' ->
      ceval (WHILE b1 DO c1 END) st st''.

(** Since we'll be using [ceval] a lot, let's define some notation.
    We'll use the notation [c / st ==> st'] for our [ceval] relation,
    that is [c / st ==> st'] means that executing program [c] in a
    starting state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

Notation "c1 '/' st '==>' st'" := (ceval st c1 st') (at level 40, st at level 39).

End CEvalFirstTry.

(** In fact, Coq provides a way to use this notation in the definition
    of [ceval] itself.  This avoids situations where we're working on
    a proof involving statements in the form [c / st ==> st'] but we
    have to refer back to a definition written using the form [ceval
    st c st'].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

Reserved Notation "c1 '/' st '==>' st'" (at level 40, st at level 39).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st ==> st
  | E_Ass  : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st ==> (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  ==> st' ->
      c2 / st' ==> st'' ->
      (c1 ; c2) / st ==> st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st ==> st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (WHILE b1 DO c1 END) / st' ==> st'' ->
      (WHILE b1 DO c1 END) / st ==> st''

  where "c1 '/' st '==>' st'" := (ceval st c1 st').

Tactic Notation "ceval_cases" tactic(first) tactic(c) := first; [
    c "E_Skip" | c "E_Ass" | c "E_Seq" | c "E_IfTrue" | c "E_IfFalse" 
  | c "E_WhileEnd" | c "E_WhileLoop" ].

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
    (X ::= ANum 2; 
     IFB BLe (AId X) (ANum 1) 
       THEN Y ::= ANum 3 
       ELSE Z ::= ANum 4 
     FI) 
   / empty_state 
   ==> (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (update empty_state X 2). 
    Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** Exercise: 2 stars *)
Example ceval_example2:
    (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ==>
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** ** Inference Rule Notation *)

(** We will sometimes (especially in informal discussions)
    write the rules for [ceval] in a more "graphical" form called
    _inference rules_, where the premises above the line allow you
    to derive the conclusion below the line.  For example, the
    constructor [E_Seq] would be written like this as an inference
    rule:
[[[
                           c1 / st ==> st'
                          c2 / st' ==> st''
                         -------------------                            (E_Seq)
                         c1;c2 / st ==> st''
]]]
    Formally, there is nothing deep or complex about inference rules:
    they are just implications.  You can read the rule name on the
    right as the name of the constructor and read both the spaces
    between premises above the line and the line itself as [->].  All
    the variables mentioned in the rule ([c1], [c2], etc.) are
    implicitly bound by a universal quantifier at the beginning.  The
    whole collection of rules is implicitly wrapped in an [Inductive]
    declaration; this is sometimes indicated informally by something
    like "Let [ceval] be the smallest relation closed under the
    following rules...".

    Here is a complete set of inference rules for [ceval]:
[[[
                           ----------------                            (E_Skip)
                           SKIP / st ==> st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   l := a1 / st ==> (update st l n)
        
                           c1 / st ==> st'
                          c2 / st' ==> st''
                         -------------------                            (E_Seq)
                         c1;c2 / st ==> st''

                          beval st b1 = true
                           c1 / st ==> st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st ==> st'

                         beval st b1 = false
                           c2 / st ==> st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st ==> st'

                         beval st b1 = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b1 DO c1 END / st ==> st

                          beval st b1 = true
                           c1 / st ==> st'
                  WHILE b1 DO c1 END / st' ==> st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b1 DO c1 END / st ==> st
]]]
*)

(* ################################################################ *)
(** ** Equivalence of Relational and Step-Indexed Evaluation *)

(** Naturally, we'd hope that the two alternative definitions of
    evaluation actually boil down to the same thing.  This section
    shows that this is the case.  Make sure you understand the
    statements of the theorems and can follow the structure of the
    proofs. *)

(** **** Exercise: 3 stars, optional (aeval_beval_rel) *)
(** Write relations [aeval_rel] and [beval_rel] in the same style as
    [ceval], and prove that they are equivalent to [aeval] and
    [beval]. *)

(** <<
Inductive aeval_rel : 
(* FILL IN HERE *)

Theorem aeval_iff_aeval_rel : forall st a n,
(* FILL IN HERE *)

Inductive beval_rel : 
(* FILL IN HERE *)

Lemma beval_iff_beval_rel : forall st b tv,
(* FILL IN HERE *)
(** [] *)
>> *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st ==> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.
  Case "i = S i'".
    intros c st st' H.
    (com_cases (destruct c) SCase); simpl in H; inversion H; subst; clear H. 
      SCase "SKIP". apply E_Skip.
      SCase "::=". apply E_Ass. reflexivity.

      SCase ";".
        remember (ceval_step st c1 i') as r1. destruct r1.
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s. 
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        SSCase "Evaluation of r1 terminates abnormally -- contradiction".
          inversion H1.

      SCase "IFB". 
        remember (beval st b) as r. destruct r.
        SSCase "r = true".
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        SSCase "r = false".
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      SCase "WHILE". remember (beval st b) as r. destruct r.
        SSCase "r = true". 
          remember (ceval_step st c i') as r1. destruct r1. 
          SSSCase "r1 = Some s".
            apply E_WhileLoop with s. rewrite Heqr. reflexivity.
            apply IHi'. rewrite Heqr1. reflexivity. 
            apply IHi'. simpl in H1. assumption.
          SSSCase "r1 = None".
            inversion H1.
        SSCase "r = false".
          inversion H1. 
          apply E_WhileEnd. 
          rewrite Heqr. subst. reflexivity.  Qed.

(** **** Exercise: 4 stars (ceval_step__ceval_inf) *)
(** Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do *not* simply transcribe the
    steps of the formal proof.

(* FILL IN HERE *)
[]
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 -> ceval_step st c i1 = Some st' -> 
  ceval_step st c i2 = Some st'.
Proof. 
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [|i2']. inversion Hle. 
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval. 
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";".
      simpl in Hceval. simpl. 
      remember (ceval_step st c1 i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.

    SCase "IFB".
      simpl in Hceval. simpl.
      remember (beval st b) as bval.
      destruct bval; apply (IHi1' i2') in Hceval; assumption.
    
    SCase "WHILE".
    simpl in Hceval. simpl.
      destruct (beval st b); try assumption. 
      remember (ceval_step st c i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption. 
        rewrite -> Heqst1'o. simpl. simpl in Hceval. 
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "i1'o = None".
        simpl in Hceval. inversion Hceval.  Qed.

(** **** Exercise: 3 stars *)
(** Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)
Theorem ceval__ceval_step: forall c st st',
      c / st ==> st' ->
      exists i, ceval_step st c i = Some st'.
Proof. 
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st ==> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ####################################################### *)
(** ** Determinacy of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement (imposed by Coq's restrictions on Fixpoint
    definitions) that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    even a partial function?  That is, is it possible that, beginning
    from the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?
 
    In fact, this cannot happen: the evaluation relation [ceval] is a
    partial function.  Here's the proof: *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st ==> st1  ->
     c / st ==> st2 ->
     st1 = st2.
Proof. 
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  (ceval_cases (induction E1) Case); intros st2 E2; inversion E2; subst. 
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq". 
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption. 
  Case "E_IfTrue". 
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse". 
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd". 
    SCase "b1 evaluates to true".
      reflexivity.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop". 
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to false".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(** Here's a slicker proof, using the fact that the relational and
    step-indexed definition of evaluation are the same. *)

Theorem ceval_deterministic' : forall c st st1 st2,
     c / st ==> st1  ->
     c / st ==> st2 ->
     st1 = st2.
Proof. 
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1]. 
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity. 
  omega. omega.  Qed.

(* ####################################################### *)
(** * Reasoning about programs *)

(** We'll get much deeper into reasoning about programs in Imp in the
    following chapters.  Here are some simple properties just to get
    the juices flowing... *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st ==> st' ->
  st' X = plus n 2.
Proof.
  intros st n st' HX Heval.
  (* inverting Heval essentially forces coq to expand one step of the
     ceval computation - in this case revealing that st' must be st
     extended with the new value of X, since plus2 is an assignment *)
  inversion Heval. subst.
  apply update_eq.  Qed.

(** **** Exercise: 3 stars (XtimesYinZ_spec) *)
(** State and prove a specification of the XtimesYinZ Imp program. *)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars *)
Theorem loop_never_stops : forall st st',
  ~(loop / st ==> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  (* Proceed by induction on the assumed derivation showing that
     loopdef terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

(** **** Exercise: 2 stars, optional *)
(** The [no_whiles] property yields [true] on just those programs that
    have no while loops.  Using [Inductive], write a property
    [no_Whiles] such that [no_Whiles c] is provable exactly when [c]
    is a program with no while loops.  Then prove its equivalence
    with [no_whiles]. *)

Inductive no_Whiles: com -> Prop := 
 (* FILL IN HERE *) 
  .

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_Whiles c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem that says this. *)
(** (Use either [no_whiles] or [no_Whiles], as you prefer.) *)
(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, optional (add_for_loop) *)
(** Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.)
*)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (short_circuit) *)  
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval].
*)
(* FILL IN HERE *)

(** **** Exercise: 4 stars (stack_compiler) *)
(** HP Calculators, programming languages like Forth and Postscript,
    and the Java Virtual Machine all evaluate arithmetic expressions
    using a stack. For instance, the expression
<<
   (2*3)+(3*(4-2))
>>
   would be entered as
<<
   2 3 * 3 4 2 - * +
>>
   and evaluated like this:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          | 
>>

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions, and to prove its
  correctness.

  The instruction set for our stack language will consist of the
  following instructions:    
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad i]: Load the identifier [i] from the store and push it on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and push the
                  result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply.
*)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr. 

(** Write a function to evaluate programs in the stack language. It
    takes as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and returns the stack after
    executing the program. Test your function on the examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense it is
    immaterial, since our compiler will never emit such a malformed
    program. However, when you do the correctness proof you may find
    some choices makes the proof easier than others. *)

Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr) 
                   : list nat :=
(* FILL IN HERE *) admit.

Example s_execute1 : 
     s_execute empty_state [] [SPush 5, SPush 3, SPush 1, SMinus]
   = [2, 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 : 
     s_execute (update empty_state X 3) [3,4] [SPush 4, SLoad X, SMult, SPlus]
   = [15, 4].
(* FILL IN HERE *) Admitted. 

(** Next, write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)
Fixpoint s_compile (e : aexp) : list sinstr :=
(* FILL IN HERE *) admit.

(** <<
Example s_compile1 : 
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X, SPush 2, SLoad Y, SMult, SMinus].
Proof. reflexivity. Qed.
>> *)

(** Finally, prove the following theorem, stating that the [compile]
    function behaves correctly.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis. *)

(* FILL IN HERE *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

