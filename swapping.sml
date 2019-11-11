(* SWAPPING.SML \lstset{language=ML,upquote=true}\begin{comment} % *)
(* %
\end{comment} % (*
*)
\begin{comment}==LITERATE PROGRAM FILE HEADER =======================================================\end{comment}

\section{HOL Preliminaries}

The HOL logic system provides a proof manager which manages the derivation of an proof.  It does so using a 
structure which represents a list of assumptions, a desired conclusion, and a list of theorems from which justify the 
conclusion as drawn from the assumptions.  A goal is a similar structure, without the theorems: that is, the goal consists
of a list of assumptions and a conclusion for which a proof is desired. The derivation of a proof is a tree structure
and can be represented using a fractional notation, where the numerator represents the goal, and the denominator represents
a set of sub-goals which result from a mechanical application of a rule of logic.  

Another way of looking at a deriviation is to treat the top-most goal as the root of a tree; the sub goals sprout out 
from the root, and whenever the outermost sub-goals evaluates to true or false, it is a leaf.  
Once we have evalauted sub-goal in such a manner, the corresponding terms from the trunk can be substituted.

There are a number of libraries in HOL which makes this possible.  One library in particular,  known as `bossLib', 
provides a suite of basic automated proving tools.  A number of other libraries provide type syntaxes which make it
possible to extends HOLs native data types to include numbers, strings and lists.We now load these libraries and open 
them to make them public.    Finally, to get feedback about data types and proofs,
we enable the HOL system to display all assumptions and data types currently in use.

\begin{lstlisting} % *)

load "bossLib";
open bossLib;

load "stringSyntax";
open stringSyntax;

load "numSyntax";
open numSyntax;

load "listSyntax";
open listSyntax;

show_types:=true;
show_assums:=true;

(* \end{lstlisting}
\begin{lstlisting} % (*

   The internal features of the bossLib structure are now exposed to the HOL session.
   Terms can now consist of expressions on strings, numbers and lists.
   Types and assumptions will be echoed verbosely to the user console.
*) \end{lstlisting} % 

\section{Definition of Boolean Refinement}

The language of program refinement is that of logic: truth and falsehood. Truth, however, is a much loftier goal than the more practical
problems faced by software engineers; to mistake program correctness for truth is philosophically invalid.  Rather, when we speak of truth 
in a programming context, it is intended to refer to the two outcomes of the Turing Machine: either the machine halts and the problem is solved, 
or the solution is not in the language of the machine.  We introduce the specifications $abort$ and $magic$, which we use when it is
important to stress this interpretation of the logic.  Given any initial state and any final state, $abort$ returns true, while $magic$ 
returns false.

\begin{lstlisting} % *)

Define `abort = \(s:'a) (s':'b). T`;
Define `magic = \(s:'a) (s':'b). F`;
 
(* \end{lstlisting}
\begin{lstlisting} % (*

	If the current state is a solution, then simply abort.
	If no solution exists in the language of the machine, then the specification can be refined only by magic.
*) \end{lstlisting} % 

In our model, specifications are boolean functions that evaluate true when a behaviour is accepted.
We may say that a specification is refined by another; since specifications are boolean
functions, refinement is a boolean operation.  Specifically, we define the boolean operator $\sqsubseteq_b$ 
such that  $v \sqsubseteq_b u$ if and only if for all applicable state spaces, $ u \Rightarrow v$.  Having defined 
refinement in this way, a common requirement that arises in proofs is to rewrite refinement using primitive
boolean operators.  To perform these common tasks, we introduce REFINEMENT_TAC and REFINEMENT_RULE.  We demonstrate
the use of these tactics in a simple proof to show that magic refines all specifications, and all specifications
refine abort.

\begin{lstlisting} % *)

set_fixity "[=." (Infixl 500);
val DefinitionOfRefinement = xDefine "bRefinement" 
	`v [=. u = !(s:'a) (s':'b). u s s' ==> v s s'`
;

val REFINEMENT_TAC = 
	(*
		[
		]	|-
				`\ s s' .v s s' [=. u 
	*)
	(PURE_ONCE_REWRITE_TAC [DefinitionOfRefinement])
				(*	[
					]	|-
							!s s'. u s s' ==> \ s s'. v s s'
				*)
	THEN
		(REPEAT GEN_TAC)	
				(*	[
					]	|-
						 u s s'	 ==>  (\s s'. v s s') s s'
				*)
	THEN
		(BETA_TAC)
				(*	[
					]	|-
						 u s s'	 ==>  v s s'
				*)
;

fun REFINEMENT_RULE th = 
	(
		BETA_RULE
		(
			GEN_ALL
			(
				PURE_ONCE_REWRITE_RULE [DefinitionOfRefinement] th
			)
		)
	)
;


(* \end{lstlisting}
\begin{lstlisting} % (*

EXAMPLES
prove 
	(
		``  f [=. magic ``,
		REFINEMENT_TAC
			(* 
				[
				] |-
					magic s s' ==> f s s'
			*)	
	THEN
		EVAL_TAC
			(* |- f [=. magic : thm *)
	)
;
	
prove 
	(
		``  abort [=. f ``,
		REFINEMENT_TAC
			(* 
				[
				] |-
					f s s' ==> abort s s'
			*)	
	THEN
		EVAL_TAC
			(* |- abort [=. f : thm *)
	)
;
*) \end{lstlisting} % 

The above code demonstrates three commonly used functions of the HOL proving system, namely:

\begin{enumerate}
\item{Define}

Allows constants and functions to be introduced.
\item{xDefine and set_fixity}

Allows symbolic constants and infix operators to be introduced.
\item{EVAL}

Allows constants and functions to be simplified through substitution and evaluation.
\end{enumerate}

section{Definition of Assignment }

 
\begin{lstlisting} % *)

Define `assign x e s s' = 
			!y. 
				if x = y then 
					(s' y) = (e s)
                else 
					(s' y) = (s y) 
		` 
;

(* \end{lstlisting}
\begin{lstlisting} % (*

EXAMPLES
	let	val	
		xForyImplies_sx_Is_es = 
		(
				EVAL_RULE (SPEC ``x:'a`` (EVAL_RULE (ASSUME ``assign x e s s'``)))
						(*	[
								assign x e s s'	
							]	|-
								s' x  = e s  : thm
						*)
		)

	in
		prove (
			``(\ (s :'a -> 'b) (s' :'a -> 'b).((s'(x:'a)) = ((e:('a->'b)->'b) s))) [=. (assign x e)``,
			(
				(REFINEMENT_TAC)	
						(*	[
							]	|-
								 assign x e s s'	
								 ==>
								 s' x = e s	
						*)
			THEN
				(DISCH_TAC)	
						(* 	[ 	
								assign x e s s'	
							]	|- 
								s' x = e s	
						*)
			THEN 
				(ACCEPT_TAC xForyImplies_sx_Is_es)
			)
		)
	end
;

*) \end{lstlisting} % 

The above code demonstrates seven commonly used tactics of the HOL proving system, namely:

\begin{enumerate}
\item{ASSUME, ASSUME_TAC}

Given a theorem whose assumptions are a subset of the current goal, adds the theorems conclusion to goal's assumptions.

\item{EVAL_RULE}

Creates an equality between the theorems conclusion and the result of evaluating its terms and functions.
\item{SPEC,SPECL}

Allows a general theorem to be specialized to a particular instance. 
SPECL allows parallel execution of multiple SPEC tactics using a list of instances.
\item{SUBST_TAC}

Given an equality, if the left-hand side is a term in the goal, then it is replaced by the right-hand side.
\item{DISCH_TAC}

Given an implications, moves the left-hand side of the implication into the list of assumptions.
\item{ACCEPT_TAC}

Once a sub-goal has been converted into the form of an existing theorem, this tactic promotes the sub-goal to a theorem.
\end{enumerate}

\section{Sequential Composition}

As the example shows, using language constructs such as a verilog generate statement, it is possible to 
implement many parallel specifications in hardware.  Depending on hardware resources and timing closure
considerations, often a sequential implementation is preferred.  This is made possible by using an
existential specification.  Specifically, we assert that their exists an intermediate state, $s''$, 
such that initial specification $f$ provides a path from $s$ to $s''$, and the final specification $g$
provides a path from $s''$ to $s'$.  As an example of how to use this, consider how the specification
$x ' = 1 \and y ' = 1$ is satisfied by $y:=1;x:=y$.
 
\begin{lstlisting} % *)

Define `sc f g s s' = (? s'' . f s s'' /\ g s'' s' ) ` ;

(* \end{lstlisting}
\begin{lstlisting} % (*

EXAMPLES
	let	val	
		goal = ``(\ (s:'a->num) (s':'a->num). (((s' (x:'a)) = 1 ) /\ ((s' (y:'a)) = 1))) [=. (sc (assign y (\ (s:'a->num).1)) (assign x (\ (s:'a->num).(s y))))``
	and
		lemma = (UNDISCH_ALL (#1 (EQ_IMP_RULE (EVAL (mk_comb(mk_comb ((rand goal),``s:'a->num``),``s':'a->num``))))))
						(*	[
								sc (assign y (\s. 1)) (assign x (\s. s y)) s s'
							]	|-
								    ?s''. 
										(!y'. if y = y' then s'' y' = 1 else s'' y' = s y') 
										/\
										(!y'. if x = y' then s' y' = s'' y else s' y' = s'' y')
						*)
	in
		prove 
		(
			goal,
			(
				(REFINEMENT_TAC)
						(*	[
							]	|-
									sc (assign y (\s. 1)) (assign x (\s. s y)) s s' ==> (s' x = 1) /\ (s' y = 1)
						*)
			THEN
				(STRIP_TAC)	
						(* 	[ 	
								sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s' x = 1) /\ (s' y = 1)
						*)
			THEN 
				(STRIP_ASSUME_TAC lemma)
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s' x = 1) /\ (s' y = 1)
						*)
			THEN
				(SUBST_TAC
					[(
						EVAL_RULE 												
							(
								(SPECL [``x:'a``]	(ASSUME ( #2(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
							)
					)]
				)
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s'' y = 1) /\ (s' y = 1)
						*)
			THEN
				(SUBST_TAC
					[(
						EVAL_RULE 												
							(
								(SPECL [``y:'a``]	(ASSUME ( #2(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
							)
					)]
				)
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s'' y = 1) /\ (s'' y = 1 )
						*)
			THEN
				(CONJ_TAC THENL
					[(
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y ( \s. 1)) (assign x ( \s. s y)) s s' 
							]	|- 
									(s'' y = (1 :num))
						*)				
						(ACCEPT_TAC
							(
								EVAL_RULE 
								(
									(SPECL [``y:'a``]	(ASSUME (#1(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
								)
							)
						)
					),(
						(ACCEPT_TAC
							(
								EVAL_RULE 
									(
										(SPECL [``y:'a``]	(ASSUME (#1(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
									)
							)
						)
					)]
				)
			)
		)
	end
;

*) \end{lstlisting} % 

The example above introduces the following tactics and rules:

\begin{enumerate}
\item{UNDISCH_ALL}

Given a list of assumptions, converts them into a chain of refinements.

\item{EQ_IMP_RULE}

Swaps the left-hand and right-hand side of an equation, as required to apply the SUBST_TAC.
\item{STRIP_TAC,STRIP_ASSUME_TAC}

Similar to DISCH_TAC, but decomposes assumptions to remove quantifiers and conjunctions so that they can be more readily used.
\item{CONJ_TAC, EQ_TAC}

If a theorem is in the form a conjunction, this breaks the goal into two sub-goals, one for the left-hand side,
the other for the right-hand side.  EQ_TAC was not used in the example, but does the same for equations.

\item{rand,rator,dest_conj,beta_conv,mk_comb, concl, etc}

There are a variety of routines defined in the Term structure which are useful for extracting and transforming specific 
terms into the form needed to prove a goal.

Given an implications, moves the left-hand side of the implication into the list of assumptions.
\item{fetch}

Retrieves a theorem stored in a theory file (e.g. definitions are stored in the current theory automatically for ease of access)
\end{enumerate}

\section{Manipulating Functions}

In predicative programming, it is often necessary to treat functions as objects.  The lambda notation is particularly powerful for this
in HOL.  Because many proofs require converting to and from the lambda notation, some utility function are introduces here.  

\begin{lstlisting} % *)

fun SWAPLR_RULE th =(PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] th);

val	thmAbstractFunction =	
	prove
	(	
		``!(t :'a -> 'b) (f :'a -> 'b).(t = (\(y :'a). f y)) <=> (!(y:'a).(t (y :'a) = f y)) ``,
		(
			(EVAL_TAC)
				(* 	[ 	
					]	|- 
							!t f. (t = f) <=> !y. t y = f y
				*)
		THEN
			(REPEAT STRIP_TAC)
				(* 	[ 	
					]	|- 
							 (t = f) <=> !y. t y = f y
				*)
		THEN
			(ACCEPT_TAC (SPECL [``t:'a->'b``,``f:'a->'b``] FUN_EQ_THM))
				(*  [] |- !t f. (t = (\y. f y)) <=> !y. t y = f y : thm *) 
		)
	)
;

val	thmConditionalFunction =	
	let val
		goal =	``!(t :'a -> 'b) (a :'a -> bool) (b :'a -> 'b) (c :'a -> 'b). (!(y :'a). 
				if a y then t y = b y else t y = c y) 
					<=>
				(t = (\(y :'a). if a y then b y else c y))``
	and
		specializedTerm0 = [``t:'a->'b``,``\(y:'a).(if (a:'a->bool) y then (b:'a->'b) y else (c:'a->'b) y)``]
	and
		specializedTerm1 = [``\rhs.((((t:'a->'b) (y:'a)) = rhs )) ``,``(a:'a -> bool) (y: 'a)``,``((b:'a->'b) (y:'a))``, ``((c:'a->'b)(y:'a))``]
	in
		prove
		(
			goal,
			(
				(*	[
					]	|-
							!t a b c. (!y. if a y then t y = b y else t y = c y) <=>  (t = (\y. if a y then b y else c y))
				*)
				(REPEAT STRIP_TAC)
					(* 	[ 	
						]	|- 
							(!y. if a y then t y = b y else t y = c y) <=>  (t = (\y. if a y then b y else c y))
					*)
			THEN
				(EQ_TAC	THENL
					[(
						(* 	[ 	
							]	|- 
									(!y. if a y then t y = b y else t y = c y) ==>  (t = (\y. if a y then b y else c y))
						*)
						(REPEAT STRIP_TAC)
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								]	|- 
										(t = (\y. if a y then b y else c y))
							*)
					THEN
						(SUBST_TAC [(BETA_RULE (SPECL specializedTerm0 thmAbstractFunction))])
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								  ]	|- 
										!y. t y = if a y then b y else c y
							*)
					THEN
						(REPEAT STRIP_TAC)
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								  ]	|- 
										t y = if a y then b y else c y							*)
					THEN
						(SUBST_TAC [(BETA_RULE(SPECL  specializedTerm1 (INST_TYPE [alpha |-> ``:'b ``, beta |->``:bool``] COND_RAND)))])
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								  ]	|- 
										 if a y then t y = b y else t y = c y
							*)
					THEN 
						(FIRST_ASSUM (ACCEPT_TAC o (SPEC ``y:'a``)))
					),(
						(* 	[ 	
							]	|- 
									(t = (\y. if a y then b y else c y)) ==>  (!y. if a y then t y = b y else t y = c y)
						*)
						(REPEAT STRIP_TAC)
							(* 	[ 	
									t = (\y. if a y then b y else c y)								  
								]	|- 
										if a y then t y = b y else t y = c y
							*)
					THEN
						(SUBST_TAC [(SWAPLR_RULE 
										(
											BETA_RULE
											(
												SPECL 
													[	``\rhs.((((t:'a->'b) (y:'a)) = rhs )) ``,
														``(a:'a -> bool) (y: 'a)``,``((b:'a->'b) (y:'a))``, 
														``((c:'a->'b)(y:'a))``
													] (INST_TYPE [alpha |-> ``:'b ``, beta |->``:bool``] COND_RAND)
											)
										)
									)]
						)
							(* 	[ 	
									t = (\y. if a y then b y else c y)								  
								]	|- 
										t y = if a y then b y else c y
							*)
					THEN
						(ASSUME_TAC 
							(
								UNDISCH (#1(EQ_IMP_RULE 				
										(
											BETA_RULE 
											(
													SPECL 
													[	``t:'a->'b``,
														``\ (y:'a).(if (a:'a->bool) y then (b:'a->'b) y else (c:'a->'b) y)``
													] thmAbstractFunction
											)
										)
									))
							)
							(* 	[ 
									!y. t y = if a y then b y else c y
								,
									t = (\y. if a y then b y else c y)								  
								]	|- 
										t y = if a y then b y else c y
							*)
						)
					THEN
						(FIRST_ASSUM (ACCEPT_TAC o (SPEC ``y:'a``)))
					)]				
					(* []	|- !t a b c.  (!y. if a y then t y = b y else t y = c y) <=> (t = (\y. if a y then b y else c y)) : thm *)
				)
			)
		)
	end
;

(* \end{lstlisting}
\begin{lstlisting} % (*

EXAMPLES


*) \end{lstlisting} % 

		
The following HOL theorems were introduced in the previous proof:

\begin{enumerate}
\item{PURE_ONCE_REWRITE_RULE}

Performs a limited rewrites of terms on an existing theorem
\item{EQ_SYM_EQ}

This theorem can be used in conjuntion with the PURE_ONCE_REWRITE rule to swap the left-hand side and right-hand side 
of an equation.
\item{COND_RAND}

This theorem treats a conditional statement as an operand of a function, allowing the function to be moved. 
It is written $\forall (f :'a -> 'b) (b :bool) (x :'a) (y :'a) \cdot  f (if b then x else y) = if b then f x else f y $
\item{FUN_EQ_THM}

This theorem defines equality among functions. 
It is written $\forall (f :'a -> 'b) (g :'a -> 'b) \cdot ((f = g) \Leftrightarrow  \forall (x :'a) \cdot f x = g x )$
\item{BETA_RULE}

This theorem evaluate a theorem which contains lambda expressions.
\item{THENL (with EQ_TAC)}

THENL is similar to THEN, but must be used following any tactic that breaks a goal down into subgoals.  
It accepts a list of tactics, one for each sub-goal.  In the proof, THENL was used with EQ_TAC, which 
breaks an equality into two sub-goals using EQ_IMP_RULE.

\item{FIRST_ASSUM and o (the tactical composition operator)}

Assumptions in HOL are not managed consistently accross versions of HOL.  If an assumption is required as a parameter to 
a tactic, FIRST_ASSUM provides a search capability. It accepts a function to which it passes as a parameter the ASSUMED 
theorem for each assumption.  If the result is a valid tactic, and the tactic succeeds on the goal, then the search
is considered successful; otherwise, the search continues with the next assumption.

\end{enumerate}
	
\section{In-place Proofs and Lemmas}

We've seen how sub-goals are a neccessary part of complex proofs.  While sub-goals are unavoidable, one method to minimize them
is to allow in-place proofs.  An in-place proof takes advantage of the fact that any assumption that remains in the assumption 
list must evaluate to true.  Thus, if we have an existing theorem that we expect will become part of the proof process, the following
strategy can be used to introduce in-place proofs:

\begin{enumerate}
\item{Introduce the lemma as an assumption of the proof}
\item{Proceed with the proof as desired until a term becomes alpha-convertible to the lemma}
\item{Convert the term to a boolean constant, then evaluate the goal using EVAL_TAC}
\end{enumerate}

The following functions facilitate the above approach:

\begin{lstlisting} % *)

fun EXHAUSTIVELY x = 
	(REPEAT (CHANGED_TAC x))
;

val REP_EVAL_TAC = 
	(EXHAUSTIVELY EVAL_TAC)
;

val thmAcceptInPlace = UNDISCH (prove (``(v:bool) ==> (v <=> T)``,REP_EVAL_TAC));
val thmRejectInPlace = UNDISCH (prove (``(~(v:bool)) ==> (v <=> F)``,REP_EVAL_TAC));

fun USE_CONTEXT (asl:term list) (th:thm) =   
	if (null asl) then th else (UNDISCH (USE_CONTEXT (tl(asl)) th))
;

fun VSUB (v:term) (e:term) (th:thm) =
	USE_CONTEXT (hyp th) (SPEC e (GEN v (DISCH_ALL th)))
;

fun MAKE_IT_SO (th:thm) = 
	((SUBST_TAC [(VSUB ``v:bool`` (concl th) thmAcceptInPlace)]) THEN EVAL_TAC)
;

fun MAKE_IT_NO (th:thm)  = 
	if(is_neg(concl th)) then
		((SUBST_TAC [(VSUB ``v:bool`` (dest_neg(concl th)) thmRejectInPlace)]) THEN EVAL_TAC)
	else
		((SUBST_TAC [(VSUB ``v:bool`` (mk_neg(concl th)) thmRejectInPlace)]) THEN EVAL_TAC)
;
(* \end{lstlisting}
\begin{lstlisting} % (*

EXAMPLES

	For an example of these theorems, see the proof of the one-point lemma
*) \end{lstlisting} % 


\section{Type Instantiation}

Before we can move on to practical examples, a discussion on type instantiation is neccessary.
Type instantiation allows us to convert a theorem that holds for all types to one that holds 
for a specific typeor combination of types.

Type instantiation can be a very powerful tool.  This is especially true when an atomic type
is cast as a composite type, such as converting the type ``:'a`` to the function ``:'a->'b``.
In the typed lambda calculus, there is no distinction between a composite type and a function.
Any  path from one type-space to another is inherently a function.

The HOL type-inference system and the INST_TYPE can be used to take simple theorems and specification
and extend them to more complex classes of systems.  Often-times, however, it is desirable to revert
from a complex type or function to a form that can be more easily manipulated and parameterized.  This 
is especially important when we consider that the current definition of state-spaces is polymorphic
in this implementation.  We know only that a state-space s is of type ``'a->'b``, without restricting
how we define our addressing mechanism (type ``'a``) or how we define our data representation (type ``'b``).

Our definitions of magic, abort and assignment are tied to state-spaces, but because they are abstract state spaces, 
it is sometimes helpful to completely eliminate them from a derivation. The following theorem faciliates this:

\begin{lstlisting} % *)

val	SPEC_EQ_THM = 
	prove
	(
		``(!(s :'a) (s' :'b).(f :'a -> 'b -> 'c) s s' = (g :'a -> 'b -> 'c) s s') <=> (f = g)``,
		(
			(EQ_TAC THENL
				[(
					(* 	[ 	
						]	|- 
								(!s s'. f s s' = g s s') ==> (f = g)
					*)
					(DISCH_TAC)
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									(f = g)
						*)
				THEN
					(SUBST_TAC [(INST_TYPE [beta |-> ``:'b->'c``] (SPEC_ALL FUN_EQ_THM))])
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									!x. f x = g x
						*)
				THEN
					(GEN_TAC)
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									f x = g x
						*)
				THEN
					(SUBST_TAC [(SPECL [``(f:'a->'b->'c) (x:'a)``,``(g:'a->'b->'c) (x:'a)``] (INST_TYPE [alpha |-> ``:'b``, beta |-> gamma] FUN_EQ_THM))])
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									 !x'. f x x' = g x x'
						*)
				THEN
					(GEN_TAC)
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									 f x x' = g x x'
						*)
				THEN
					(FIRST_ASSUM (ACCEPT_TAC o (SPECL [``x:'a``,``x':'b``])))
				),(
					(* 	[ 	
						]	|- 
								(f = g) ==> !s s'. f s s' = g s s'
					*)
					(REPEAT STRIP_TAC)
						(* 	[ 	
									(f = g) 
							]	|- 
									!s s'. f s s' = g s s'
						*)
				THEN
					(REPEAT AP_THM_TAC)
						(* 	[ 	
									(f = g) 
							]	|- 
									f = g 
						*)
				THEN
					(FIRST_ASSUM ACCEPT_TAC)
				)]
			)
		)	
			(* 
				[] |- (!s s'. f s s' = g s s') <=> (f = g) : proof
			*) 
	)
;

(* \end{lstlisting}
\begin{lstlisting} % (*

EXAMPLES

Type instantiation is ubiquitous in the HOL logic proving system
 
*) \end{lstlisting} % 

\section{Predicative Programming Laws}

We've already seen how the ability to substitute terms with expressions allows us to derive proofs from goals. 
Since programs are proofs, this means that substitution allows us to derive new programs from existing
algorithms.  The substitution may be a replacement of an abstract class with a functional prototype, or it may be
a data refinement.  Whatever the reason, the ability to construct new programs from existing templates is a 
powerful software development strategy.

Keeping with the existing model for state spaces and specifications, the following provides a suitable definintion of
substitution at the theoretical level.  Our example shows how this can be used to derive higher level theorems such 
as the forward substitution law.

\begin{lstlisting} % *)

val thmAbstractSpecification = 
		INST_TYPE [alpha |-> ``:'a -> 'b``, beta |-> ``:'a -> 'b``, gamma |-> ``:bool``] SPEC_EQ_THM
			(* 	
				[] |- (!s s'. f s s' <=> g s s') <=> (f = g)   : thm 			
			*)
;

val thmOnePointLemma=
	prove
	(
		`` (x = x) /\ (f x t ) <=> f x t``,
		(
			(EQ_TAC	THENL
				[(
					(* 	[ 	
						]	|- 
								((x  = x) /\ (f  x t )) ==> f x t
					*)
						(ASSUME_TAC (REFL ``x``))
						(* 	[ 	(x = x) 
							]	|- 
									((x = x) /\ (f x t)) ==> f x t
						*)
					THEN
						(FIRST_ASSUM  MAKE_IT_SO)
				),(
					(* 	[ 	
						]	|- 
								(f x t) ==> (x = x) /\ f x t
					*)
						(DISCH_TAC)
						(* 	[ 	
								(f x t)
							]	|- 
									(x = x) /\ f x t
						*)
					THEN
						(FIRST_ASSUM  MAKE_IT_SO)
				)]
			)					
		)
	)
;
		
Define `subs f x e s s'
              = (let s'' = \y. if x=y then e s else s y
                  in f s'' s') `;

val thmForwardSubstitution =
	let	val	
		conversion0 = BETA_RULE
						(
							SWAPLR_RULE 
							(
								SPECL 
									[
										``s'':'a->'b``,
										``\(y:'a).((x:'a) = y)``,
										``\(y:'a).((e:('a->'b)->'b) (s:'a->'b))``,
										``s:'a->'b``
									] 
										thmConditionalFunction
							)
						)
	and
		conversion1 = SWAPLR_RULE 						
						(
							BETA_RULE
							(
								SPECL 
									[
										``s'':'a->'b``,
										``\ (y:'a).if (x:'a) = y then (e:('a->'b)->'b) (s:'a->'b) else s y``
									] 
										thmAbstractFunction
							)
						)
	and
		lemma0 = BETA_RULE
						(
							SPECL 
								[
									``s'':'a->'b``,
									``\(y:'a).if (x:'a) = y then (e:('a->'b)->'b) (s:'a->'b) else s y``
								] 
									thmAbstractFunction
						)
	and 
		lemma1	=	VSUB ``t:'c`` ``s':'c`` 
						(
							VSUB ``x:'a->'b`` ``\(y:'a).if(x = y) then (e:('a->'b)->'b) (s:'a->'b) else s y`` 
								(INST_TYPE [alpha |-> ``:('a->'b)`` , beta |-> ``:'c``] thmOnePointLemma)
						)
	in
		prove 
		(
			``!f e x s s'. sc (assign x e) f s s' = subs f x e s s' ``,
			(
				(REPEAT STRIP_TAC) 
					(* 	[ 	
						]	|- 
								 sc (assign x e) f s s' <=> subs f x e s s'
					*)
			THEN
				(EVAL_TAC)
					(* 	[ 	
						]	|- 
								(?s''. 
									(!y. if x = y then s'' y = e s else s'' y = s y) /\ f s'' s') 
								<=>
									f (\y. if x = y then e s else s y) s'
					*)
			THEN
				(REWRITE_TAC [(REWRITE_RULE [conversion0] lemma0),conversion1])
					(* 	[ 	
						]	|- 
								(?s''. 
									(s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								<=>
									f (\y. if x = y then e s else s y) s'
					*)
			THEN
				(SUBST_TAC [(SWAPLR_RULE lemma1)])
					(* 	[ 	
						]	|- 
								 (?s''. 
									(s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								<=>
										((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 	
									/\	
										f (\y. if x = y then e s else s y) s'
					*)
			THEN
				(EQ_TAC THENL
					[(
						(* 	[ 	
							]	|- 
									 (?s''. 
										(s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
									==>
											((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
											f (\y. if x = y then e s else s y) s'

						*)
						(DISCH_TAC)
							(* 	[ 	
									(?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								]	|- 
											((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
											f (\y. if x = y then e s else s y) s'
							*)
					THEN
						(FIRST_ASSUM CHOOSE_TAC)
							(* 	[ 	
									(s'' = (\y. if x = y then e s else s y)) /\ f s'' s'
								,
									(?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								]	|- 
											((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										 /\
											f (\y. if x = y then e s else s y) s'
							*)
					THEN
						(FIRST_ASSUM (fn th =>  (TRY(REWRITE_TAC [(SWAPLR_RULE th)]))))
					),(
						(* 	[ 	
							]	|- 
											((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
											f (\y. if x = y then e s else s y) s'
									==>
									 (?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
						*)
						(DISCH_TAC)
							(* 	[ 	
									((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
									f (\y. if x = y then e s else s y) s'
								]	|-
									 (?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
							*)
					THEN
						(FIRST_ASSUM (fn th =>  (TRY (EXISTS_TAC ((#1(dest_eq(#1(dest_conj(concl th))))))))))
							(* 	[ 	
									((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
									f (\y. if x = y then e s else s y) s'
								]	|- 
											((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
											f (\y. if x = y then e s else s y) s'
							*)
					THEN
						(FIRST_ASSUM MAKE_IT_SO)
					)]
				)
			)
		)
	end
;

(* \end{lstlisting}
\begin{lstlisting} % (*

EXAMPLES

	Please refer to the section on swapping algorithms for examples of the use of the forward substitution law
*) \end{lstlisting} % 




\section{Swapping Algorithms}

The final exercise is to demonstrate the use of the theory on some sample programs.

A useful function on state spaces is the swap command which is defined as:

(s' x = s y /\ s' y = s x) 

where s is free provided that s x and s y exist and are of the same type.

We wish to show that provided x and y are the same type, the following are valid implementatons:

\begin{enumerate}
\item{in the general case, instantiating variable names (type 'a) with strings}

\begin{lstlisting} % *)
fun EvaluateFor valList =
	if(null valList) then 
	(
		(REPEAT DISCH_TAC) 
		THEN
		(REPEAT (FIRST_ASSUM (fn th => (CHANGED_TAC (SUBST_TAC [th]))) ))
	)
	else
	(
		(EVERY_ASSUM 
			(fn th =>	let val instance = (SPECL [(hd valList)] th) 
					in 
					( 
						(ASSUME_TAC instance) THEN 
						(UNDISCH_TAC (concl instance))	THEN
						(REP_EVAL_TAC)
 					)
					end
			)
		)
		THEN
		(
			EvaluateFor (tl valList)
		)
	)
;

val GeneralSwap = let val
	conversion =	
		PURE_ONCE_REWRITE_RULE [thmAbstractSpecification] 
			(
				SPECL 
					[
						``"t"``,
						``(assign "x" (\ (s:string->'b). s "y"))``,
						``(\ (s:string->'b).s "x")``
					]   
					(INST_TYPE 
						[	alpha |-> ``:string``, 
							gamma |-> ``:string->'b``
						] 
						(	REFINEMENT_RULE 
							(	
								SPECL 
									[
										``f:('a->'b)->'c->bool``,
										``e:('a->'b)->'b``,
										``x:'a``
									] 
									thmForwardSubstitution
							)	
						)
					)
			)
	in
		prove
		(
			``	( 
					(
						\ (s:string->'b) (s':string->'b) . ((s' "x") = (s "y")) /\ ((s' "y") = (s "x"))
					) 
					[=. 
					( 
						sc 
						(
							sc (assign ("t") (\ (s:string->'b).s "x")) (assign "x" (\ (s:string->'b). s "y"))
						)
						(assign "y" (\ (s:string->'b).s "t")) 
					)
				)
			``
			,
			(SUBST_TAC [conversion])
				(*	[				
					]	|- 
							 (\s s'. (s' "x" = s "y") /\ (s' "y" = s "x")) [=. sc (subs (assign "x" (\s. s "y")) "t" (\s. s "x")) (assign "y" (\s. s "t"))					
				*)
		THEN
			(REP_EVAL_TAC)
				(*	[
					]	|-
							!s s'.  
								(?s''. 
										(!y.if "x" = y then  s'' y = s "y"  else s' y = if "t" = y then s "x" else s y) 
												/\
										(!y. if "y" = y then s' y = s'' "t" else s' y = s'' y) 
								)
								==>
									(s' "x" = s "y") /\ (s' "y" = s "x")
				*)
				
		THEN
			(REPEAT STRIP_TAC)	
		THEN
			(EvaluateFor [``"t"``,``"x"``,``"y"``])
		THEN
			REP_EVAL_TAC
		)
	end
;

(* \end{lstlisting}
\begin{lstlisting} % (*

	Proof of an algorithm for swapping values among two variables

*) \end{lstlisting} % 


\item{in the case where s x and s y are numeric}

\begin{lstlisting} % *)

load "arithmeticTheory";
open arithmeticTheory;
(*
	need this for LESS_EQ_REFL, LESS_EQ_ADD_SUB, SUB_EQ_0, and ADD_0
	
*)

val NumericSwap = let val
		conversion =	
			PURE_ONCE_REWRITE_RULE [thmAbstractSpecification] 
			(
				SPECL 
					[
						``"x"``, 
						``(assign "y" (\ (s:string->num). ((s "x") - (s "y"))))``, 
						``(\ (s:string->num).((s "x") + (s "y")))``
					] 
					(INST_TYPE 
						[	
							alpha |-> ``:string``, 
							beta |-> ``:num``, 
							gamma |-> ``:string->num``
						] 
						(	REFINEMENT_RULE
							(
								SPECL 
									[
										``f:('a->'b)->'c->bool``,
										``e:('a->'b)->'b``,
										``x:'a``
									] thmForwardSubstitution
							)
						)
					)
			)
	and
		lemma = prove (
				``!(a:num) (b:num). (a + b -(a + b -b)) = (b + a - a)``,
				(PROVE_TAC [LESS_EQ_REFL, LESS_EQ_ADD_SUB, SUB_EQ_0,ADD_0,ADD_SYM])
			)
	in
		prove
		(
			``	
				( 
					\ (s:string->num) (s':string->num). ((s' "x") = (s "y")) /\ ((s' "y") = (s "x"))
				) 
				[=. 
				( 
					sc 
						(
							(	sc
									(assign "x" (\ (s:string->num).((s "x") + (s "y")))) 
									(assign "y" (\ (s:string->num). ((s "x") - (s "y"))))
							)
						)
						(
								assign "x" (\ (s:string->num).((s "x") - (s "y")))
						)
				)
			``
			,
			(SUBST_TAC [conversion])
				(*	[
					]	|-
							(\(s :string -> num) (s' :string -> num). (s' "x" = s "y") /\ (s' "y" = s "x")) 
							[=.
								 sc
								   (subs (assign "y" (\(s :string -> num). s "x" - s "y")) "x"
									  (\(s :string -> num). s "x" + s "y"))
								   (assign "x" (\(s :string -> num). s "x" - s "y"))
				*)
		THEN
			(REP_EVAL_TAC)
				(*	[
					]	|-
							!(s :string -> num) (s' :string -> num).
								  (?(s'' :string -> num).
								     (!(y :string).
									if "y" = y then s'' y = s "x" + s "y" - s "y"
									else s'' y = if "x" = y then s "x" + s "y" else s y) /\
								     !(y :string).
								       if "x" = y then s' y = s'' "x" - s'' "y" else s' y = s'' y) ==>
								  (s' "x" = s "y") /\ (s' "y" = s "x")
				*)
		THEN
			(REPEAT STRIP_TAC)	
		THEN
			(EvaluateFor [``"x"``,``"y"``])
				(*	[
						!(y :string).
							if "y" = y then  (s'' :string -> num) y = (s :string -> num) "x" + s "y" - s "y"
							else s'' y = if "x" = y then s "x" + s "y" else s y
										/\
						!(y :string).
							  if "x" = y then (s' :string -> num) y = (s'' :string -> num) "x" - s'' "y"
							  else s' y = s'' y
										/\
						(s'' :string -> num) "y" = (s :string -> num) "x" + s "y" - s "y"
										/\
						(s' :string -> num) "y" = (s'' :string -> num) "y"
										/\
						(s'' :string -> num) "x" = (s :string -> num) "x" + s "y"
										/\
						(s' :string -> num) "x" = (s'' :string -> num) "x" - s'' "y"
					]	|-
							 (s :string -> num) "x" + s "y" - (s "x" + s "y" - s "y") = s "y"
				*)
				(*	[	
						!(y :string).
							if "y" = y then  (s'' :string -> num) y = (s :string -> num) "x" + s "y" - s "y"
							else s'' y = if "x" = y then s "x" + s "y" else s y
										/\
						!(y :string).
							if "x" = y then (s' :string -> num) y = (s'' :string -> num) "x" - s'' "y"
							else s' y = s'' y
										/\
						(s'' :string -> num) "y" = (s :string -> num) "x" + s "y" - s "y"
										/\
						(s' :string -> num) "y" = (s'' :string -> num) "y"
										/\
						(s'' :string -> num) "x" = (s :string -> num) "x" + s "y"
										/\
						(s' :string -> num) "x" = (s'' :string -> num) "x" - s'' "y"						
					]	|-
							(s' :string -> num) "x" = (s :string -> num) "y"
				*)
		THEN
			(PROVE_TAC [LESS_EQ_REFL, LESS_EQ_ADD_SUB, SUB_EQ_0,ADD_0,lemma])
		)
	end
;

(* \end{lstlisting}
\begin{lstlisting} % (*

	BORROWING FROM ARITHMETIC THEORY TO SOLVE THE SPECIFIC CASE FOR NUMERIC SWAPPING
	
*) \end{lstlisting} % 

\end{enumerate}


This concludes the demonstration.

\begin{comment}===LITERATE PROGRAM FILE TRAILER =======================================================\end{comment}
 \begin{lstlisting} 
(* 
   Last updated October 12, 2010
*) 
\end{lstlisting}  %
% *)