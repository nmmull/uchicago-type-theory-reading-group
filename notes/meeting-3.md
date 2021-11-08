# Meeting 3 (10/15)

* Thanks again Justin for leading the meeting.

* *1.7 Coproduct Types*
  * Fairly standard presentation, Justin emphasized figuring out the recursion and induction principles based on the general questions: how do you "do something" with a value of type $A + B$?
  
  * A uniqueness principle is not given, but I have since realized that it is propositionally derivable. The term
    $$
    \lambda c^{A + B}. \text{ind}_{A + B}(\lambda d^{A + B}. d =_{A + B} \text{rec}_{A + B}(A + B, \lambda x^A. \mathsf{inl}(x), \lambda x^B. \mathsf{inr}(x), d), \lambda x^A.\text{refl}_{\mathsf{inl}(x)}, \lambda x^B.\text{refl}_{\mathsf{inr}(x)}, c)
    $$
    is of type
    $$
    \prod_{c: A+B} c =_{A + B} \text{rec}_{A + B}(A + B, \lambda x^A. \mathsf{inl}(x), \lambda x^B. \mathsf{inr}(x), c)
    $$
  
* *1.8 The Type of Booleans*

  * Interesting because we can define coproducts (and products) in terms of Booleans. We can think of these as finitely (binary) indexed sums (and products) of types.
  
  * It's not clear what the authors mean by: "we don't get the same judgmental equalities" for the encoding of binary products using Booleans. We landed on: we believe you'd get all the same judgmental equalities if you assume functional extensionality.
    
  
* *1.9 The Natural Numbers*

  * Another standard presentation, the induction principle matches the usual notion of induction on natural numbers.
  * Question: What class of functions is encoded by terms of type $\mathbb N^k \to \mathbb N$? The text notes that it's more than the primitive recursive functions, and naturally it should be at most the total computable functions. I'm honestly not sure, but this feels related to recursive constructive mathematics (https://plato.stanford.edu/entries/mathematics-constructive/#RecuConsMath). One potential limitation of this class is it doesn't seem possible to do unbounded search if it is classically guaranteed to be total. In particular, given a term $M : \mathbb N \to \mathbb N$, which encodes the total computable function $f$, and a term of type $\neg \neg \Sigma_{x : \mathbb N} (M x =_{\mathbb N} 0)$, is it possible to define a term $N : \mathbb N \to \mathbb N$ which encodes $\mu x. fx = 0$ (the smallest input on which $f$ outputs $0$)? Again, honestly not sure. This is related to Markov's principle in RCM.
  
* *1.10 Pattern Matching*

  * A fairly informal section, basically along the lines of "we will make pattern matching more formal eventually but it's so convenient we'll start using it now since you probably know roughly what we mean."