# Meeting 2 (10/8)

* *Presenter sign-ups:* There are still plenty of spots open for leading meetings throughout the quarter. Again, this is I think a low stakes commitment, make what you want of it, it's really just an opportunity to direct the discussion.

* *Section 1.1: Type Theory vs. Set Theory*

  * The beginning exposition essentially covers the Curry-Howard isomorphism without saying so.
  * The most important part of this section is the discussion on *propositional* vs. *judgmental equality*. These are also called *internal* and *external equality*, respectively. A proof of propositional equality is a term of an equality type whereas a proof of judgmental equality is a meta-theoretic argument that two terms are the same up to $\beta\eta$-equivalence and definitional expansion.
  * One point of notational abuse: the authors will sometimes use "let $x \equiv M$..." for "substitute $M$ for $x$ in the given context."
  *  What the authors call a *judgment* is called a *statement* in other texts. The designation "judgment" is then reserved for a context together with a statement (i.e., $\Gamma \vdash M : A$). My sense is that, because of their informal approach to type theory, the authors always assume an ambient context.

* *Section 1.2, 1.5, Function Types and Product Types*

  * We introduce a new type into our theory by giving:

    * a type former, to construct the new type from existing types
    * constructors, to build terms of the new type
    * eliminators, to apply to terms of the new type (to show how to work with terms of the new type)
    * computation rules, to express how terms of the new type can be reduced
    * uniqueness principles, to express that a term of the new type equal to the term gotten by applying eliminators and then constructors to it.

    We covered these for functions and product types.

  * (Skye) There was a question about why we include the uniqueness principles. I had forgotten at the time that the authors mention that uniqueness principles are not always given, but may still be provable propositionally, as in the case for products.

  * Computations rules are called *$\beta$-rules* and the uniqueness principles is called the $\eta$-rules. This is different from standard use, where these terms are restricted to function types. So $\mathsf{proj}_1\langle M, N \rangle \equiv M$ is one of the $\beta$-rules for products.

  * We went over the definition of a category, and looked at a few examples. Two more interesting examples were monoids as categories and preorders as categories. Categories can be viewed as generalizations of these two structures.

  * We gave a general definition of a *classifying category* or a *term model* for a type theory. In the case of simple (non-dependent) type theory (with just function types and finite products), this category has types as objects and, as an arrow from $A$ to $B$, a $\beta\eta$-equivalence class of terms $[M]$, such that $x : A \vdash M: B$. That is, $M$ is a term of type $B$ in the context with a single variable of type $A$. The equivalence class notation is usually dropped. Identity arrows are single variables, since $x : A \vdash x : A$ and composition is done by substitution, $M(x) \circ N = M[N / x]$. This requires proving that if $x : B \vdash M : C$ and $x : A \vdash N : B$, then $x : A \vdash M[N/x] : C$. The other equalities which make this a category require similar substitution lemmas.

  * We gave a definition of products in a category, and looked at the correspondence between categorical structure in the term model and type theoretic structure in the type theory. Product types in simple type theory form products in the classifying category theory. There is a clean correspondence with the above component of type theoretic constructions:

    * The existence of the object $A \times B$ corresponds to a type former
    * The arrow into $A \times B$ corresponds to a constructor
    * The arrows out of $A \times B$ (the projections) correspond to eliminators
    * The commutativity of the diagram corresponds to the $\beta$-rules
    * The uniqueness of the arrow into $A \times B$ corresponds the $\eta$-rule.

    *The moral:* It is often easier to determine what the $\beta$- and $\eta$-rules are by looking at their corresponding category theoretic interpretations.

* We didn't get to sections 1.3, 1.4, or 1.7.

  * Section 1.3 was on universes. The system in the book has a standard cumulative hierarchy of universes to avoid Girard's paradox.
  * Sections 1.4 and 1.7 cover the dependent versions of functions and products, which I assume most people are already familiar with, but I'm happy to answer any questions about them offline.

* There was a short discussion as people were leaving on the term model for dependent type theories. These require the use of *slice categories* to express categorically the type theoretic structure. Again, happy to chat offline about this.



