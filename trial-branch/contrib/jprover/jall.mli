(* JProver provides an efficient refiner for first-order classical
   and first-order intuitionistic logic. It consists of two main parts:
   a proof search procedure and a proof reconstruction procedure.


   Proof Search
   ============

   The proof search process is based on a matrix-based (connection-based)
   proof procedure, i.e.~a non-normalform extension procedure.
   Besides the well-known quantifier substitution (Martelli Montanari),
   a special string unifiation procedure is used in order to
   efficiently compute intuitionistic rule non-permutabilities.


   Proof Reconstruction
   ====================

   The proof reconstruction process converts machine-generated matrix proofs
   into cut-free Gentzen-style sequent proofs. For classcal logic "C",
   Gentzen's sequent calculus "LK" is used as target calculus.
   For intuitionistic logic "J", either Gentzen's single-conclusioned sequent
   calculus "LJ" or Fitting's multiply-conclusioned sequent calculus "LJmc"
   can be used. All sequent claculi are implemented in a set-based formulation
   in order to avoid structural rules.

   The proof reconstruction procedure combines three main procedures, depending
   on the selected logics and sequent calculi. It consists of:

    1) A uniform traversal algorithm for all logics and target sequent calculi.
       This procedure converts classical (intuitionistic) matrix proofs
       directly into cut-free "LK" ("LJmc" or "LJ") sequent proofs.
       However, the direct construction of "LJ" proofs may fail in some cases
       due to proof theoretical reasons.

    2) A complete redundancy deletion algorithm, which integrates additional
       knowledge from the proof search process into the reconstruction process.
       This procedure is called by the traversal algorithms in order to avoid
       search and deadlocks during proof reconstruciton.

    3) A permutation-based proof transformation for converting "LJmc" proofs
       into "LJ" proofs.
       This procedure is called by-need, whenever the direct reconstruction
       of "LJ" proofs from matrix proofs fails.




   Literature:
   ==========

   JProver system description was presented at CADE 2001:
   @InProceedings{inp:Schmitt+01a,
     author          = "Stephan Schmitt and Lori Lorigo and Christoph Kreitz and
                        Alexey Nogin",
     title           = "{{\sf JProver}}: Integrating Connection-based Theorem
                        Proving into Interactive Proof Assistants",
     booktitle       = "International Joint Conference on Automated Reasoning",
     year            = "2001",
     editor          = "R. Gore and A. Leitsch and T. Nipkow",
     volume          = 2083,
     series          = LNAI,
     pages           = "421--426",
     publisher       = SPRINGER,
     language        = English,
     where           = OWN,
   }

   The implementation of JProver is based on the following publications:



   Slides of PRL-seminar talks:
   ---------------------------

   An Efficient Refiner for First-order Intuitionistic Logic

   http://www.cs.cornell.edu/Nuprl/PRLSeminar/PRLSeminar99_00/schmitt/feb28.html


   An Efficient Refiner for First-order Intuitionistic Logic (Part II)

   http://www.cs.cornell.edu/Nuprl/PRLSeminar/PRLSeminar99_00/schmitt/may22.html



   Proof search:
   -------------


[1]
   @InProceedings{inp:OttenKreitz96b,
     author       = "J.~Otten and C.~Kreitz",
     title        = "A uniform proof procedure  for classical and
                     non-classical logics",
     booktitle	  = "Proceedings of the 20$^{th}$ German Annual Conference on
                     Artificial Intelligence",
     year	  = "1996",
     editor	  = "G.~G{\"o}rz and S.~H{\"o}lldobler",
     number	  = "1137",
     series	  = LNAI,
     pages	  = "307--319",
     publisher	  = SPRINGER
    }


[2]
   @Article{ar:KreitzOtten99,
     author	  = "C.~Kreitz and J.~Otten",
     title 	  = "Connection-based theorem proving in classical and
                     non-classical logics",
     journal	  = "Journal for Universal Computer Science,
                     Special Issue on Integration of Deductive Systems",
     year  	  = "1999",
     volume	  = "5",
     number	  = "3",
     pages 	  = "88--112"
    }




   Special string unifiation procedure:
   ------------------------------------


[3]
   @InProceedings{inp:OttenKreitz96a,
     author	  = "J.~Otten and C.~Kreitz",
     titl         = "T-string-unification: unifying prefixes in
                     non-classical proof methods",
     booktitle	  = "Proceedings of the 5$^{th}$ Workshop on Theorem Proving
		     with Analytic Tableaux and Related Methods",
     year         = 1996,
     editor   	  = "U.~Moscato",
     number	  = "1071",
     series   	  = LNAI,
     pages        = "244--260",
     publisher 	  = SPRINGER,
     month   	  = "May      "
    }



   Proof reconstruction: Uniform traversal algorithm
   -------------------------------------------------


[4]
   @InProceedings{inp:SchmittKreitz96a,
     author       = "S.~Schmitt and C.~Kreitz",
     title        = "Converting non-classical matrix proofs into
                     sequent-style systems",
     booktitle    = "Proceedings of the 13$^t{}^h$ Conference on
                     Automated Deduction",
     editor       =  M.~A.~McRobbie and J.~K.~Slaney",
     number       = "1104",
     series       = LNAI,
     pages        = "418--432",
     year         = "1996",
     publisher    = SPRINGER,
     month        = "July/August"
    }


[5]
   @Article{ar:KreitzSchmitt00,
     author	  = "C.~Kreitz and S.~Schmitt",
     title 	  = "A uniform procedure for converting matrix proofs
                     into sequent-style systems",
     journal	  = "Journal of Information and Computation",
     year  	  = "2000",
     note  	  = "(to appear)"
    }


[6]
   @Book{bo:Schmitt00,
     author	  = "S.~Schmitt",
     title 	  = "Proof reconstruction in classical and non-classical logics",
     year  	  = "2000",
     publisher	  = "Infix",
     series       = "Dissertationen zur K{\"u}nstlichen Intelleigenz",
     number       = "(to appear)",
     note         = "(Ph.{D}.~{T}hesis, Technische Universit{\"a}t Darmstadt,
                     FG Intellektik, Germany, 1999)"
    }

   The traversal algorithm is presented in the Chapters 2 and 3 of my thesis.
   The thesis will be made available for the Department through Christoph Kreitz,
   Upson 4159, kreitz@cs.cornell.edu




   Proof reconstruction: Complete redundancy deletion
   --------------------------------------------------


[7]
   @Book{bo:Schmitt00,
     author	  = "S.~Schmitt",
     title 	  = "Proof reconstruction in classical and non-classical logics",
     year  	  = "2000",
     publisher	  = "Infix",
     series       = "Dissertationen zur K{\"u}nstlichen Intelleigenz",
     note         = "(Ph.{D}.~{T}hesis, Technische Universit{\"a}t Darmstadt,
                     FG Intellektik, Germany, 1999)"
     note         = "(to appear)",

    }

   The integration of proof knowledge and complete redundancy deletion is presented
   in Chapter 4 of my thesis.


[8]
   @InProceedings{inp:Schmitt00,
     author	  = "S.~Schmitt",
     title        = "A tableau-like representation framework for efficient
                     proof reconstruction",
     booktitle	  = "Proceedings of the International Conference on Theorem Proving
                     with Analytic Tableaux and Related Methods",
     year	  = "2000",
     series   	  = LNAI,
     publisher 	  = SPRINGER,
     month   	  = "June"
     note         = "(to appear)",
    }




   Proof Reconstruction: Permutation-based poof transformations "LJ" -> "LJmc"
   ---------------------------------------------------------------------------


[9]
   @InProceedings{inp:EglySchmitt98,
     author	  = "U.~Egly and S.~Schmitt",
     title        = "Intuitionistic proof transformations and their
                     application to constructive program synthesis",
     booktitle	  = "Proceedings of the 4$^{th}$ International Conference
                     on Artificial Intelligence and Symbolic Computation",
     year         = "1998",
     editor   	  = "J.~Calmet and J.~Plaza",
     number	  = "1476",
     series   	  = LNAI,
     pages	  = "132--144",
     publisher 	  = SPRINGER,
     month   	  = "September"
    }


[10]
   @Article{ar:EglySchmitt99,
     author	  = "U.~Egly and S.~Schmitt",
     title 	  = "On intuitionistic proof transformations, their
                     complexity, and application to constructive program synthesis",
     journal	  = "Fundamenta Informaticae,
                     Special Issue: Symbolic Computation and Artificial Intelligence",
    year  	  = "1999",
    volume	  = "39",
    number	  = "1--2",
    pages 	  = "59--83"
   }
*)

(*: open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermSubst 

open Jlogic_sig
:*)

open Jterm
open Opname
open Jlogic

val ruletable : rule -> string

module JProver(JLogic: JLogicSig) :
sig
  val test : term -> string -> string -> unit

  (* Procedure call: test conclusion logic calculus

     test is applied to a first-order formula. The output is some
     formatted sequent proof for test / debugging purposes.

     The arguments for test are as follows:

     logic = "C"|"J"
     i.e. first-order classical logic or first-order intuitionistic logic

     calculus = "LK"|"LJ"|"LJmc"
     i.e. "LK" for classical logic "C", and either Gentzen's single conclusioned
     calculus "LJ" or Fittings multiply-conclusioned calculus "LJmc" for
     intuitionistic logic "J".

     term = first-order formula representing the proof goal.
  *)



  val seqtest : term -> string -> string -> unit

  (* seqtest procedure is for debugging purposes only *)


  val gen_prover : int option -> string -> string -> term list -> term list -> JLogic.inference

  (* Procedure call: gen_prover mult_limit logic calculus hypothesis conclusion

     The arguments for gen_prover are as follows:

     mult_limit - maximal multiplicity to try, None for unlimited

     logic = same as in test

     calculus = same as in test

     hypothesis = list of first-order terms forming the antecedent of the input sequent

     conclusion = list of first-order terms forming the succedent of the input sequent
     This list should contain only one element if logic = "J" and calculus = "LJ".
  *)


  val prover : int option -> term list -> term -> JLogic.inference

  (* Procedure call: gen_prover mult_limit "J" "LJ" hyps [concl]

     prover provides the first-order refiner for NuPRL, using
     a single concluisoned succedent [concl] in the sequent.
     The result is a sequent proof in the single-conclusioned calculus "LJ".
  *)
end
