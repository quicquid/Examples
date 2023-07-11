-------------------------- MODULE UnitConversion2 --------------------------
(***************************************************************************)
(* Write a program that can answer unit conversion questions. Like 'How    *)
(* many meters are in an inch?', given a big list of conversion facts      *)
(* about units.                                                            *)
(*                                                                         *)
(* Example facts:                                                          *)
(* m = 3.28 ft                                                             *)
(* ft = 12 in                                                              *)
(* hr = 60 min                                                             *)
(* min = 60 sec                                                            *)
(*                                                                         *)
(* Example queries:                                                        *)
(* 2 m = ? in -> 78.72                                                     *)
(* 13 in = ? m -> 0.330                                                    *)
(* 13 in = ? hr -> not convertible                                         *)
(*                                                                         *)
(* Properties:                                                             *)
(* Input conversion should be checked on consistent transitive closure     *)
(* Facts will be given as (string, float, string) and query as             *)
(* (float, string, string).                                                *)
(***************************************************************************)

EXTENDS Naturals, Integers, Sequences, TLC, Rationals

(***************************************************************************)
(* General considerations:                                                 *)
(*                                                                         *)
(* In this example, we refrain from accepting floats like in the above     *)
(* example, as TLC does not support floating point numbers. Since the      *)
(* complexity of this task is not to map floating point numbers, this      *)
(* compromise is made. Therefore, the Rationals module was created to      *)
(* introduce the set on rational numbers and the most common operations    *)
(* on rational numbers.                                                    *)
(*                                                                         *)
(* Furthermore, a conversion fact from one unit to another cannot be used  *)
(* in a symmetric way as the set of integers is not closed under           *)
(* division required for the inversion of the conversion factor.           *)
(***************************************************************************)

CONSTANTS Input, Queries

(***************************************************************************)
(* The unit domain of the given set of input tuples is defined as the      *)
(* set of units of the conversions.                                        *)
(***************************************************************************)
UnitDomain(S) == {x[1] : x \in S} \cup {x[3] : x \in S}

(***************************************************************************)
(* Input facts should be given as tuples (sequences) of length 3 in the    *)
(* form (string, int, string).                                             *)
(***************************************************************************)
ValidInput(S) == \A x \in S : /\ Len(x) = 3
                              /\ x[1] \in UnitDomain(S)
                              /\ x[2] \in Rat
                              /\ x[3] \in UnitDomain(S)
                              /\ x[1] # x[3]
                              
                              
(***************************************************************************)
(* Queries should be given as tuples (sequences) of length 3 in the form   *)
(* (int, string, string).                                                  *)
(***************************************************************************)
ValidQueries(S) == \A x \in S : /\ Len(x) = 3
                                /\ x[1] \in Rat
                                /\ x[2] \in UnitDomain(Input)
                                /\ x[3] \in UnitDomain(Input)
                                /\ x[2] # x[3]

ASSUME /\ ValidInput(Input) 
       /\ ValidQueries(Queries)

(***************************************************************************)
(* Convert input facts to records for better understanding of fields.      *)
(***************************************************************************)
Facts == {[from |-> x[1], amt |-> x[2], to |-> x[3]] : x \in Input}
RevFacts == {[from |-> x[3], amt |-> Div(One, x[2]), to |-> x[1]] : x \in Input}
Qs == {[amt |-> x[1], from |-> x[2], to |-> x[3]] : x \in Queries}


RECURSIVE TransClosure(_)
(***************************************************************************)
(* The transitive closure of the conversion relation including the         *)
(* total conversion factor.                                                *)
(***************************************************************************)
TransClosure(S) ==
   LET OneStep(G) == {x \in G \X G : x[1][3] = x[2][1]} IN
   LET T == S \cup {<<x[1][1], Mult(x[1][2], x[2][2]), x[2][3]>> : x \in OneStep(S)} IN
   IF S = T THEN S ELSE TransClosure(T)
   
Conversions(S) == {<<conv.from, conv.amt, conv.to>> : conv \in S}
      
Consistent(S) == \A f1, f2 \in S : (f1[1] = f2[1] /\ f1[3] = f2[3]) => (f1[2] = f2[2])

(***************************************************************************)
(* Define a conversion from one unit to another to be convertible iff      *)
(* there exists a path from the start to the end unit.                     *)
(***************************************************************************)
RECURSIVE Convertible(_, _)
Convertible(from, to) == 
    IF \E f \in Facts : f.from = from /\ f.to = to
        THEN TRUE
    ELSE IF \E f \in Facts : f.from = from
            THEN Convertible((CHOOSE f \in Facts : f.from = from).to, to)
         ELSE FALSE
                      
RECURSIVE Convert(_, _, _, _)
Convert(S, amt, from, to) == 
    IF \E x \in S : x.from = from /\ x.to = to
        THEN Mult(amt, (CHOOSE x \in S : (x.from = from /\ x.to = to)).amt)
    ELSE IF \E x \in S : x.from = from
            THEN Convert(S, Mult(amt, (CHOOSE x \in S : x.from = from).amt), 
                                    (CHOOSE x \in S : x.from = from).to, to)  
         ELSE <<0, 0>>
                                        
(*

--fair algorithm UnitConversion {
    variables
      G = [nodes |-> {}, edges |-> {}], \* conversion graph
      query \in Qs,
      paths = {};
      out = <<0, 0>>; \* conversion result
    
    \* construct graph from input facts
    procedure buildGraph(input = {})
      variables f = 0;
      {
        while (input # {}) {
          f := CHOOSE x \in input : TRUE;
          call addFact(f);
          input := input \ {f};
        };
        return;
      }
      
    procedure addFact(fact = [from |-> "", amt |-> 0, to |-> ""])
      variables H = G, i = {}, j = {}, m = "", n = "";
      {
        H := [H EXCEPT !.nodes = H.nodes \cup {fact.from, fact.to},
                       !.edges = H.edges \cup {fact}];
        i := H.nodes;
        while (i # {}) {
          m := CHOOSE x \in i : TRUE;
          j := i \ {m};
          while (j # {}) {
            n := CHOOSE x \in j : TRUE;
            call findPaths(H, m, n);
            j := j \ {n};
          };
          i := i \ {m};
        };
        
        \* check whether insertion of new fact leads to inconsistencies
        if (~\E p1, p2 \in paths : /\ Head(p1.p) = Head(p2.p)
                                   /\ p1.p[Len(p1.p)] = p2.p[Len(p2.p)]
                                   /\ ~Equal(p1.len, p2.len)) {
          H := [H EXCEPT !.edges = H.edges \cup {[from |-> fact.to, 
                                                  amt |-> Div(One, fact.amt),
                                                  to |-> fact.from]}];
          G := H;
        };
        paths := {};
        return;
      }
    
    \* find all possible paths between to nodes in conversion graph
    procedure findPaths(g = [nodes |-> {}, edges |-> {}], from = "", to = "")
      variables queue = <<[len |-> One, p |-> <<from>>]>>, visited = {}, 
                n = [len |-> Zero, p |-> <<>>], nes = {};
      {
        while (Len(queue) # 0) {
          n := queue[1];
          queue := Tail(queue);
          if (Head(n.p) = to) {
            paths := paths \cup {n};
          };
          nes := {e \in g.edges : e.from = Head(n.p)};
          while (nes # {}) {
            with (ne \in nes) {
              if (ne \notin visited) {
                visited := visited \cup {ne};
                queue := queue \o <<[len |-> Mult(n.len, ne.amt), p |-> <<ne.to>> \o n.p]>>
              };
              nes := nes \ {ne};
            };
          };
        };
        return;
      } 
    
    \* evaluate given query based on constructed conversion graph
    procedure convert(q = [from |-> "", amt |-> Zero, to |-> ""])
      variables queue = <<[node |-> q.from, val |-> q.amt]>>, visited = {q.from},
                n = [node |-> "", val |-> Zero], nes = {};
      {
        while (Len(queue) # 0) {
          n := queue[1];
          queue := Tail(queue);
          if (n.node = q.to) {
            out := n.val;
            return;
          };
          nes := {e \in G.edges : e.from = n.node};
          while (nes # {}) {
            with (ne \in nes) {
              if (ne.to \notin visited) {
                visited := visited \cup {ne.to};
                queue := queue \o <<[node |-> ne.to, val |-> Mult(n.val, ne.amt)]>>;
              };
              nes := nes \ {ne};
            };
          };          
        };
        return;
      }
    
    {
      call buildGraph(Facts);
      call convert(query);
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "c2a6cc7e" /\ chksum(tla) = "4266080d")
\* Procedure variable n of procedure addFact at line 136 col 48 changed to n_
\* Procedure variable queue of procedure findPaths at line 167 col 17 changed to queue_
\* Procedure variable visited of procedure findPaths at line 167 col 60 changed to visited_
\* Procedure variable n of procedure findPaths at line 168 col 17 changed to n_f
\* Procedure variable nes of procedure findPaths at line 168 col 49 changed to nes_
VARIABLES G, query, paths, out, pc, stack, input, f, fact, H, i, j, m, n_, g, 
          from, to, queue_, visited_, n_f, nes_, q, queue, visited, n, nes

vars == << G, query, paths, out, pc, stack, input, f, fact, H, i, j, m, n_, g, 
           from, to, queue_, visited_, n_f, nes_, q, queue, visited, n, nes
        >>

Init == (* Global variables *)
        /\ G = [nodes |-> {}, edges |-> {}]
        /\ query \in Qs
        /\ paths = {}
        /\ out = <<0, 0>>
        (* Procedure buildGraph *)
        /\ input = {}
        /\ f = 0
        (* Procedure addFact *)
        /\ fact = [from |-> "", amt |-> 0, to |-> ""]
        /\ H = G
        /\ i = {}
        /\ j = {}
        /\ m = ""
        /\ n_ = ""
        (* Procedure findPaths *)
        /\ g = [nodes |-> {}, edges |-> {}]
        /\ from = ""
        /\ to = ""
        /\ queue_ = <<[len |-> One, p |-> <<from>>]>>
        /\ visited_ = {}
        /\ n_f = [len |-> Zero, p |-> <<>>]
        /\ nes_ = {}
        (* Procedure convert *)
        /\ q = [from |-> "", amt |-> Zero, to |-> ""]
        /\ queue = <<[node |-> q.from, val |-> q.amt]>>
        /\ visited = {q.from}
        /\ n = [node |-> "", val |-> Zero]
        /\ nes = {}
        /\ stack = << >>
        /\ pc = "Lbl_14"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF input # {}
               THEN /\ f' = (CHOOSE x \in input : TRUE)
                    /\ /\ fact' = f'
                       /\ stack' = << [ procedure |->  "addFact",
                                        pc        |->  "Lbl_2",
                                        H         |->  H,
                                        i         |->  i,
                                        j         |->  j,
                                        m         |->  m,
                                        n_        |->  n_,
                                        fact      |->  fact ] >>
                                    \o stack
                    /\ H' = G
                    /\ i' = {}
                    /\ j' = {}
                    /\ m' = ""
                    /\ n_' = ""
                    /\ pc' = "Lbl_3"
                    /\ input' = input
               ELSE /\ pc' = Head(stack).pc
                    /\ f' = Head(stack).f
                    /\ input' = Head(stack).input
                    /\ stack' = Tail(stack)
                    /\ UNCHANGED << fact, H, i, j, m, n_ >>
         /\ UNCHANGED << G, query, paths, out, g, from, to, queue_, visited_, 
                         n_f, nes_, q, queue, visited, n, nes >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ input' = input \ {f}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << G, query, paths, out, stack, f, fact, H, i, j, m, n_, 
                         g, from, to, queue_, visited_, n_f, nes_, q, queue, 
                         visited, n, nes >>

buildGraph == Lbl_1 \/ Lbl_2

Lbl_3 == /\ pc = "Lbl_3"
         /\ H' = [H EXCEPT !.nodes = H.nodes \cup {fact.from, fact.to},
                           !.edges = H.edges \cup {fact}]
         /\ i' = H'.nodes
         /\ pc' = "Lbl_4"
         /\ UNCHANGED << G, query, paths, out, stack, input, f, fact, j, m, n_, 
                         g, from, to, queue_, visited_, n_f, nes_, q, queue, 
                         visited, n, nes >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ IF i # {}
               THEN /\ m' = (CHOOSE x \in i : TRUE)
                    /\ j' = i \ {m'}
                    /\ pc' = "Lbl_5"
                    /\ UNCHANGED << G, paths, H >>
               ELSE /\ IF ~\E p1, p2 \in paths : /\ Head(p1.p) = Head(p2.p)
                                                 /\ p1.p[Len(p1.p)] = p2.p[Len(p2.p)]
                                                 /\ ~Equal(p1.len, p2.len)
                          THEN /\ H' = [H EXCEPT !.edges = H.edges \cup {[from |-> fact.to,
                                                                          amt |-> Div(One, fact.amt),
                                                                          to |-> fact.from]}]
                               /\ G' = H'
                          ELSE /\ TRUE
                               /\ UNCHANGED << G, H >>
                    /\ paths' = {}
                    /\ pc' = "Lbl_7"
                    /\ UNCHANGED << j, m >>
         /\ UNCHANGED << query, out, stack, input, f, fact, i, n_, g, from, to, 
                         queue_, visited_, n_f, nes_, q, queue, visited, n, 
                         nes >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ IF j # {}
               THEN /\ n_' = (CHOOSE x \in j : TRUE)
                    /\ /\ from' = m
                       /\ g' = H
                       /\ stack' = << [ procedure |->  "findPaths",
                                        pc        |->  "Lbl_6",
                                        queue_    |->  queue_,
                                        visited_  |->  visited_,
                                        n_f       |->  n_f,
                                        nes_      |->  nes_,
                                        g         |->  g,
                                        from      |->  from,
                                        to        |->  to ] >>
                                    \o stack
                       /\ to' = n_'
                    /\ queue_' = <<[len |-> One, p |-> <<from'>>]>>
                    /\ visited_' = {}
                    /\ n_f' = [len |-> Zero, p |-> <<>>]
                    /\ nes_' = {}
                    /\ pc' = "Lbl_8"
                    /\ i' = i
               ELSE /\ i' = i \ {m}
                    /\ pc' = "Lbl_4"
                    /\ UNCHANGED << stack, n_, g, from, to, queue_, visited_, 
                                    n_f, nes_ >>
         /\ UNCHANGED << G, query, paths, out, input, f, fact, H, j, m, q, 
                         queue, visited, n, nes >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ j' = j \ {n_}
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << G, query, paths, out, stack, input, f, fact, H, i, m, 
                         n_, g, from, to, queue_, visited_, n_f, nes_, q, 
                         queue, visited, n, nes >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ pc' = Head(stack).pc
         /\ H' = Head(stack).H
         /\ i' = Head(stack).i
         /\ j' = Head(stack).j
         /\ m' = Head(stack).m
         /\ n_' = Head(stack).n_
         /\ fact' = Head(stack).fact
         /\ stack' = Tail(stack)
         /\ UNCHANGED << G, query, paths, out, input, f, g, from, to, queue_, 
                         visited_, n_f, nes_, q, queue, visited, n, nes >>

addFact == Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7

Lbl_8 == /\ pc = "Lbl_8"
         /\ IF Len(queue_) # 0
               THEN /\ n_f' = queue_[1]
                    /\ queue_' = Tail(queue_)
                    /\ IF Head(n_f'.p) = to
                          THEN /\ paths' = (paths \cup {n_f'})
                          ELSE /\ TRUE
                               /\ paths' = paths
                    /\ nes_' = {e \in g.edges : e.from = Head(n_f'.p)}
                    /\ pc' = "Lbl_9"
                    /\ UNCHANGED << stack, g, from, to, visited_ >>
               ELSE /\ pc' = Head(stack).pc
                    /\ queue_' = Head(stack).queue_
                    /\ visited_' = Head(stack).visited_
                    /\ n_f' = Head(stack).n_f
                    /\ nes_' = Head(stack).nes_
                    /\ g' = Head(stack).g
                    /\ from' = Head(stack).from
                    /\ to' = Head(stack).to
                    /\ stack' = Tail(stack)
                    /\ paths' = paths
         /\ UNCHANGED << G, query, out, input, f, fact, H, i, j, m, n_, q, 
                         queue, visited, n, nes >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ IF nes_ # {}
               THEN /\ \E ne \in nes_:
                         /\ IF ne \notin visited_
                               THEN /\ visited_' = (visited_ \cup {ne})
                                    /\ queue_' = queue_ \o <<[len |-> Mult(n_f.len, ne.amt), p |-> <<ne.to>> \o n_f.p]>>
                               ELSE /\ TRUE
                                    /\ UNCHANGED << queue_, visited_ >>
                         /\ nes_' = nes_ \ {ne}
                    /\ pc' = "Lbl_9"
               ELSE /\ pc' = "Lbl_8"
                    /\ UNCHANGED << queue_, visited_, nes_ >>
         /\ UNCHANGED << G, query, paths, out, stack, input, f, fact, H, i, j, 
                         m, n_, g, from, to, n_f, q, queue, visited, n, nes >>

findPaths == Lbl_8 \/ Lbl_9

Lbl_10 == /\ pc = "Lbl_10"
          /\ IF Len(queue) # 0
                THEN /\ n' = queue[1]
                     /\ queue' = Tail(queue)
                     /\ IF n'.node = q.to
                           THEN /\ out' = n'.val
                                /\ pc' = "Lbl_11"
                           ELSE /\ pc' = "Lbl_12"
                                /\ out' = out
                     /\ UNCHANGED << stack, q, visited, nes >>
                ELSE /\ pc' = Head(stack).pc
                     /\ queue' = Head(stack).queue
                     /\ visited' = Head(stack).visited
                     /\ n' = Head(stack).n
                     /\ nes' = Head(stack).nes
                     /\ q' = Head(stack).q
                     /\ stack' = Tail(stack)
                     /\ out' = out
          /\ UNCHANGED << G, query, paths, input, f, fact, H, i, j, m, n_, g, 
                          from, to, queue_, visited_, n_f, nes_ >>

Lbl_12 == /\ pc = "Lbl_12"
          /\ nes' = {e \in G.edges : e.from = n.node}
          /\ pc' = "Lbl_13"
          /\ UNCHANGED << G, query, paths, out, stack, input, f, fact, H, i, j, 
                          m, n_, g, from, to, queue_, visited_, n_f, nes_, q, 
                          queue, visited, n >>

Lbl_13 == /\ pc = "Lbl_13"
          /\ IF nes # {}
                THEN /\ \E ne \in nes:
                          /\ IF ne.to \notin visited
                                THEN /\ visited' = (visited \cup {ne.to})
                                     /\ queue' = queue \o <<[node |-> ne.to, val |-> Mult(n.val, ne.amt)]>>
                                ELSE /\ TRUE
                                     /\ UNCHANGED << queue, visited >>
                          /\ nes' = nes \ {ne}
                     /\ pc' = "Lbl_13"
                ELSE /\ pc' = "Lbl_10"
                     /\ UNCHANGED << queue, visited, nes >>
          /\ UNCHANGED << G, query, paths, out, stack, input, f, fact, H, i, j, 
                          m, n_, g, from, to, queue_, visited_, n_f, nes_, q, 
                          n >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ pc' = Head(stack).pc
          /\ queue' = Head(stack).queue
          /\ visited' = Head(stack).visited
          /\ n' = Head(stack).n
          /\ nes' = Head(stack).nes
          /\ q' = Head(stack).q
          /\ stack' = Tail(stack)
          /\ UNCHANGED << G, query, paths, out, input, f, fact, H, i, j, m, n_, 
                          g, from, to, queue_, visited_, n_f, nes_ >>

convert == Lbl_10 \/ Lbl_12 \/ Lbl_13 \/ Lbl_11

Lbl_14 == /\ pc = "Lbl_14"
          /\ /\ input' = Facts
             /\ stack' = << [ procedure |->  "buildGraph",
                              pc        |->  "Lbl_15",
                              f         |->  f,
                              input     |->  input ] >>
                          \o stack
          /\ f' = 0
          /\ pc' = "Lbl_1"
          /\ UNCHANGED << G, query, paths, out, fact, H, i, j, m, n_, g, from, 
                          to, queue_, visited_, n_f, nes_, q, queue, visited, 
                          n, nes >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ /\ q' = query
             /\ stack' = << [ procedure |->  "convert",
                              pc        |->  "Done",
                              queue     |->  queue,
                              visited   |->  visited,
                              n         |->  n,
                              nes       |->  nes,
                              q         |->  q ] >>
                          \o stack
          /\ queue' = <<[node |-> q'.from, val |-> q'.amt]>>
          /\ visited' = {q'.from}
          /\ n' = [node |-> "", val |-> Zero]
          /\ nes' = {}
          /\ pc' = "Lbl_10"
          /\ UNCHANGED << G, query, paths, out, input, f, fact, H, i, j, m, n_, 
                          g, from, to, queue_, visited_, n_f, nes_ >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == buildGraph \/ addFact \/ findPaths \/ convert \/ Lbl_14 \/ Lbl_15
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

TypeOK == /\ \A x \in G.nodes : x \in UnitDomain(Input)
          /\ \A x \in G.edges : \E y \in Facts \cup RevFacts : /\ x.from = y.from
                                                               /\ Equal(x.amt, y.amt)
                                                               /\ x.to = y.to
          /\ out \in Rat \cup {<<0, 0>>}

(***************************************************************************)
(* The transitive closure of the conversion relation should always be      *)
(* consitent i.e. there must be a unique conversion between any pair of    *)
(* nodes (if such conversion exists).                                      *)
(***************************************************************************)
TransInv == Consistent(TransClosure(Conversions(G.edges)))

(***************************************************************************)
(* Eventually, all units present in the input facts should appear as nodes *)
(* in the unit conversion graph.                                           *)
(***************************************************************************)
AllUnits == <>(G.nodes = UnitDomain(Input))

(***************************************************************************)
(* Correctness is given when the conversion result evaluated using the     *)
(* constructed conversion graph is equal to the conversion rate given by   *)
(* the input facts (if such a conversion exists).                          *)
(***************************************************************************)
Correctness == IF Convertible(query.from, query.to)
                 THEN Equal(out, Convert(G.edges, query.amt, query.from, query.to))
               ELSE Equal(out, <<0, 0>>)

=============================================================================
\* Modification History
\* Last modified Wed Jul 05 17:18:26 CEST 2023 by travn
\* Created Tue Mar 14 16:54:07 CET 2023 by travn
