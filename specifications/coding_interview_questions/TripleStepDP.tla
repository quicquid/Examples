---------------------------- MODULE TripleStepDP ----------------------------
(***************************************************************************)
(* A child is running up a staircase with n steps and can hop either 1     *)
(* step, 2 steps, or 3 steps at a time. Implement a method to count how    *)
(* many possible ways the child can run up the stairs.                     *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

ASSUME N \in Nat

(***************************************************************************)
(* The sum of the elements of a sequence.                                  *)
(***************************************************************************)
RECURSIVE SeqSum(_)
SeqSum(S) == IF S = << >> THEN 0
          ELSE Head(S) + SeqSum(Tail(S))

(***************************************************************************)
(* Define the set of possible ways to be the set of all possible sequences *)
(* of length 0 to N containing the elements in [1,3] whose sum is N.       *)
(***************************************************************************)
PossibleWays == {x \in (UNION {[1..m -> 1..3] : m \in 0..N}) : SeqSum(x) = N}

(*

--fair algorithm TripleStep {
    variables
        m = [x \in 1..(N + 1) |-> 0]; \* memoisation sequence
        
    procedure possibleWays(i = 0) {
        if (i = 0) { \* base case N = 0
            m[1] := 1;
        } else if (i = 1) { \* base case N = 1
            m[2] := 1;
        } else if (i = 2) { \* base case N = 2
            m[3] := 2;
        } else if (m[i + 1] = 0) { \* recursion
            call possibleWays(i - 1);
            call possibleWays(i - 2);
            call possibleWays(i - 3);
            m[i + 1] := m[i] + m[i - 1] + m[i - 2];
        };
        return;
    }
    
    {
        call possibleWays(N);
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "58f8b1b7" /\ chksum(tla) = "6145e863")
VARIABLES m, pc, stack, i

vars == << m, pc, stack, i >>

Init == (* Global variables *)
        /\ m = [x \in 1..(N + 1) |-> 0]
        (* Procedure possibleWays *)
        /\ i = 0
        /\ stack = << >>
        /\ pc = "Lbl_6"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i = 0
               THEN /\ m' = [m EXCEPT ![1] = 1]
                    /\ pc' = "Lbl_5"
                    /\ UNCHANGED << stack, i >>
               ELSE /\ IF i = 1
                          THEN /\ m' = [m EXCEPT ![2] = 1]
                               /\ pc' = "Lbl_5"
                               /\ UNCHANGED << stack, i >>
                          ELSE /\ IF i = 2
                                     THEN /\ m' = [m EXCEPT ![3] = 2]
                                          /\ pc' = "Lbl_5"
                                          /\ UNCHANGED << stack, i >>
                                     ELSE /\ IF m[i + 1] = 0
                                                THEN /\ /\ i' = i - 1
                                                        /\ stack' = << [ procedure |->  "possibleWays",
                                                                         pc        |->  "Lbl_2",
                                                                         i         |->  i ] >>
                                                                     \o stack
                                                     /\ pc' = "Lbl_1"
                                                ELSE /\ pc' = "Lbl_5"
                                                     /\ UNCHANGED << stack, i >>
                                          /\ m' = m

Lbl_2 == /\ pc = "Lbl_2"
         /\ /\ i' = i - 2
            /\ stack' = << [ procedure |->  "possibleWays",
                             pc        |->  "Lbl_3",
                             i         |->  i ] >>
                         \o stack
         /\ pc' = "Lbl_1"
         /\ m' = m

Lbl_3 == /\ pc = "Lbl_3"
         /\ /\ i' = i - 3
            /\ stack' = << [ procedure |->  "possibleWays",
                             pc        |->  "Lbl_4",
                             i         |->  i ] >>
                         \o stack
         /\ pc' = "Lbl_1"
         /\ m' = m

Lbl_4 == /\ pc = "Lbl_4"
         /\ m' = [m EXCEPT ![i + 1] = m[i] + m[i - 1] + m[i - 2]]
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << stack, i >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ pc' = Head(stack).pc
         /\ i' = Head(stack).i
         /\ stack' = Tail(stack)
         /\ m' = m

possibleWays == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5

Lbl_6 == /\ pc = "Lbl_6"
         /\ /\ i' = N
            /\ stack' = << [ procedure |->  "possibleWays",
                             pc        |->  "Done",
                             i         |->  i ] >>
                         \o stack
         /\ pc' = "Lbl_1"
         /\ m' = m

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == possibleWays \/ Lbl_6
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

TypeOK == \A x \in 1..(N + 1) : m[x] \in Nat

(***************************************************************************)
(* For all elements of m with index > 3 the recursion should hold. The     *)
(* prior indices are implicitly defined within the spec.                   *)
(***************************************************************************)
RecInv == \A x \in 4..N : m[x] # 0 => (m[x] = m[x - 1] + m[x - 2] + m[x - 3])

(***************************************************************************)
(* Correctness is given when the value of the memoisation sequence at      *)
(* index N+1 (sequences are one-based) is equal to the cardinality of the  *)
(* set of possible sequences.                                              *)
(***************************************************************************)
Correctness == m[N + 1] = Cardinality(PossibleWays)

=============================================================================
\* Modification History
\* Last modified Wed Jul 05 17:16:59 CEST 2023 by travn
\* Created Fri Jun 02 16:58:35 CEST 2023 by travn
