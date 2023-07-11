--------------------------- MODULE RobotGridDP ---------------------------
(***************************************************************************)
(* Imagine a robot sitting on the upper left corner of a grid with r rows  *)
(* and c columns. The robot can only move in two directions, right and     *)
(* down, but certain cells are "off limits" such that the robot cannot     *)
(* step on them. Design an algorithm to find a path for the robot from the *)
(* top left to the bottom right.                                           *)
(***************************************************************************)

EXTENDS Naturals, Sequences, SequencesExt

CONSTANTS R, C, BlockSet

(***************************************************************************)
(* The set of valid coordinates as the set of sequences of length 2 whose  *)
(* elements represent x and y coordinates within the grid. The top left    *)
(* and bottom right position should be excluded.                           *)
(***************************************************************************)
ValidCoordinates ==
    {<<x,y>> : x \in 1..R, y \in 1..C} \ {<<1,1>>, <<R,C>>}

ASSUME /\ R \in Nat \ {0}
       /\ C \in Nat \ {0}
       /\ \A x \in BlockSet : x \in ValidCoordinates

(***************************************************************************)
(* Assert whether a position can be moved to by checking its position      *)
(* within the grid limits and whether it is part of the "off limit" cells  *)
(***************************************************************************)
CanMoveTo(x, y) == 
    /\ x >= 1 /\ x <= R
    /\ y >= 1 /\ y <= C
    /\ <<x, y>> \notin BlockSet

(*

--fair algorithm RobotGrid {
    variables
        m = [x \in 1..R |-> [y \in 1..C |-> <<>>]], \* memoisation sequence
        outcome = <<>>; \* helper variable representing outcome
        
    procedure findPath() {
        call getPath(1, 1, 2, 1);
        call getPath(1, 1, 1, 2);
        return;
    }
        
    procedure getPath(fromX = 1, fromY = 1, toX = R, toY = C) {
        if (~CanMoveTo(toX, toY) \/ m[toX][toY] # <<>>) {
            return;
        };
        \* Append new position to path in memoisation sequence.
        m[toX][toY] := m[fromX][fromY] \o << <<fromX, fromY>> >>;
        call getPath(toX, toY, toX + 1, toY);
        call getPath(toX, toY, toX, toY + 1);
        return;
    }
    
    {
        call findPath();
        
        if (m[R][C] = <<>>) {
            outcome := <<"failure">>;
        } else {
            outcome := <<"success", m[R][C]>>;
        };
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "72162796" /\ chksum(tla) = "e2eb1152")
VARIABLES m, outcome, pc, stack, fromX, fromY, toX, toY

vars == << m, outcome, pc, stack, fromX, fromY, toX, toY >>

Init == (* Global variables *)
        /\ m = [x \in 1..R |-> [y \in 1..C |-> <<>>]]
        /\ outcome = <<>>
        (* Procedure getPath *)
        /\ fromX = 1
        /\ fromY = 1
        /\ toX = R
        /\ toY = C
        /\ stack = << >>
        /\ pc = "Lbl_6"

Lbl_1 == /\ pc = "Lbl_1"
         /\ /\ fromX' = 1
            /\ fromY' = 1
            /\ stack' = << [ procedure |->  "getPath",
                             pc        |->  "Lbl_2",
                             fromX     |->  fromX,
                             fromY     |->  fromY,
                             toX       |->  toX,
                             toY       |->  toY ] >>
                         \o stack
            /\ toX' = 2
            /\ toY' = 1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << m, outcome >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ /\ fromX' = 1
            /\ fromY' = 1
            /\ stack' = << [ procedure |->  "getPath",
                             pc        |->  Head(stack).pc,
                             fromX     |->  fromX,
                             fromY     |->  fromY,
                             toX       |->  toX,
                             toY       |->  toY ] >>
                         \o Tail(stack)
            /\ toX' = 1
            /\ toY' = 2
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << m, outcome >>

findPath == Lbl_1 \/ Lbl_2

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF ~CanMoveTo(toX, toY) \/ m[toX][toY] # <<>>
               THEN /\ pc' = Head(stack).pc
                    /\ fromX' = Head(stack).fromX
                    /\ fromY' = Head(stack).fromY
                    /\ toX' = Head(stack).toX
                    /\ toY' = Head(stack).toY
                    /\ stack' = Tail(stack)
               ELSE /\ pc' = "Lbl_4"
                    /\ UNCHANGED << stack, fromX, fromY, toX, toY >>
         /\ UNCHANGED << m, outcome >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ m' = [m EXCEPT ![toX][toY] = m[fromX][fromY] \o << <<fromX, fromY>> >>]
         /\ /\ fromX' = toX
            /\ fromY' = toY
            /\ stack' = << [ procedure |->  "getPath",
                             pc        |->  "Lbl_5",
                             fromX     |->  fromX,
                             fromY     |->  fromY,
                             toX       |->  toX,
                             toY       |->  toY ] >>
                         \o stack
            /\ toX' = toX + 1
            /\ toY' = toY
         /\ pc' = "Lbl_3"
         /\ UNCHANGED outcome

Lbl_5 == /\ pc = "Lbl_5"
         /\ /\ fromX' = toX
            /\ fromY' = toY
            /\ toX' = toX
            /\ toY' = toY + 1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << m, outcome, stack >>

getPath == Lbl_3 \/ Lbl_4 \/ Lbl_5

Lbl_6 == /\ pc = "Lbl_6"
         /\ stack' = << [ procedure |->  "findPath",
                          pc        |->  "Lbl_7" ] >>
                      \o stack
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << m, outcome, fromX, fromY, toX, toY >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ IF m[R][C] = <<>>
               THEN /\ outcome' = <<"failure">>
               ELSE /\ outcome' = <<"success", m[R][C]>>
         /\ pc' = "Done"
         /\ UNCHANGED << m, stack, fromX, fromY, toX, toY >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == findPath \/ getPath \/ Lbl_6 \/ Lbl_7
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

(***************************************************************************)
(* For all elements of the memoisation sequence it should hold that their  *)
(* value (i.e. the path to this position) should not contain "off limit"   *)
(* cells.                                                                  *)
(***************************************************************************)
PosInv ==
    \A x \in 1..R, y \in 1..C : ToSet(m[x][y]) \intersect BlockSet = {}

(***************************************************************************)
(* The robot can reach the goal position if eventually a path to the       *)
(* bottom right cell has been found.                                       *)
(***************************************************************************)
CanReachGoal == <>(m[R][C] # <<>>)

=============================================================================
\* Modification History
\* Last modified Wed Jul 05 16:59:32 CEST 2023 by travn
\* Created Fri Jun 23 20:11:05 CEST 2023 by travn
